import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecExtendOfNonzeroLocus

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SecRingIso

open ReciprocityTheory.ChartRestriction.G.Geo.Tor LBGerm TopologicalSpace

section General

variable {X X' Y Z : Scheme.{0}}

theorem gs_comp (r : Z ⟶ Y) (φ : Y ⟶ X) (z : Z) (U : X.Opens) (h : φ (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ φ) z U a = (r.stalkMap z).hom (gs φ (r z) U a) := by
  have e := gs_pull (𝟙 Y) φ (r z) U h a
  rw [Category.id_comp] at e
  exact (gs_pull r φ z U h a).symm.trans ((gs_stalkMap r z (φ ⁻¹ᵁ U) h _).trans (congrArg _ e))

theorem gs_comp_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (r : Z ⟶ Spec Γ(X, U)) (z : Z) (f : Γ(X, U)) :
    gs (r ≫ hU.fromSpec) z U f = gs (𝟙 Z) z ⊤ (r.appTop.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom f)) := by
  have hm : hU.fromSpec (r z) ∈ U := hU.range_fromSpec.le ⟨r z, rfl⟩
  have e := congrArg (fun q => q.hom f) (hU.fromSpec_app_of_le U le_rfl)
  refine (gs_pull r hU.fromSpec z U hm f).symm.trans ((congrArg (gs r z _) e).trans ((gs_res r z le_top hm _).trans ?_))
  refine Eq.trans ?_ (gs_pull (𝟙 Z) r z ⊤ trivial _).symm
  rw [Category.id_comp]
  congr 2
  exact congrArg (fun q => q.hom f) (X.presheaf.map_id _)

theorem hom_ext_spec {A : CommRingCat.{0}} {p q : Z ⟶ Spec A}
    (h : ∀ (a : A) (z : Z), gs (𝟙 Z) z ⊤ (p.appTop.hom ((Scheme.ΓSpecIso A).inv.hom a)) =
      gs (𝟙 Z) z ⊤ (q.appTop.hom ((Scheme.ΓSpecIso A).inv.hom a))) : p = q := by
  refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).2 b
  exact fn_ext fun z _ => h a z

theorem hom_ext_affine {U : X.Opens} (hU : IsAffineOpen U) {φ ψ : Z ⟶ X} (hφ : ∀ z, φ z ∈ U) (hψ : ∀ z, ψ z ∈ U)
    (h : ∀ (f : Γ(X, U)) (z : Z), gs φ z U f = gs ψ z U f) : φ = ψ := by
  have l : ∀ χ : Z ⟶ X, (∀ z, χ z ∈ U) → ∃ r : Z ⟶ Spec Γ(X, U), r ≫ hU.fromSpec = χ := fun χ hχ =>
    ⟨IsOpenImmersion.lift hU.fromSpec χ (by
      rw [hU.range_fromSpec]; rintro _ ⟨z, rfl⟩; exact hχ z), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨p, rfl⟩ := l φ hφ
  obtain ⟨q, rfl⟩ := l ψ hψ
  rw [hom_ext_spec (p := p) (q := q) fun a z =>
    (gs_comp_fromSpec hU p z a).symm.trans ((h a z).trans (gs_comp_fromSpec hU q z a))]

theorem exists_hom_of_ringHom {U : X.Opens} (hU : IsAffineOpen U) (W : X'.Opens) (ρ : Γ(X, U) →+* Γ(X', W)) :
    ∃ φ : W.toScheme ⟶ X, (∀ z, φ z ∈ U) ∧ ∀ (f : Γ(X, U)) z, gs φ z U f = gs W.ι z W (ρ f) := by
  refine ⟨(W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ)) ≫ hU.fromSpec,
    fun z => hU.range_fromSpec.le ⟨_, rfl⟩, fun f z => (gs_comp_fromSpec hU _ z f).trans ?_⟩
  have e : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ)).appTop =
      CommRingCat.ofHom ρ ≫ W.topIso.inv := by
    rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Opens.toSpecΓ_appTop,
      Iso.inv_hom_id_assoc]
  refine (congrArg (gs (𝟙 _) z ⊤) (congrArg (fun q => q.hom f) e)).trans ?_
  have e₂ := gs_appLE W.ι W ⊤ (fun x _ => x.2) (𝟙 _) z trivial (ρ f)
  rw [Category.id_comp] at e₂
  refine Eq.trans ?_ e₂
  exact congrArg (gs (𝟙 _) z ⊤) (congrArg (fun q => q.hom (ρ f)) (W.ι_appLE W ⊤ (fun x _ => x.2))).symm

theorem exists_quot {M : LB X} (t u : M.Sec) (W : X.Opens) (hW : W ≤ nonzeroLocus u) :
    ∃ f : Γ(X, W), ∀ (x : X) (j : M.ι), x ∈ W → x ∈ M.U j →
      gs (𝟙 X) x _ (t.f j) = gs (𝟙 X) x _ (u.f j) * gs (𝟙 X) x W f := by
  have hu : ∀ j, IsUnit (resG X (inf_le_right : W ⊓ M.U j ≤ M.U j) (u.f j)) := fun j =>
    X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have := (mem_nonzeroLocus_iff_isUnit u hy.2).1 (hW hy.1)
      rw [← gs_res (𝟙 X) y (inf_le_right : W ⊓ M.U j ≤ M.U j) hy, gs_eq _ y _ hy] at this
      exact this
  obtain ⟨v, hv⟩ : ∃ v : ∀ j, Γ(X, W ⊓ M.U j), ∀ (y : X) j, y ∈ W ⊓ M.U j →
      gs (𝟙 X) y _ (t.f j) = gs (𝟙 X) y _ (u.f j) * gs (𝟙 X) y _ (v j) :=
    ⟨fun j => ((hu j).unit⁻¹).val * resG X inf_le_right (t.f j), fun y j hy => by
      rw [← gs_res (𝟙 X) y (inf_le_right : W ⊓ M.U j ≤ M.U j) hy (u.f j), ← gs_mul _ y _ hy]
      refine (gs_res (𝟙 X) y (inf_le_right : W ⊓ M.U j ≤ M.U j) hy (t.f j)).symm.trans (congrArg _ ?_)
      rw [← _root_.mul_assoc, (hu j).mul_val_inv, _root_.one_mul]⟩
  obtain ⟨c, hc, -⟩ := DVR.sec_glue W (fun j => W ⊓ M.U j) (fun _ => inf_le_left) (fun y hy => by
      obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus (hW hy)
      exact Opens.mem_iSup.2 ⟨j, hy, hj⟩) v (fun a b => fn_ext fun y hy => by
      rw [gs_res _ y _ hy, gs_res _ y _ hy]
      have e₁ := hv y a hy.1
      have u₁ := (mem_nonzeroLocus_iff_isUnit u hy.1.2).1 (hW hy.1.1)
      rw [gs_compat t (𝟙 X) y hy.1.2 hy.2.2, hv y b hy.2, ← _root_.mul_assoc,
        ← gs_compat u (𝟙 X) y hy.1.2 hy.2.2] at e₁
      exact (u₁.mul_left_cancel e₁).symm)
  refine ⟨c, fun y j hW hj => (hv y j ⟨hW, hj⟩).trans (congrArg _ ?_)⟩
  exact (congrArg (gs (𝟙 X) y _) (hc j)).symm.trans (gs_res (𝟙 X) y inf_le_left ⟨hW, hj⟩ c)

end General

section Sections

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {n m k : ℕ}

abbrev ch (L : LB X) (j : Fin 1 → L.ι) : X.Opens := LB.wchart L (fun _ : Fin 1 => 𝟙 X) j

def fn (a : H0 L n) (j : Fin 1 → L.ι) : Γ(X, ch L j) := a.f j

abbrev sv (r : Z ⟶ X) (z : Z) (a : H0 L n) (j : Fin 1 → L.ι) : Z.presheaf.stalk z := gs r z (ch L j) (fn a j)

theorem mem_iff (a : H0 L n) (r : Z ⟶ X) (z : Z) {j : Fin 1 → L.ι} (hj : r z ∈ ch L j) :
    r z ∈ nonzeroLocus a ↔ IsUnit (sv r z a j) := mem_nonzeroLocus_iff_pull a r z (k := j) hj

theorem exists_ch {a : H0 L n} {x : X} (h : x ∈ nonzeroLocus a) : ∃ j, x ∈ ch L j :=
  exists_chart_of_mem_nonzeroLocus h

theorem sv_mul {a : H0 L n} {b : H0 L m} {d : H0 L k} (h : ∀ j, fn d j = fn a j * fn b j) (r : Z ⟶ X) (z : Z)
    {j : Fin 1 → L.ι} (hj : r z ∈ ch L j) : sv r z d j = sv r z a j * sv r z b j :=
  (congrArg (gs r z _) (h j)).trans (gs_mul r z _ hj _ _)

theorem sv_add {a b d : H0 L n} (h : ∀ j, fn d j = fn a j + fn b j) (r : Z ⟶ X) (z : Z)
    {j : Fin 1 → L.ι} (hj : r z ∈ ch L j) : sv r z d j = sv r z a j + sv r z b j :=
  (congrArg (gs r z _) (h j)).trans (gs_add r z _ hj _ _)

theorem sv_pow {a : H0 L n} {d : H0 L k} (h : ∀ j, fn d j = fn a j ^ m) (r : Z ⟶ X) (z : Z)
    {j : Fin 1 → L.ι} (hj : r z ∈ ch L j) : sv r z d j = sv r z a j ^ m :=
  (congrArg (gs r z _) (h j)).trans (gs_pow r z _ hj _ _)

theorem mem_mul {a : H0 L n} {b : H0 L m} {d : H0 L k} (h : ∀ j, fn d j = fn a j * fn b j) {x : X}
    (ha : x ∈ nonzeroLocus a) (hb : x ∈ nonzeroLocus b) : x ∈ nonzeroLocus d := by
  obtain ⟨j, hj⟩ := exists_ch ha
  refine (mem_iff d (𝟙 X) x hj).2 ?_
  rw [sv_mul h (𝟙 X) x hj]
  exact ((mem_iff a (𝟙 X) x hj).1 ha).mul ((mem_iff b (𝟙 X) x hj).1 hb)

theorem mem_pow {a : H0 L n} {d : H0 L k} (h : ∀ j, fn d j = fn a j ^ m) {x : X}
    (ha : x ∈ nonzeroLocus a) : x ∈ nonzeroLocus d := by
  obtain ⟨j, hj⟩ := exists_ch ha
  refine (mem_iff d (𝟙 X) x hj).2 ?_
  rw [sv_pow h (𝟙 X) x hj]
  exact ((mem_iff a (𝟙 X) x hj).1 ha).pow _

theorem exists_mul (a : H0 L n) (b : H0 L m) : ∃ d : H0 L (n + m), ∀ j, fn d j = fn a j * fn b j :=
  ⟨secOfGerm (M := LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => ((n + m : ℕ) : ℤ))) (fun j => fn a j * fn b j)
    fun y j j' hj hj' => by
      refine (gs_mul (𝟙 X) y _ hj (fn a j) (fn b j)).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val
        (gm_linComb L (fun _ : Fin 1 => 𝟙 X) _ (𝟙 X) y j j' hj hj')) (gs_mul (𝟙 X) y _ hj' (fn a j') (fn b j'))).symm)
      refine (congrArg₂ (· * ·) (sec_trans a (𝟙 X) y hj hj') (sec_trans b (𝟙 X) y hj hj')).trans ?_
      simp only [trF, Fintype.prod_unique, Nat.cast_add, zpow_add, Units.val_mul]
      exact mul_mul_mul_comm _ _ _ _, fun _ => rfl⟩

theorem exists_lin (c : Γ(X, ⊤)) (a b : H0 L n) :
    ∃ d : H0 L n, ∀ j, fn d j = fn a j + resG X (le_top : ch L j ≤ ⊤) c * fn b j :=
  ⟨DVR.SecOps.secAdd a (DVR.SecOps.secScale c b), fun _ => rfl⟩

def IsQuot (t u : H0 L n) (W : X.Opens) (f : Γ(X, W)) : Prop :=
  ∀ (x : X) (j : Fin 1 → L.ι), x ∈ W → x ∈ ch L j → sv (𝟙 X) x t j = sv (𝟙 X) x u j * gs (𝟙 X) x W f

theorem IsQuot.pull {t u : H0 L n} {W : X.Opens} {f : Γ(X, W)} (h : IsQuot t u W f) (r : Z ⟶ X) (z : Z)
    {j : Fin 1 → L.ι} (hW : r z ∈ W) (hj : r z ∈ ch L j) : sv r z t j = sv r z u j * gs r z W f := by
  rw [sv, sv, gs_stalkMap r z _ hj, gs_stalkMap r z _ hj, gs_stalkMap r z _ hW, ← map_mul]
  exact congrArg _ (h _ j hW hj)

theorem exists_isQuot (t u : H0 L n) (W : X.Opens) (hW : W ≤ nonzeroLocus u) : ∃ f, IsQuot t u W f :=
  exists_quot t u W hW

def PresMul (θ : ∀ n : ℕ, 1 ≤ n → (H0 L' n ≃ H0 L n)) : Prop :=
  ∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 L' n) (b : H0 L' m) (d : H0 L' (n + m)),
    (∀ j, fn d j = fn a j * fn b j) →
      ∀ j, fn (θ (n + m) (hn.trans (Nat.le_add_right n m)) d) j = fn (θ n hn a) j * fn (θ m hm b) j

def PresAdd (θ : ∀ n : ℕ, 1 ≤ n → (H0 L' n ≃ H0 L n)) : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (a b d : H0 L' n), (∀ j, fn d j = fn a j + fn b j) →
    ∀ j, fn (θ n hn d) j = fn (θ n hn a) j + fn (θ n hn b) j

variable {θ : ∀ n : ℕ, 1 ≤ n → (H0 L' n ≃ H0 L n)}

theorem presMul_refl : PresMul (L := L) (L' := L) (fun _ _ => Equiv.refl _) := fun _ _ _ _ _ _ _ h => h

theorem PresMul.exists_mul (h : PresMul θ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hk : 1 ≤ k) (e : k = n + m) (a : H0 L' n)
    (b : H0 L' m) : ∃ d : H0 L' k, (∀ j, fn d j = fn a j * fn b j) ∧
      ∀ j, fn (θ k hk d) j = fn (θ n hn a) j * fn (θ m hm b) j := by
  subst e
  obtain ⟨d, hd⟩ := SecRingIso.exists_mul a b
  exact ⟨d, hd, h n m hn hm a b d hd⟩

theorem PresAdd.exists_add (h : PresAdd θ) (hn : 1 ≤ n) (a b : H0 L' n) :
    ∃ d : H0 L' n, (∀ j, fn d j = fn a j + fn b j) ∧ ∀ j, fn (θ n hn d) j = fn (θ n hn a) j + fn (θ n hn b) j :=
  ⟨DVR.SecOps.secAdd a b, fun _ => rfl, h n hn a b _ fun _ => rfl⟩

theorem PresMul.exists_pow (h : PresMul θ) (hn : 1 ≤ n) (a : H0 L' n) (m : ℕ) : ∀ (k : ℕ) (hk : 1 ≤ k),
    k = n * (m + 1) → ∃ d : H0 L' k, (∀ j, fn d j = fn a j ^ (m + 1)) ∧
      ∀ j, fn (θ k hk d) j = fn (θ n hn a) j ^ (m + 1) := by
  induction m with
  | zero =>
    intro k hk e
    obtain rfl : k = n := by simpa using e
    exact ⟨a, fun _ => by simp, fun _ => by simp⟩
  | succ m ih =>
    intro k hk e
    have h₁ : 1 ≤ n * (m + 1) := Nat.mul_pos hn (Nat.succ_pos m)
    obtain ⟨u, hu, hu'⟩ := ih _ h₁ rfl
    obtain ⟨d, hd, hd'⟩ := h.exists_mul h₁ hn hk e u a
    exact ⟨d, fun j => by rw [hd, hu, ← pow_succ], fun j => by rw [hd', hu', ← pow_succ]⟩

theorem PresMul.symm (h : PresMul θ) : PresMul (fun n hn => (θ n hn).symm) := fun n m hn hm a b d hd j => by
  obtain ⟨e, he, he'⟩ := h.exists_mul hn hm (hn.trans (Nat.le_add_right n m)) rfl ((θ n hn).symm a) ((θ m hm).symm b)
  simp only [Equiv.apply_symm_apply] at he'
  obtain rfl : d = θ _ (hn.trans (Nat.le_add_right n m)) e := DVR.SecOps.sec_ext fun j => (hd j).trans (he' j).symm
  simp only [Equiv.symm_apply_apply]
  exact he j

theorem PresAdd.symm (h : PresAdd θ) : PresAdd (fun n hn => (θ n hn).symm) := fun n hn a b d hd j => by
  obtain ⟨e, he, he'⟩ := h.exists_add hn ((θ n hn).symm a) ((θ n hn).symm b)
  simp only [Equiv.apply_symm_apply] at he'
  obtain rfl : d = θ _ hn e := DVR.SecOps.sec_ext fun j => (hd j).trans (he' j).symm
  simp only [Equiv.symm_apply_apply]
  exact he j

theorem exists_numerator [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (σ : H0 L n)
    (f : Γ(X, nonzeroLocus σ)) : ∃ (m : ℕ) (t : H0 L (n * (m + 1))), ∀ u : H0 L (n * (m + 1)),
      (∀ j, fn u j = fn σ j ^ (m + 1)) → IsQuot t u _ f := by
  obtain ⟨m, τ, hτ⟩ := (sec_extend_of_nonzeroLocus X L hL n σ).1 f
  obtain ⟨t, ht⟩ := exists_mul τ σ
  refine ⟨m, t, fun u hu x j hx hj => ?_⟩
  have e : sv (𝟙 X) x τ j = sv (𝟙 X) x σ j ^ m * gs (𝟙 X) x _ f := hτ x j hx ((mem_wchart_oneTerm 0).1 hj)
  refine (sv_mul ht (𝟙 X) x hj).trans ?_
  rw [sv_pow hu (𝟙 X) x hj, e]
  ring

theorem PresMul.transfer [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (h : PresMul θ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (s : H0 L' n) (a b : H0 L' k) (e : ∀ (x : X) j, x ∈ nonzeroLocus (θ n hn s) → x ∈ ch L j →
      sv (𝟙 X) x (θ k hk a) j = sv (𝟙 X) x (θ k hk b) j) (x : X') (j : Fin 1 → L'.ι) (hx : x ∈ nonzeroLocus s)
    (hj : x ∈ ch L' j) : sv (𝟙 X') x a j = sv (𝟙 X') x b j := by
  obtain ⟨d, hd₀⟩ := exists_lin (-1) (θ k hk a) (θ k hk b)
  have hd : ∀ j, fn d j = fn (θ k hk a) j - fn (θ k hk b) j := fun j => by
    rw [hd₀, map_neg, map_one]; ring
  obtain ⟨m, hm⟩ := (sec_extend_of_nonzeroLocus X L hL n (θ n hn s)).2 k d fun y i hy hi => by
    have hi' : y ∈ ch L i := (mem_wchart_oneTerm 0).2 hi
    exact (congrArg (gs (𝟙 X) y _) (hd i)).trans ((gs_sub _ y _ hi' _ _).trans (sub_eq_zero.2 (e y i hy hi')))
  have hm' : ∀ j, fn (θ n hn s) j ^ m * fn d j = 0 := hm
  have h₁ : 1 ≤ n * (m + 1) := Nat.mul_pos hn (Nat.succ_pos m)
  obtain ⟨u, hu, hu'⟩ := h.exists_pow hn s m _ h₁ rfl
  obtain ⟨p, hp, hp'⟩ := h.exists_mul h₁ hk (h₁.trans (Nat.le_add_right _ k)) rfl u a
  obtain ⟨q, hq, hq'⟩ := h.exists_mul h₁ hk (h₁.trans (Nat.le_add_right _ k)) rfl u b
  obtain rfl : p = q := (θ _ (h₁.trans (Nat.le_add_right _ k))).injective (DVR.SecOps.sec_ext fun i : Fin 1 → L.ι => by
    refine (hp' i).trans (Eq.trans ?_ (hq' i).symm)
    have := hm' i
    rw [hd] at this
    rw [hu']
    linear_combination fn (θ n hn s) i * this)
  exact ((mem_iff u (𝟙 X') x hj).1 (mem_pow hu hx)).mul_left_cancel
    ((sv_mul hp (𝟙 X') x hj).symm.trans (sv_mul hq (𝟙 X') x hj))

end Sections

section Relation

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {n m k : ℕ}

def Corresp (θ : ∀ n : ℕ, 1 ≤ n → (H0 L' n ≃ H0 L n)) (φ : Z ⟶ X) (ψ : Z ⟶ X') : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (a b : H0 L' n) (z : Z), (φ z ∈ nonzeroLocus (θ n hn b) ↔ ψ z ∈ nonzeroLocus b) ∧
    ∀ j j', ψ z ∈ nonzeroLocus b → φ z ∈ ch L j → ψ z ∈ ch L' j' →
      sv φ z (θ n hn a) j * sv ψ z b j' = sv φ z (θ n hn b) j * sv ψ z a j'

variable {θ : ∀ n : ℕ, 1 ≤ n → (H0 L' n ≃ H0 L n)} {φ φ₁ φ₂ : Z ⟶ X} {ψ : Z ⟶ X'}

theorem Corresp.comp (h : Corresp θ φ ψ) (r : Y ⟶ Z) : Corresp θ (r ≫ φ) (r ≫ ψ) := fun n hn a b y =>
  ⟨(h n hn a b (r y)).1, fun j j' hb hj hj' => by
    rw [sv, sv, sv, sv, gs_comp r φ y _ hj, gs_comp r φ y _ hj, gs_comp r ψ y _ hj', gs_comp r ψ y _ hj', ← map_mul,
      ← map_mul]
    exact congrArg _ ((h n hn a b (r y)).2 j j' hb hj hj')⟩

theorem Corresp.of_local (h : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧ Corresp θ (U.ι ≫ φ) (U.ι ≫ ψ)) : Corresp θ φ ψ :=
  fun n hn a b z => by
    obtain ⟨U, hz, H⟩ := h z
    obtain ⟨y, rfl⟩ : ∃ y : U.toScheme, U.ι y = z := ⟨⟨z, hz⟩, rfl⟩
    refine ⟨(H n hn a b y).1, fun j j' hb hj hj' => ?_⟩
    have e := (H n hn a b y).2 j j' hb hj hj'
    rw [sv, sv, sv, sv, gs_comp U.ι φ y _ hj, gs_comp U.ι φ y _ hj, gs_comp U.ι ψ y _ hj', gs_comp U.ι ψ y _ hj',
      ← map_mul, ← map_mul] at e
    exact (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap y)).1 e

theorem Corresp.symm (h : Corresp θ φ ψ) : Corresp (fun n hn => (θ n hn).symm) ψ φ := fun n hn a b z => by
  obtain ⟨a, rfl⟩ := (θ n hn).surjective a
  obtain ⟨b, rfl⟩ := (θ n hn).surjective b
  simp only [Equiv.symm_apply_apply]
  refine ⟨(h n hn a b z).1.symm, fun j' j hb hj' hj => ?_⟩
  rw [mul_comm, ← (h n hn a b z).2 j j' ((h n hn a b z).1.1 hb) hj hj', mul_comm]

theorem Corresp.unique_affine [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (h₁ : Corresp θ φ₁ ψ)
    (h₂ : Corresp θ φ₂ ψ) (hn : 1 ≤ n) (σ : H0 L n) (hσ : IsAffineOpen (nonzeroLocus σ))
    (hφ : ∀ z, φ₁ z ∈ nonzeroLocus σ) : φ₁ = φ₂ := by
  obtain ⟨s, rfl⟩ := (θ n hn).surjective σ
  have hφ₂ : ∀ z, φ₂ z ∈ nonzeroLocus (θ n hn s) := fun z => (h₂ n hn s s z).1.2 ((h₁ n hn s s z).1.1 (hφ z))
  refine hom_ext_affine hσ hφ hφ₂ fun f z => ?_
  obtain ⟨m, t, ht⟩ := exists_numerator hL _ f
  have hk : 1 ≤ n * (m + 1) := Nat.mul_pos hn (Nat.succ_pos m)
  obtain ⟨u, hu, -⟩ := presMul_refl.exists_pow hn (θ n hn s) m _ hk rfl
  have hq := ht u hu
  obtain ⟨a, rfl⟩ := (θ _ hk).surjective t
  obtain ⟨b, rfl⟩ := (θ _ hk).surjective u
  have hb : ψ z ∈ nonzeroLocus b := (h₁ _ hk a b z).1.1 (mem_pow hu (hφ z))
  obtain ⟨j', hj'⟩ := exists_ch hb
  have key : ∀ χ : Z ⟶ X, Corresp θ χ ψ → χ z ∈ nonzeroLocus (θ n hn s) →
      sv ψ z b j' * gs χ z _ f = sv ψ z a j' := fun χ h hχ => by
    obtain ⟨j, hj⟩ := exists_ch hχ
    have e := (h _ hk a b z).2 j j' hb hj hj'
    rw [hq.pull χ z hχ hj, _root_.mul_assoc] at e
    rw [mul_comm]
    exact ((mem_iff _ χ z hj).1 (mem_pow hu hχ)).mul_left_cancel e
  exact ((mem_iff b ψ z hj').1 hb).mul_left_cancel ((key φ₁ h₁ (hφ z)).trans (key φ₂ h₂ (hφ₂ z)).symm)

theorem Corresp.unique [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (h₁ : Corresp θ φ₁ ψ)
    (h₂ : Corresp θ φ₂ ψ) (hn : 1 ≤ n) {κ : Type} (σ : κ → H0 L n) (hc : ⨆ i, nonzeroLocus (σ i) = ⊤)
    (hσ : ∀ i, IsAffineOpen (nonzeroLocus (σ i))) : φ₁ = φ₂ := by
  refine Scheme.hom_ext_of_forall _ _ fun z => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ (φ₁ z)))
  exact ⟨φ₁ ⁻¹ᵁ nonzeroLocus (σ i), hi, (h₁.comp _).unique_affine hL (h₂.comp _) hn (σ i) (hσ i) fun y => y.2⟩

def FnCorresp (θ : ∀ n : ℕ, 1 ≤ n → (H0 L' n ≃ H0 L n)) (hn : 1 ≤ n) (s : H0 L' n)
    (f : Γ(X, nonzeroLocus (θ n hn s))) (g : Γ(X', nonzeroLocus s)) : Prop :=
  ∃ (k : ℕ) (hk : 1 ≤ k) (t u : H0 L' k), nonzeroLocus s ≤ nonzeroLocus u ∧
    nonzeroLocus (θ n hn s) ≤ nonzeroLocus (θ k hk u) ∧ IsQuot (θ k hk t) (θ k hk u) _ f ∧ IsQuot t u _ g

variable {hn : 1 ≤ n} {s : H0 L' n}

theorem FnCorresp.unique [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (hM : PresMul θ)
    {f : Γ(X, nonzeroLocus (θ n hn s))} {g g' : Γ(X', nonzeroLocus s)} (h : FnCorresp θ hn s f g)
    (h' : FnCorresp θ hn s f g') : g = g' := by
  obtain ⟨k, hk, t, u, hu, -, hf, hg⟩ := h
  obtain ⟨k', hk', t', u', hu', -, hf', hg'⟩ := h'
  have hkk : 1 ≤ k + k' := hk.trans (Nat.le_add_right _ _)
  obtain ⟨p, hp, hp'⟩ := hM.exists_mul hk hk' hkk rfl t u'
  obtain ⟨q, hq, hq'⟩ := hM.exists_mul hk hk' hkk rfl u t'
  refine fn_ext fun x hx => ?_
  obtain ⟨j, hj⟩ := exists_ch hx
  have e := hM.transfer hL hn hkk s p q (fun y i hy hi => by
    rw [sv_mul hp' (𝟙 X) y hi, sv_mul hq' (𝟙 X) y hi, hf y i hy hi, hf' y i hy hi]; ring) x j hx hj
  rw [sv_mul hp (𝟙 X') x hj, sv_mul hq (𝟙 X') x hj, hg x j hx hj, hg' x j hx hj] at e
  refine (((mem_iff u (𝟙 X') x hj).1 (hu hx)).mul ((mem_iff u' (𝟙 X') x hj).1 (hu' hx))).mul_left_cancel ?_
  linear_combination e

theorem FnCorresp.exists [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (hM : PresMul θ)
    (f : Γ(X, nonzeroLocus (θ n hn s))) : ∃ g, FnCorresp θ hn s f g := by
  obtain ⟨m, t, ht⟩ := exists_numerator hL _ f
  have hk : 1 ≤ n * (m + 1) := Nat.mul_pos hn (Nat.succ_pos m)
  obtain ⟨u, hu, hu'⟩ := hM.exists_pow hn s m _ hk rfl
  obtain ⟨t, rfl⟩ := (θ _ hk).surjective t
  obtain ⟨g, hg⟩ := exists_isQuot t u (nonzeroLocus s) fun _ hx => mem_pow hu hx
  exact ⟨g, _, hk, t, u, fun _ hx => mem_pow hu hx, fun _ hx => mem_pow hu' hx, ht _ hu', hg⟩

theorem isQuot_one (u : H0 L n) (W : X.Opens) : IsQuot u u W 1 := fun x j hx _ => by
  rw [gs_eq (𝟙 X) x W hx, map_one, map_one, _root_.mul_one]

theorem FnCorresp.one : FnCorresp θ hn s 1 1 := ⟨n, hn, s, s, le_rfl, le_rfl, isQuot_one _ _, isQuot_one _ _⟩

theorem IsQuot.mul {W : X.Opens} {t u : H0 L n} {t' u' : H0 L m} {p q : H0 L k} {f f' : Γ(X, W)}
    (h : IsQuot t u W f) (h' : IsQuot t' u' W f') (hp : ∀ j, fn p j = fn t j * fn t' j)
    (hq : ∀ j, fn q j = fn u j * fn u' j) : IsQuot p q W (f * f') := fun x j hx hj => by
  rw [sv_mul hp (𝟙 X) x hj, sv_mul hq (𝟙 X) x hj, gs_mul (𝟙 X) x W hx, h x j hx hj, h' x j hx hj]
  ring

theorem IsQuot.add {W : X.Opens} {t u : H0 L n} {t' u' : H0 L m} {p p₁ p₂ q : H0 L k} {f f' : Γ(X, W)}
    (h : IsQuot t u W f) (h' : IsQuot t' u' W f') (hp₁ : ∀ j, fn p₁ j = fn t j * fn u' j)
    (hp₂ : ∀ j, fn p₂ j = fn u j * fn t' j) (hp : ∀ j, fn p j = fn p₁ j + fn p₂ j)
    (hq : ∀ j, fn q j = fn u j * fn u' j) : IsQuot p q W (f + f') := fun x j hx hj => by
  rw [sv_add hp (𝟙 X) x hj, sv_mul hp₁ (𝟙 X) x hj, sv_mul hp₂ (𝟙 X) x hj, sv_mul hq (𝟙 X) x hj,
    gs_add (𝟙 X) x W hx, h x j hx hj, h' x j hx hj]
  ring

theorem FnCorresp.mul (hM : PresMul θ) {f f' : Γ(X, nonzeroLocus (θ n hn s))} {g g' : Γ(X', nonzeroLocus s)}
    (h : FnCorresp θ hn s f g) (h' : FnCorresp θ hn s f' g') : FnCorresp θ hn s (f * f') (g * g') := by
  obtain ⟨k, hk, t, u, hu, hv, hf, hg⟩ := h
  obtain ⟨k', hk', t', u', hu', hv', hf', hg'⟩ := h'
  have hkk : 1 ≤ k + k' := hk.trans (Nat.le_add_right _ _)
  obtain ⟨p, hp, hp'⟩ := hM.exists_mul hk hk' hkk rfl t t'
  obtain ⟨q, hq, hq'⟩ := hM.exists_mul hk hk' hkk rfl u u'
  exact ⟨_, hkk, p, q, fun _ hx => mem_mul hq (hu hx) (hu' hx), fun _ hx => mem_mul hq' (hv hx) (hv' hx),
    hf.mul hf' hp' hq', hg.mul hg' hp hq⟩

theorem FnCorresp.add (hM : PresMul θ) (hA : PresAdd θ) {f f' : Γ(X, nonzeroLocus (θ n hn s))}
    {g g' : Γ(X', nonzeroLocus s)} (h : FnCorresp θ hn s f g) (h' : FnCorresp θ hn s f' g') :
    FnCorresp θ hn s (f + f') (g + g') := by
  obtain ⟨k, hk, t, u, hu, hv, hf, hg⟩ := h
  obtain ⟨k', hk', t', u', hu', hv', hf', hg'⟩ := h'
  have hkk : 1 ≤ k + k' := hk.trans (Nat.le_add_right _ _)
  obtain ⟨p₁, hp₁, hp₁'⟩ := hM.exists_mul hk hk' hkk rfl t u'
  obtain ⟨p₂, hp₂, hp₂'⟩ := hM.exists_mul hk hk' hkk rfl u t'
  obtain ⟨p, hp, hp'⟩ := hA.exists_add hkk p₁ p₂
  obtain ⟨q, hq, hq'⟩ := hM.exists_mul hk hk' hkk rfl u u'
  exact ⟨_, hkk, p, q, fun _ hx => mem_mul hq (hu hx) (hu' hx), fun _ hx => mem_mul hq' (hv hx) (hv' hx),
    hf.add hf' hp₁' hp₂' hp' hq', hg.add hg' hp₁ hp₂ hp hq⟩

theorem exists_ringHom [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (hM : PresMul θ) (hA : PresAdd θ)
    (hn : 1 ≤ n) (s : H0 L' n) : ∃ ρ : Γ(X, nonzeroLocus (θ n hn s)) →+* Γ(X', nonzeroLocus s),
      ∀ f g, FnCorresp θ hn s f g → ρ f = g := by
  choose ρ hρ using FnCorresp.exists (hn := hn) (s := s) hL hM
  have a : ∀ f f', ρ (f + f') = ρ f + ρ f' := fun f f' => (hρ _).unique hL hM ((hρ f).add hM hA (hρ f'))
  exact ⟨⟨⟨⟨ρ, (hρ _).unique hL hM FnCorresp.one⟩, fun f f' => (hρ _).unique hL hM ((hρ f).mul hM (hρ f'))⟩,
    by simpa using a 0 0, a⟩, fun f g h => (hρ f).unique hL hM h⟩

theorem exists_local_hom [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (hM : PresMul θ)
    (hA : PresAdd θ) (hn : 1 ≤ n) (s : H0 L' n) (hs : IsAffineOpen (nonzeroLocus (θ n hn s))) :
    ∃ φ : (nonzeroLocus s).toScheme ⟶ X, Corresp θ φ (nonzeroLocus s).ι := by
  obtain ⟨ρ, hρ⟩ := exists_ringHom hL hM hA hn s
  obtain ⟨φ, hφ, hg⟩ := exists_hom_of_ringHom hs (nonzeroLocus s) ρ
  refine ⟨φ, fun m hm a b z => ?_⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hz : (nonzeroLocus s).ι z ∈ nonzeroLocus s := z.2
  have h₁ : 1 ≤ (m' + 1) * (2 * n' + 1) := Nat.mul_pos hm (Nat.succ_pos _)
  have h₂ : 1 ≤ (n' + 1) * (2 * m' + 1 + 1) := Nat.mul_pos hn (Nat.succ_pos _)
  obtain ⟨w, hw, hw'⟩ := hM.exists_pow hm b (2 * n') _ h₁ rfl
  obtain ⟨u, hu, hu'⟩ := hM.exists_pow hn s (2 * m' + 1) _ h₂ rfl
  have key : ∀ c : H0 L' (m' + 1), ∃ v : (nonzeroLocus s).toScheme.presheaf.stalk z,
      (∀ j, φ z ∈ ch L j → sv φ z (θ _ hm c) j * sv φ z (θ _ hm b) j ^ (2 * n' + 1) = sv φ z (θ _ h₂ u) j * v) ∧
      ∀ j, (nonzeroLocus s).ι z ∈ ch L' j → sv (nonzeroLocus s).ι z c j * sv (nonzeroLocus s).ι z b j ^ (2 * n' + 1) =
        sv (nonzeroLocus s).ι z u j * v := fun c => by
    obtain ⟨t, ht, ht'⟩ := hM.exists_mul hm h₁ h₂ (by ring) c w
    obtain ⟨f, hf⟩ := exists_isQuot (θ _ h₂ t) (θ _ h₂ u) (nonzeroLocus (θ _ hn s)) fun _ hx => mem_pow hu' hx
    obtain ⟨g, hg'⟩ := exists_isQuot t u (nonzeroLocus s) fun _ hx => mem_pow hu hx
    obtain rfl := hρ f g ⟨_, h₂, t, u, fun _ hx => mem_pow hu hx, fun _ hx => mem_pow hu' hx, hf, hg'⟩
    refine ⟨gs φ z _ f, fun j hj => ?_, fun j hj => ?_⟩
    · rw [← hf.pull φ z (hφ z) hj, sv_mul ht' φ z hj, sv_pow hw' φ z hj]
    · rw [hg, ← hg'.pull _ z hz hj, sv_mul ht _ z hj, sv_pow hw _ z hj]
  obtain ⟨va, ha, ha'⟩ := key a
  obtain ⟨vb, hb, hb'⟩ := key b
  have loc : φ z ∈ nonzeroLocus (θ _ hm b) ↔ (nonzeroLocus s).ι z ∈ nonzeroLocus b := by
    obtain ⟨j, hj⟩ := exists_ch (hφ z)
    obtain ⟨j', hj'⟩ := exists_ch hz
    have e := congrArg IsUnit (hb j hj)
    have e' := congrArg IsUnit (hb' j' hj')
    rw [← pow_succ', isUnit_pow_succ_iff, IsUnit.mul_iff] at e e'
    rw [mem_iff _ φ z hj, mem_iff _ _ z hj', e, e', and_iff_right ((mem_iff _ φ z hj).1 (mem_pow hu' (hφ z))),
      and_iff_right ((mem_iff _ _ z hj').1 (mem_pow hu hz))]
  refine ⟨loc, fun j j' hzb hj hj' => ?_⟩
  refine ((((mem_iff _ φ z hj).1 (loc.2 hzb)).pow (2 * n' + 1)).mul
    (((mem_iff _ _ z hj').1 hzb).pow (2 * n' + 1))).mul_left_cancel ?_
  have e₁ := congrArg₂ (· * ·) (ha j hj) (hb' j' hj')
  have e₂ := congrArg₂ (· * ·) (hb j hj) (ha' j' hj')
  linear_combination e₁ - e₂

theorem exists_hom [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (hM : PresMul θ)
    (hA : PresAdd θ) (hn : 1 ≤ n) {κ : Type} (s : κ → H0 L' n) (hc' : ⨆ i, nonzeroLocus (s i) = ⊤)
    (hc : ⨆ i, nonzeroLocus (θ n hn (s i)) = ⊤) (hs : ∀ i, IsAffineOpen (nonzeroLocus (θ n hn (s i)))) :
    ∃ Φ : X' ⟶ X, Corresp θ Φ (𝟙 X') := by
  choose φ hφ using fun i => exists_local_hom hL hM hA hn (s i) (hs i)
  let 𝒰 := X'.openCoverOfIsOpenCover (fun i => nonzeroLocus (s i)) hc'
  have hcomp : ∀ i j : κ, pullback.fst (nonzeroLocus (s i)).ι (nonzeroLocus (s j)).ι ≫ φ i =
      pullback.snd _ _ ≫ φ j := fun i j =>
    ((hφ i).comp _).unique hL (by rw [pullback.condition]; exact (hφ j).comp _) hn _ hc hs
  have hΦ : ∀ i : κ, (nonzeroLocus (s i)).ι ≫ 𝒰.glueMorphisms φ hcomp = φ i := fun i => 𝒰.ι_glueMorphisms φ hcomp i
  refine ⟨𝒰.glueMorphisms φ hcomp, Corresp.of_local fun x => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc'.ge (Set.mem_univ x))
  exact ⟨_, hi, by rw [hΦ, Category.comp_id]; exact hφ i⟩

end Relation

theorem Corresp.over {R : Type} [CommRing R] {X X' Z : Scheme.{0}} {L : LB X} {L' : LB X'}
    {θ : ∀ n : ℕ, 1 ≤ n → (H0 L' n ≃ H0 L n)} {φ : Z ⟶ X} {ψ : Z ⟶ X'} (h : Corresp θ φ ψ)
    (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of R)) {n : ℕ} (hn : 1 ≤ n)
    (hθ : ∀ (c : R) (a b d : H0 L' n), (∀ j, fn d j = fn a j + resG X' (le_top : ch L' j ≤ ⊤) (scal p' c) * fn b j) →
      ∀ j, fn (θ n hn d) j = fn (θ n hn a) j + resG X (le_top : ch L j ≤ ⊤) (scal p c) * fn (θ n hn b) j)
    {κ : Type} (s : κ → H0 L' n) (hc : ⨆ i, nonzeroLocus (s i) = ⊤) : φ ≫ p = ψ ≫ p' := by
  refine hom_ext_spec fun c z => ?_
  have v : ∀ {Y : Scheme.{0}} (χ : Z ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of R)),
      gs (𝟙 Z) z ⊤ ((χ ≫ q).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) = gs χ z ⊤ (scal q c) :=
    fun χ q => by
      have e := gs_pull (𝟙 Z) χ z ⊤ trivial (scal q c)
      rw [Category.id_comp] at e
      exact e
  rw [v, v]
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ (ψ z)))
  have hi' := (h n hn (s i) (s i) z).1.2 hi
  obtain ⟨j, hj⟩ := exists_ch hi'
  obtain ⟨j', hj'⟩ := exists_ch hi
  obtain ⟨d, hd⟩ := exists_lin (scal p' c) (s i) (s i)
  have e := (h n hn d (s i) z).2 j j' hi hj hj'
  rw [sv, sv, sv, sv, hθ c _ _ d hd, hd, gs_add φ z _ hj, gs_add ψ z _ hj', gs_mul φ z _ hj, gs_mul ψ z _ hj',
    gs_res φ z _ hj, gs_res ψ z _ hj'] at e
  refine (((mem_iff _ φ z hj).1 hi').mul ((mem_iff _ ψ z hj').1 hi)).mul_left_cancel ?_
  linear_combination e

end SecRingIso

open SecRingIso in

theorem exists_iso_of_sectionRing_equiv : ∀ (R : Type) [CommRing R] (X X' : Over (Spec (CommRingCat.of R))) [CompactSpace X.left] [QuasiSeparatedSpace X.left] [CompactSpace X'.left] [QuasiSeparatedSpace X'.left] (L : LB X.left) (L' : LB X'.left), L.IsLB → L'.IsLB → ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 L' n ≃ H0 L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : R) (a b d : H0 L' n), (∀ j, d.f j = a.f j + resTop _ (scal X'.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal X.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 L' n) (b : H0 L' m) (d : H0 L' (n + m)), (∀ j : Fin 1 → L'.ι, (show Γ(X'.left, LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) j) from d.f j) = (show Γ(X'.left, LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) j) from a.f j) * (show Γ(X'.left, LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) j) from b.f j)) → ∀ j : Fin 1 → L.ι, (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ n hn a).f j) * (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ m hm b).f j)) → (∃ (N : ℕ) (hN : 1 ≤ N) (κ : Type) (s : κ → H0 L' N), (⨆ i, nonzeroLocus (s i) = ⊤) ∧ (⨆ i, nonzeroLocus (θ N hN (s i)) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧ IsAffineOpen (nonzeroLocus (θ N hN (s i)))) → ∃ Φ : X' ≅ X, (∀ (n : ℕ) (hn : 1 ≤ n) (a b : H0 L' n), Φ.hom.left ⁻¹ᵁ nonzeroLocus (θ n hn b) = nonzeroLocus b ∧ ∀ (x : X'.left) (j : Fin 1 → L.ι) (j' : Fin 1 → L'.ι), x ∈ nonzeroLocus b → Φ.hom.left x ∈ L.U (j 0) → x ∈ L'.U (j' 0) → Geo.Tor.gs Φ.hom.left x _ ((θ n hn a).f j) * Geo.Tor.gs (𝟙 X'.left) x _ (b.f j') = Geo.Tor.gs Φ.hom.left x _ ((θ n hn b).f j) * Geo.Tor.gs (𝟙 X'.left) x _ (a.f j')) := by
  intro R _ X X' _ _ _ _ L L' hL hL' θ hlin hmul ⟨N, hN, κ, s, hc', hc, hs⟩
  have hθ : ∀ (n : ℕ) (hn : 1 ≤ n) (c : R) (a b d : H0 L' n),
      (∀ j, fn d j = fn a j + Geo.Tor.resG X'.left (le_top : ch L' j ≤ ⊤) (scal X'.hom c) * fn b j) →
      ∀ j, fn (θ n hn d) j = fn (θ n hn a) j +
        Geo.Tor.resG X.left (le_top : ch L j ≤ ⊤) (scal X.hom c) * fn (θ n hn b) j := hlin
  have hM : PresMul θ := hmul
  have hA : PresAdd θ := fun n hn a b d hd j => by
    have e := hθ n hn 1 a b d (fun j => by rw [hd, scal, map_one, map_one, map_one, _root_.one_mul]) j
    rwa [scal, map_one, map_one, map_one, _root_.one_mul] at e
  obtain ⟨Φ, hΦ⟩ := exists_hom hL hM hA hN s hc' hc fun i => (hs i).2
  obtain ⟨Ψ, hΨ⟩ := exists_hom hL' hM.symm hA.symm hN (fun i => θ N hN (s i)) hc
    (by simpa only [Equiv.symm_apply_apply] using hc') fun i => by
      simpa only [Equiv.symm_apply_apply] using (hs i).1
  have e₁ : Φ ≫ Ψ = 𝟙 _ := (hΨ.comp Φ).unique hL' (by rw [Category.comp_id]; exact hΦ.symm) hN s hc'
    fun i => (hs i).1
  have e₂ : Ψ ≫ Φ = 𝟙 _ := (hΦ.comp Ψ).unique hL (by rw [Category.comp_id]; exact hΨ.symm) hN _ hc
    fun i => (hs i).2
  refine ⟨Over.isoMk ⟨Φ, Ψ, e₁, e₂⟩ ((hΦ.over X.hom X'.hom hN (hθ N hN) s hc').trans (Category.id_comp _)),
    fun n hn a b => ⟨TopologicalSpace.Opens.ext (Set.ext fun x => (hΦ n hn a b x).1), fun x j j' hx hj hj' => ?_⟩⟩
  exact (hΦ n hn a b x).2 j j' hx ((mem_wchart_oneTerm 0).2 hj) ((mem_wchart_oneTerm 0).2 hj')

end GlobalTheory
