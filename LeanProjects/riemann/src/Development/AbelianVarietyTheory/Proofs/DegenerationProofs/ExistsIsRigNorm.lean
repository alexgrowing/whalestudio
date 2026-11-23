import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInverseExtensionProperClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyThetaExtensionTest
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnEqOfFineCharts

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.TestNorm

open CubeGen

variable {p : ℕ} [Fact p.Prime]

section Bundle

variable {H HK A : Scheme.{0}} {M : LB H} {L : LB A} {j : HK ⟶ H} {φ : HK ⟶ A}

def wg (w : LB.Iso (L.pull φ) (M.pull j)) {Z : Scheme.{0}} (q : Z ⟶ HK) (z : Z) (a : M.ι) (b : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm q z ((M.pull j).U (fun _ => a) ⊓ (L.pull φ).U (fun _ => b)) (w.s (fun _ => a, fun _ => b))

theorem wg_trans {w : LB.Iso (L.pull φ) (M.pull j)} (hw : w.IsGen) {Z : Scheme.{0}} (q : Z ⟶ HK) (z : Z)
    {a a' : M.ι} {b b' : L.ι} (ha : j (q z) ∈ M.U a) (ha' : j (q z) ∈ M.U a') (hb : φ (q z) ∈ L.U b)
    (hb' : φ (q z) ∈ L.U b') :
    wg w q z a b = gm (q ≫ j) z _ (M.g a a') * (gm (q ≫ φ) z _ (L.g b b'))⁻¹ * wg w q z a' b' := by
  have hm : q z ∈ (M.pull j).U (fun _ => a) ⊓ (L.pull φ).U (fun _ => b) ⊓
      ((M.pull j).U (fun _ => a') ⊓ (L.pull φ).U (fun _ => b')) :=
    ⟨⟨mem_pull.2 ha, mem_pull.2 hb⟩, mem_pull.2 ha', mem_pull.2 hb'⟩
  have e := congrArg (gm q z _) (hw (fun _ => a, fun _ => b) (fun _ => a', fun _ => b'))
  refine (gm_res q z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div (L.pull φ) (M.pull j) q z (fun _ => a, fun _ => b) (fun _ => a', fun _ => b') hm).trans ?_)
    (gm_res q z _ hm _))))
  exact congrArg₂ (fun s t => s * t⁻¹) (gm_pull_g M j q z _ _ hm.1.1 hm.2.1) (gm_pull_g L φ q z _ _ hm.1.2 hm.2.2)

def wv (w : LB.Iso (L.pull φ) (M.pull j)) (q : Sp (PadicAlgCl p) ⟶ HK) (a : M.ι) (b : L.ι) : ℝ :=
  un p (wg w q (z₀ p) a b)

theorem wv_pos (w : LB.Iso (L.pull φ) (M.pull j)) (q : Sp (PadicAlgCl p) ⟶ HK) (a : M.ι) (b : L.ι) :
    0 < wv w q a b := un_pos _

theorem wv_trans {w : LB.Iso (L.pull φ) (M.pull j)} (hw : w.IsGen) {c : Sp (OO p) ⟶ H}
    {q : Sp (PadicAlgCl p) ⟶ HK} (h : q ≫ j = gPt p ≫ c) {a a' : M.ι} {b b' : L.ι} (ha : c (cPt p) ∈ M.U a)
    (ha' : c (cPt p) ∈ M.U a') (hb : (q ≫ φ) (z₀ p) ∈ L.U b) (hb' : (q ≫ φ) (z₀ p) ∈ L.U b') :
    un p (gm (q ≫ φ) (z₀ p) _ (L.g b b')) * wv w q a b = wv w q a' b' := by
  have m : ∀ {a}, c (cPt p) ∈ M.U a → j (q (z₀ p)) ∈ M.U a := fun {a} ha => by
    show (q ≫ j) _ ∈ M.U a
    rw [h]
    exact gen_mem c ha
  rw [wv, wg_trans hw q _ (m ha) (m ha') hb hb', map_mul, map_mul, map_inv, h,
    un_integral c (U := M.U a ⊓ M.U a') ⟨ha, ha'⟩, _root_.one_mul, mul_inv_cancel_left₀ (un_pos _).ne']
  rfl

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
  [Algebra V K] [IsFractionRing V K]

theorem wv_eq_of_extends (hM : M.IsLB) (hL : L.IsLB) {w : LB.Iso (L.pull φ) (M.pull j)} (hw : w.IsGen)
    {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f] {fK : HK ⟶ Sp K}
    (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H) (he : e ≫ f = 𝟙 _) (ψ : H ⟶ A)
    (hψ : j ≫ ψ = φ) {c c' : Sp (OO p) ⟶ H} {q q' : Sp (PadicAlgCl p) ⟶ HK} (hc : q ≫ j = gPt p ≫ c)
    (hc' : q' ≫ j = gPt p ≫ c') (h : c ≫ f = c' ≫ f) {a a' : M.ι} {b b' : L.ι} (ha : c (cPt p) ∈ M.U a)
    (ha' : c' (cPt p) ∈ M.U a') (hb : (c ≫ ψ) (cPt p) ∈ L.U b) (hb' : (c' ≫ ψ) (cPt p) ∈ L.U b') :
    wv w q a b = wv w q' a' b' := by
  subst hψ
  have m : ∀ {c : Sp (OO p) ⟶ H} {q : Sp (PadicAlgCl p) ⟶ HK}, q ≫ j = gPt p ≫ c → ∀ {a b},
      c (cPt p) ∈ M.U a → (c ≫ ψ) (cPt p) ∈ L.U b →
      q (z₀ p) ∈ (M.pull j).U (fun _ => a) ⊓ (L.pull (j ≫ ψ)).U (fun _ => b) := fun {c q} hc {a b} ha hb => by
    have : (q ≫ j) (z₀ p) ∈ M.U a ⊓ ψ ⁻¹ᵁ L.U b := by
      rw [hc]
      exact gen_mem c ⟨ha, hb⟩
    exact ⟨mem_pull.2 this.1, mem_pull.2 this.2⟩
  refine un_eq_of_fine_charts hK e he (α := M.ι × L.ι) (κ := PUnit) (fun s => M.U s.1 ⊓ ψ ⁻¹ᵁ L.U s.2)
    (fun s t => res (inf_le_inf inf_le_left inf_le_left) (M.g s.1 t.1) *
      (res (inf_le_inf inf_le_right inf_le_right : _ ≤ ψ ⁻¹ᵁ L.U s.2 ⊓ ψ ⁻¹ᵁ L.U t.2)
        (pullU ψ (L.U s.2 ⊓ L.U t.2) (L.g s.2 t.2)))⁻¹)
    (fun s _ => (M.pull j).U (fun _ => s.1) ⊓ (L.pull (j ≫ ψ)).U (fun _ => s.2))
    (fun s _ => w.s (fun _ => s.1, fun _ => s.2)) (fun x => ?_) (fun s x => ?_) (fun s _ t _ x hs ht => ?_)
    hc hc' h (a := (a, b)) (a' := (a', b')) (b := ⟨⟩) (b' := ⟨⟩) ⟨ha, hb⟩ ⟨ha', hb'⟩ (m hc ha hb) (m hc' ha' hb')
  · obtain ⟨a, ha⟩ := exists_chart hM x
    obtain ⟨b, hb⟩ := exists_chart hL (ψ x)
    exact ⟨(a, b), ha, hb⟩
  · exact ⟨fun h => ⟨⟨⟩, mem_pull.2 h.1, mem_pull.2 h.2⟩, fun ⟨_, h⟩ => ⟨mem_pull.1 h.1, mem_pull.1 h.2⟩⟩
  · have hm : j x ∈ M.U s.1 ⊓ ψ ⁻¹ᵁ L.U s.2 ⊓ (M.U t.1 ⊓ ψ ⁻¹ᵁ L.U t.2) :=
      ⟨⟨mem_pull.1 hs.1, mem_pull.1 hs.2⟩, mem_pull.1 ht.1, mem_pull.1 ht.2⟩
    refine (wg_trans hw (𝟙 HK) x hm.1.1 hm.2.1 hm.1.2 hm.2.2).trans (congrArg (· * _) ?_)
    rw [Category.id_comp, Category.id_comp]
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res j x _ hm _) ((map_inv _ _).trans (congrArg (·⁻¹)
      ((gm_res j x _ hm _).trans (gm_pull j ψ x (L.U s.2 ⊓ L.U t.2) ⟨hm.1.2, hm.2.2⟩ _)))))).symm

theorem gen_wv_eq (hM : M.IsLB) (hL : L.IsLB) {w : LB.Iso (L.pull φ) (M.pull j)} (hw : w.IsGen)
    {Y YK B : Scheme.{0}} {f : Y ⟶ Sp V} [Smooth f] [GeometricallyIntegral f] {i : YK ⟶ Y} {fK : YK ⟶ Sp K}
    (hK : IsPullback i fK f (spMap (algebraMap V K))) (e : Sp V ⟶ Y) (he : e ≫ f = 𝟙 _)
    {I : Type} [Fintype I] (α : I → (Y ⟶ H)) (ψ : I → (YK ⟶ HK)) (β : I → (B ⟶ A)) (Φ : YK ⟶ B)
    (h₁ : ∀ k, ψ k ≫ j = i ≫ α k) (h₂ : ∀ k, ψ k ≫ φ = Φ ≫ β k) {ε : I → ℤ} {t : LB.Gen (LB.LinComb L β ε)}
    (ht : t.IsGen) {c c' : Sp (OO p) ⟶ Y} {q q' : Sp (PadicAlgCl p) ⟶ YK} (hc : q ≫ i = gPt p ≫ c)
    (hc' : q' ≫ i = gPt p ≫ c') (h : c ≫ f = c' ≫ f) {a a' : I → M.ι} {b b' : I → L.ι}
    (ha : ∀ k, (c ≫ α k) (cPt p) ∈ M.U (a k)) (ha' : ∀ k, (c' ≫ α k) (cPt p) ∈ M.U (a' k))
    (hb : ∀ k, ((q ≫ Φ) ≫ β k) (z₀ p) ∈ L.U (b k)) (hb' : ∀ k, ((q' ≫ Φ) ≫ β k) (z₀ p) ∈ L.U (b' k)) :
    un p (gm (q ≫ Φ) (z₀ p) (LB.wchart L β b) (t.s b)) * ∏ k, wv w (q ≫ ψ k) (a k) (b k) ^ ε k =
      un p (gm (q' ≫ Φ) (z₀ p) (LB.wchart L β b') (t.s b')) * ∏ k, wv w (q' ≫ ψ k) (a' k) (b' k) ^ ε k := by
  let D := LB.div (M.pull j) (L.pull φ)
  let s : (I → M.ι) → (I → L.ι) → I → D.ι := fun a b k => (fun _ => a k, fun _ => b k)
  have p₁ : ∀ k x, j (ψ k x) = α k (i x) := fun k x => congrArg (fun g => g x) (h₁ k)
  have p₂ : ∀ k x, φ (ψ k x) = β k (Φ x) := fun k x => congrArg (fun g => g x) (h₂ k)
  have mem : ∀ a b x, x ∈ LB.wchart D ψ (s a b) ↔
      (∀ k, α k (i x) ∈ M.U (a k)) ∧ ∀ k, β k (Φ x) ∈ L.U (b k) := fun a b x => by
    refine Set.mem_iInter.trans (Iff.trans (forall_congr' fun k => ?_) forall_and)
    rw [← p₁, ← p₂]
    exact and_congr mem_pull mem_pull
  have le : ∀ a b, LB.wchart D ψ (s a b) ≤ Φ ⁻¹ᵁ LB.wchart L β b := fun a b x hx =>
    Set.mem_iInter.2 ((mem a b x).1 hx).2
  let r : ∀ a b, Γ(YK, LB.wchart D ψ (s a b))ˣ := fun a b => res (le a b) (pullU Φ _ (t.s b)) *
    ∏ k, res (LB.wchart_le D ψ (s a b) k) (pullU (ψ k) _ (w.s (s a b k))) ^ ε k
  have v : ∀ (Z : Scheme.{0}) (u : Z ⟶ YK) (z : Z) a b, u z ∈ LB.wchart D ψ (s a b) →
      gm u z _ (r a b) = gm (u ≫ Φ) z (LB.wchart L β b) (t.s b) * ∏ k, wg w (u ≫ ψ k) z (a k) (b k) ^ ε k :=
    fun Z u z a b hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res u z _ hz _).trans (gm_pull u Φ z _ (le a b hz) _))
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
        ((gm_res u z _ hz _).trans (gm_pull u (ψ k) z _ (LB.wchart_le D ψ (s a b) k hz) _))))))
  have m : ∀ {c : Sp (OO p) ⟶ Y} {q : Sp (PadicAlgCl p) ⟶ YK}, q ≫ i = gPt p ≫ c → ∀ {a b},
      (∀ k, (c ≫ α k) (cPt p) ∈ M.U (a k)) → (∀ k, ((q ≫ Φ) ≫ β k) (z₀ p) ∈ L.U (b k)) →
      q (z₀ p) ∈ LB.wchart D ψ (s a b) := fun {c q} hc {a b} ha hb => (mem a b _).2 ⟨fun k => by
    show ((q ≫ i) ≫ α k) _ ∈ M.U (a k)
    rw [hc, Category.assoc]
    exact gen_mem _ (ha k), hb⟩
  have key := un_eq_of_fine_charts hK e he (LB.wchart M α) (LB.LinComb M α ε).g (fun a b => LB.wchart D ψ (s a b)) r
    (fun x => by
      choose a ha using fun k => exists_chart hM (α k x)
      exact ⟨a, Set.mem_iInter.2 ha⟩)
    (fun a x => by
      choose b hb using fun k => exists_chart hL (β k (Φ x))
      exact ⟨fun h => ⟨b, (mem a b x).2 ⟨Set.mem_iInter.1 h, hb⟩⟩,
        fun ⟨b, h⟩ => Set.mem_iInter.2 ((mem a b x).1 h).1⟩)
    (fun a b a' b' x hx hx' => by
      obtain ⟨m₁, m₂⟩ := (mem a b x).1 hx
      obtain ⟨m₁', m₂'⟩ := (mem a' b' x).1 hx'
      rw [v _ (𝟙 YK) x a b hx, v _ (𝟙 YK) x a' b' hx', Category.id_comp,
        gen_trans ht Φ x (Set.mem_iInter.2 m₂) (Set.mem_iInter.2 m₂')]
      erw [gm_linComb M α ε i x a a' (Set.mem_iInter.2 m₁) (Set.mem_iInter.2 m₁')]
      rw [trF, mul_left_comm, _root_.mul_assoc, mul_left_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine congrArg (_ * ·) (Finset.prod_congr rfl fun k _ => ?_)
      rw [← mul_zpow, ← mul_zpow, Category.id_comp, wg_trans hw (ψ k) x (a := a k) (a' := a' k) (b := b k) (b' := b' k)
        (by rw [p₁]; exact m₁ k) (by rw [p₁]; exact m₁' k) (by rw [p₂]; exact m₂ k) (by rw [p₂]; exact m₂' k),
        h₁, h₂, _root_.mul_assoc, mul_left_comm, mul_inv_cancel_left])
    hc hc' h (Set.mem_iInter.2 ha) (Set.mem_iInter.2 ha') (m hc ha hb) (m hc' ha' hb')
  rw [v _ _ _ _ _ (m hc ha hb), v _ _ _ _ _ (m hc' ha' hb')] at key
  simpa only [map_mul, map_prod, map_zpow, wv] using key

end Bundle

theorem ext_gPt {X S : Scheme.{0}} (s : X ⟶ S) [IsSeparated s] {b b' : Sp (OO p) ⟶ X} (h : b ≫ s = b' ≫ s)
    (h' : gPt p ≫ b = gPt p ≫ b') : b = b' := by
  have := InvExt.isDominant_gPt p
  exact ext_of_isDominant_of_isSeparated s h (gPt p) h'

theorem isPullback_cube {S U : Scheme.{0}} {j : U ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {A : Over U} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left} (gp : IsGrpPullback A G j F) :
    IsPullback (cubeMapOf gp).F3 (G3 A).hom (G3 G).hom j := by
  have hp := gp.1
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 A i).left ≫ F := cubeMap_comp_proj_three (cubeMapOf gp)
  have w : (cubeMapOf gp).F3 ≫ (G3 G).hom = (G3 A).hom ≫ j :=
    Over.w (lift (pushPt hp.w (x3 A 0)) (lift (pushPt hp.w (x3 A 1)) (pushPt hp.w (x3 A 2))))
  have ex : ∀ s : PullbackCone (G3 G).hom j, ∃ l : s.pt ⟶ (G3 A).left,
      l ≫ (cubeMapOf gp).F3 = s.fst ∧ l ≫ (G3 A).hom = s.snd := by
    intro s
    let P : Over U := Over.mk s.snd
    let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x3 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ F = s.fst ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G3 A := lift (x 0) (lift (x 1) (x 2))
    have lx : ∀ i, l ≫ x3 A i = x i := fun i => by fin_cases i <;> simp [l, x3]
    refine ⟨l.left, hom_ext_triple _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f3, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => hom_ext_triple _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f3, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem sum_thε : ∑ I : thK.{0}, thε I = 0 := by decide

theorem prod_thε {t : ℝ} (ht : 0 < t) : ∏ I : thK.{0}, t ^ thε I = 1 := by
  have : ∀ s : Finset thK.{0}, ∏ I ∈ s, t ^ thε I = t ^ ∑ I ∈ s, thε I := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ ht.ne']
  rw [this, sum_thε, zpow_zero]

section Test

variable {C : Core} {T : C.Theta} {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)

theorem base_ext {y y' : Sp (OO p) ⟶ C.Z} (h : gPt p ≫ y = gPt p ≫ y') : y = y' :=
  have := C.sep
  ext_gPt C.π (specZIsTerminal.hom_ext _ _) h

abbrev jg : pullback τ.H.hom (Out.jK τ.V) ⟶ τ.H.left := pullback.fst τ.H.hom (Out.jK τ.V)

def IsLift (c : Sp (OO p) ⟶ τ.H.left) (q : Sp (PadicAlgCl p) ⟶ pullback τ.H.hom (Out.jK τ.V)) : Prop :=
  c ≫ τ.H.hom = spMap τ.j ∧ q ≫ jg τ = gPt p ≫ c

theorem exists_frac : ∃ r, gPt p ≫ spMap τ.j = r ≫ Out.jK τ.V := by
  obtain ⟨r, hr⟩ := spMap_factor_jK ((OO p).subtype.comp τ.j) (Subtype.val_injective.comp τ.j_inj)
  exact ⟨r, (Spec.map_comp _ _).symm.trans hr⟩

variable {τ} {c c' : Sp (OO p) ⟶ τ.H.left} {q q' : Sp (PadicAlgCl p) ⟶ pullback τ.H.hom (Out.jK τ.V)}

theorem IsLift.gen (h : IsLift τ c q) : (q ≫ τ.φ) ≫ C.a = gPt p ≫ c ≫ τ.f := by
  rw [Category.assoc, τ.φ_f, ← Category.assoc, h.2, Category.assoc]

theorem IsLift.over (h : IsLift τ c q) : (c ≫ τ.f) ≫ C.GG.hom = y := by
  rw [Category.assoc, τ.f_over, ← Category.assoc, h.1, τ.fac]

theorem IsLift.base (h : IsLift τ c q) : (q ≫ τ.φ) ≫ C.A.hom ≫ C.U.ι = gPt p ≫ y := by
  rw [← C.isPullback_a.w, ← Category.assoc, h.gen, Category.assoc, h.over]

theorem IsLift.centre (h : IsLift τ c q) : τ.H.hom (c (cPt p)) = IsLocalRing.closedPoint τ.V := by
  have := τ.j_loc
  exact (congrArg (fun g => g (cPt p)) h.1).trans (IsLocalRing.comap_closedPoint τ.j)

theorem IsLift.unique (hp : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) (h : IsLift τ c q) (h' : IsLift τ c' q')
    (e : q ≫ τ.φ = q' ≫ τ.φ) : c = c' ∧ q = q' := by
  have := τ.sep
  have := DvrModel.isOpenImmersion_generic (IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V))
  have e₁ : c = c' := ext_gPt τ.H.hom (h.1.trans h'.1.symm) (hp.hom_ext
    (by rw [Category.assoc, Category.assoc, ← h.gen, ← h'.gen, e])
    (by rw [Category.assoc, Category.assoc, h.1, h'.1]))
  exact ⟨e₁, (cancel_mono (jg τ)).1 (by rw [h.2, h'.2, e₁])⟩

variable (τ) in
theorem exists_lift {b : Sp (OO p) ⟶ C.G.toScheme} {x : Sp (PadicAlgCl p) ⟶ C.A.left} (hb : b ≫ C.GG.hom = y)
    (hx : gPt p ≫ b = x ≫ C.a) : ∃ c q, IsLift τ c q ∧ c ≫ τ.f = b ∧ q ≫ τ.φ = x := by
  have := C.isOpenImmersion_a
  obtain ⟨c, h₁, h₂⟩ := τ.lift b hb
  obtain ⟨r, hr⟩ := exists_frac τ
  have h : IsLift τ c (pullback.lift (gPt p ≫ c) r (by rw [Category.assoc, h₁, hr])) :=
    ⟨h₁, pullback.lift_fst _ _ _⟩
  exact ⟨c, _, h, h₂, (cancel_mono C.a).1 (by rw [h.gen, h₂, hx])⟩

variable (E : T.Ext τ)

theorem IsLift.theta (h : IsLift τ c q) {a : E.L.L.ι} {b : T.L.L.ι} (ha : c (cPt p) ∈ E.L.L.U a)
    (hb : (q ≫ τ.φ) (z₀ p) ∈ T.L.L.U b) :
    ‖valF (q ≫ τ.φ) _ (T.θ.f b)‖ * wv E.w q a b ≤ 1 ∧
      (‖valF (q ≫ τ.φ) _ (T.θ.f b)‖ * wv E.w q a b = 1 ↔ c (cPt p) ∈ Out.nonzeroLocus E.θ) := by
  have ha' : jg τ (q (z₀ p)) ∈ E.L.L.U a := by
    show (q ≫ jg τ) _ ∈ _
    rw [h.2]
    exact gen_mem c ha
  have hm : q (z₀ p) ∈ (E.L.L.pull (jg τ)).U (fun _ => a) ⊓ (T.L.L.pull τ.φ).U (fun _ => b) :=
    ⟨mem_pull.2 ha', mem_pull.2 hb⟩
  have e := congrArg (q.stalkMap (z₀ p)).hom (E.θ_eq _ a b ha' hb)
  rw [map_mul, ← gs_comp q _ _ _ ha', ← gs_comp q _ _ _ hb, h.2] at e
  have e₁ := (gs_stalkMap q (z₀ p) _ hm (E.w.s (fun _ => a, fun _ => b)).val).symm.trans (gs_unit q _ _ hm _)
  have e₂ : ‖valF (q ≫ τ.φ) _ (T.θ.f b)‖ * wv E.w q a b = sn p (gs (gPt p ≫ c) (z₀ p) _ (E.θ.f a)) := by
    rw [e, map_mul, ← sn_gs _ hb, _root_.mul_comm]
    exact congrArg (· * _) (congrArg (sn p) e₁).symm
  rw [e₂, mem_nonzeroLocus_iff E.θ c _ ha, isUnit_gs_iff c _ _ ha]
  exact sn_integral c ha _

def IsRigNorm (ρ : ℝ) : Prop :=
  ∀ c q (u : Sp (PadicAlgCl p) ⟶ C.U.toScheme) (a : E.L.L.ι) (b : T.L.L.ι), IsLift τ c q →
    q ≫ τ.φ = u ≫ eSec C.A → c (cPt p) ∈ E.L.L.U a → (q ≫ τ.φ) (z₀ p) ∈ T.L.L.U b →
    un p (gm u (z₀ p) (LB.wchart T.L.L (fun _ : PUnit => eSec C.A) fun _ => b) (T.L.rig.s fun _ => b)) *
      wv E.w q a b = ρ

theorem exists_isRigNorm (hp : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) : ∃ ρ, 0 < ρ ∧ IsRigNorm E ρ := by
  by_cases h : ∃ c q, ∃ (u : Sp (PadicAlgCl p) ⟶ C.U.toScheme) (a : E.L.L.ι) (b : T.L.L.ι), IsLift τ c q ∧
    q ≫ τ.φ = u ≫ eSec C.A ∧ c (cPt p) ∈ E.L.L.U a ∧ (q ≫ τ.φ) (z₀ p) ∈ T.L.L.U b
  swap
  · exact ⟨1, one_pos, fun c q u a b h₁ h₂ h₃ h₄ => absurd ⟨c, q, u, a, b, h₁, h₂, h₃, h₄⟩ h⟩
  obtain ⟨c', q', u', a', b', k₁, k₂, k₃, k₄⟩ := h
  refine ⟨_, mul_pos (un_pos (gm u' (z₀ p) (LB.wchart T.L.L (fun _ : PUnit => eSec C.A) fun _ => b')
    (T.L.rig.s fun _ => b'))) (wv_pos E.w q' a' b'), fun c q u a b h₁ h₂ h₃ h₄ => ?_⟩
  have he : eSec C.A ≫ C.A.hom = 𝟙 _ := Over.w η[C.A]
  have base : ∀ {c q} {u : Sp (PadicAlgCl p) ⟶ C.U.toScheme}, IsLift τ c q → q ≫ τ.φ = u ≫ eSec C.A →
      u ≫ C.U.ι = gPt p ≫ y := fun {c q u} h₁ h₂ => by
    rw [← h₁.base, h₂, Category.assoc]
    exact congrArg (u ≫ ·) ((Category.id_comp _).symm.trans ((congrArg (· ≫ C.U.ι) he.symm).trans
      (Category.assoc _ _ _)))
  obtain rfl : u = u' := (cancel_mono C.U.ι).1 ((base h₁ h₂).trans (base k₁ k₂).symm)
  obtain ⟨rfl, rfl⟩ := h₁.unique hp k₁ (h₂.trans k₂.symm)
  have m : ∀ {b}, (q ≫ τ.φ) (z₀ p) ∈ T.L.L.U b →
      u (z₀ p) ∈ LB.wchart T.L.L (fun _ : PUnit => eSec C.A) fun _ => b := fun {b} hb =>
    Set.mem_iInter.2 fun _ => by rw [h₂] at hb; exact hb
  rw [gen_trans T.L.rigGen u _ (m h₄) (m k₄), trF, Fintype.prod_unique, zpow_one, map_mul, ← h₂,
    ← wv_trans E.w_gen h₁.2 h₃ k₃ h₄ k₄]
  ring

variable {E}

theorem IsRigNorm.integral {ρ : ℝ} (hρ : IsRigNorm E ρ) {s : Sp (OO p) ⟶ C.A.left} (h : IsLift τ c q)
    (hs : c ≫ τ.f = s ≫ C.a) {a : E.L.L.ι} {b : T.L.L.ι} (ha : c (cPt p) ∈ E.L.L.U a)
    (hb : s (cPt p) ∈ T.L.L.U b) : wv E.w q a b = ρ := by
  have := C.isOpenImmersion_a
  have hG := τ.isSemiAbelian
  have := hG.smooth
  have := geometricallyIntegral_of_isSemiAbelian τ.H
  have hy : (s ≫ C.A.hom) ≫ C.U.ι = y := by
    rw [Category.assoc, ← C.isPullback_a.w, ← Category.assoc, ← hs, h.over]
  obtain ⟨y₁, hy₁⟩ := exists_fac_of_closedPoint τ.y₀ C.U (by
    rw [← h.centre]
    show (c ≫ τ.H.hom ≫ τ.y₀) (cPt p) ∈ C.U
    rw [← Category.assoc, h.1, τ.fac, ← hy]
    exact ((s ≫ C.A.hom) (cPt p)).2)
  let ψ : τ.H.left ⟶ C.A.left := C.isPullback_a.lift τ.f (τ.H.hom ≫ y₁) (by rw [τ.f_over, Category.assoc, hy₁])
  have hψ : ψ ≫ C.a = τ.f := C.isPullback_a.lift_fst _ _ _
  have hφ : jg τ ≫ ψ = τ.φ := (cancel_mono C.a).1 (by rw [Category.assoc, hψ, τ.φ_f])
  have he : eSec C.A ≫ C.A.hom = 𝟙 _ := Over.w η[C.A]
  let s₀ : Sp (OO p) ⟶ C.A.left := (s ≫ C.A.hom) ≫ eSec C.A
  obtain ⟨c₀, q₀, k₁, k₂, k₃⟩ := exists_lift τ (b := s₀ ≫ C.a) (x := gPt p ≫ s₀) (by
    rw [Category.assoc, C.isPullback_a.w, ← hy, ← Category.assoc]
    exact congrArg (· ≫ C.U.ι) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) he).trans (Category.comp_id _))))
    (Category.assoc _ _ _).symm
  have e₁ : c ≫ ψ = s := (cancel_mono C.a).1 (by rw [Category.assoc, hψ, hs])
  have e₂ : c₀ ≫ ψ = s₀ := (cancel_mono C.a).1 (by rw [Category.assoc, hψ, k₂])
  obtain ⟨a₀, ha₀⟩ := exists_chart E.L.isLB (c₀ (cPt p))
  obtain ⟨b₀, hb₀⟩ := exists_chart T.L.isLB (s₀ (cPt p))
  have e₃ := hρ c₀ q₀ (gPt p ≫ s ≫ C.A.hom) a₀ b₀ k₁ (k₃.trans (Category.assoc _ _ _).symm) ha₀
    (by rw [k₃]; exact gen_mem s₀ hb₀)
  have e₄ := un_integral (s ≫ C.A.hom) (U := LB.wchart T.L.L (fun _ : PUnit => eSec C.A) fun _ => b₀)
    (Set.mem_iInter.2 fun _ => hb₀) (T.L.rig.s fun _ => b₀)
  rw [← ((_root_.one_mul _).symm.trans (congrArg (· * _) e₄.symm)).trans e₃]
  exact wv_eq_of_extends E.L.isLB T.L.isLB E.w_gen (IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V)) (eSec τ.H)
    (Over.w η[τ.H]) ψ hφ h.2 k₁.2 (h.1.trans k₁.1.symm) ha ha₀ (by rw [e₁]; exact hb) (by rw [e₂]; exact hb₀)

end Test

end GlobalTheory.ZJ.TestNorm
