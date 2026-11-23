import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.RigidLinearisation

theorem exists_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ c := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(res le (t.s PEmpty.elim)).val, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm

theorem gs_one {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) : gs f y ⊤ (1 : Γ(X, ⊤)) = 1 := by
  rw [gs_eq _ y ⊤ trivial, map_one, map_one]

theorem gs_pow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (c : Γ(X, ⊤)) (n : ℕ) : gs f y ⊤ (c ^ n) = gs f y ⊤ c ^ n := by
  rw [gs_eq _ y ⊤ trivial, gs_eq _ y ⊤ trivial, map_pow, map_pow]

theorem exists_good' {X Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (z : Z) : ∃ J, Good M z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hM (χ z)
  exact ⟨I, hI⟩

theorem val_eq_of_rigid {X Y S : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (e : S ⟶ Y) (he : ∀ c : Γ(Y, ⊤), (e.app ⊤).hom c = 1 → c = 1)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨c, hc⟩ := exists_ratio hM hF hu hu'
  have c1 : c = 1 := he c (fn_ext (V := ⊤) fun y _ => by
    obtain ⟨I, hI⟩ := exists_good' hM y
    have := hc _ e y I hI
    rw [h y I hI, mul_inv_cancel] at this
    refine (gs_pull (𝟙 S) e y ⊤ trivial c).trans ?_
    rw [Category.id_comp, ← this]
    exact (gs_one (𝟙 S) y).symm)
  have := hc Z r z J hJ
  rw [c1, gs_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

theorem exists_gen_of_iso {Y : Scheme.{0}} (L : LB Y) (τ : Y ⟶ Y) (h : LBIso L (L.pull τ)) :
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, τ] ![1, -1]), t.IsGen := by
  obtain ⟨w, hw⟩ := h
  have hp := (isGen_iff w).1 hw
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j ≤ (L.pull τ).U (fun _ => j 1) ⊓ L.U (j 0) :=
    fun j y hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy 1), Set.mem_iInter.1 hy 0⟩
  refine ⟨⟨fun j => (res (le j) (w.s (fun _ => j 1, j 0)))⁻¹⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  have v : ∀ j : Fin 2 → L.ι, y ∈ LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j →
      gm (𝟙 Y) y (LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j) (res (le j) (w.s (fun _ => j 1, j 0)))⁻¹ =
        (gw w (𝟙 Y) y (j 1) (j 0))⁻¹ := fun j hj =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res (𝟙 Y) y (le j) hj _))
  refine (v j hj).trans (Eq.trans ?_ (congrArg (_ * ·) (v j' hj')).symm)
  rw [hp Y (𝟙 Y) y (j 1) (j' 1) (j 0) (j' 0) (Set.mem_iInter.1 hj 1) (Set.mem_iInter.1 hj' 1)
    (Set.mem_iInter.1 hj 0) (Set.mem_iInter.1 hj' 0), trF, Fin.prod_univ_two]
  show _ = gm (𝟙 Y ≫ 𝟙 Y) y _ (L.g (j 0) (j' 0)) ^ (1 : ℤ) * gm (𝟙 Y ≫ τ) y _ (L.g (j 1) (j' 1)) ^ (-1 : ℤ) * _
  rw [Category.id_comp (𝟙 Y), zpow_one, zpow_neg_one, mul_inv, mul_inv, inv_inv, mul_comm (_⁻¹) (gm (𝟙 Y) y _ _)]

theorem exists_normalised {X Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (p : Y ⟶ X) (e : X ⟶ Y) (he : e ≫ p = 𝟙 X)
    (ρ : X ⟶ X) (τ : Y ⟶ Y) (hτ : e ≫ τ = ρ ≫ e) (r : (L.pull e).Gen) (hr : r.IsGen) (h : LBIso L (L.pull τ)) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, τ] ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (b : Z ⟶ X) (z : Z) (J), Good L z J →
        val u (b ≫ e) z J = val r b z J * (val r (b ≫ ρ) z J)⁻¹ := by
  obtain ⟨t, ht⟩ := exists_gen_of_iso L τ h
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := ![𝟙 Y, τ]) (ε' := ![1, -1]) (fun U _ k => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fintype.prod_unique,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.assoc, hτ, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (p ≫ e))))
      (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ r p) (LB.invGen L _ _ (LB.pullGen L _ _ r (p ≫ ρ)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _)
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _))))
  refine ⟨u, hu, fun Z b z J hJ => ?_⟩
  have e₁ : (b ≫ e) ≫ p = b := by rw [Category.assoc, he, Category.comp_id]
  rw [hv Z _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_pull hJ, val_pull hJ,
    ← Category.assoc (b ≫ e) p e, ← Category.assoc (b ≫ e) p ρ, e₁, mul_inv_cancel, _root_.one_mul]

theorem exists_const {k : Type} [Field k] [IsAlgClosed k] {F : Scheme.{0}} [IsIntegral F] (q : F ⟶ Sp k)
    (c : Γ(F, ⊤)) {n : ℕ} (hn : n ≠ 0) (hc : c ^ n = 1) : ∃ a : Γ(Sp k, ⊤), (q.app ⊤).hom a = c := by
  let f : k →+* Γ(F, ⊤) := (q.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hs : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial k).Splits := IsAlgClosed.splits _
  have hm : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial k).Monic := Polynomial.monic_X_pow_sub_C _ hn
  have e := congrArg (Polynomial.eval₂ f c) (hs.eq_prod_roots_of_monic hm)
  rw [Polynomial.eval₂_multiset_prod, Multiset.map_map] at e
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_one, hc, sub_self,
    Polynomial.eval₂_one] at e
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 e.symm)
  simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at ha
  exact ⟨_, (sub_eq_zero.1 ha).symm⟩

theorem exists_linearisation : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X : Scheme.{0}) (P : Over X) (e : X ⟶ P.left) (ρ : Γ →* Aut X) (τ : Γ →* Aut P.left) (L : LB P.left), e ≫ P.hom = 𝟙 X → GeometricallyIntegral P.hom → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → (∀ g, (τ g).hom ≫ P.hom = P.hom ≫ (ρ g).hom ∧ e ≫ (τ g).hom = (ρ g).hom ≫ e) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst P.hom x ≫ (τ g).hom = pullback.fst P.hom x) → L.IsLB → (∃ r : (L.pull e).Gen, r.IsGen) → (∀ g, LBIso L (L.pull (τ g).hom)) → ∃ u : ∀ g, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 P.left, (τ g).hom] ![1, -1]), (∀ g, (u g).IsGen) ∧ (∀ g h, LB.Gen.Corr L _ _ _ _ (u (h * g)) (LB.mulGen L _ _ _ _ (u g) (LB.pullGen L _ _ (u h) (τ g).hom))) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ P.left) g, y ≫ (τ g).hom = y → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u g) y) (LB.oneGen L) := by
  intro Γ _ _ X P e ρ τ L he hgi hrig hcomm hfix hL ⟨r, hr⟩ hiso
  choose u hu hn using fun g => exists_normalised hL P.hom e he (ρ g).hom (τ g).hom (hcomm g).2 r hr (hiso g)
  have rig : ∀ c : Γ(P.left, ⊤), (e.app ⊤).hom c = 1 → c = 1 := fun c hc =>
    hrig ⊤ c le_top (by
      have : e.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ le_top = e.app ⊤ := (e.app_eq_appLE (U := ⊤)).symm
      rw [this]; exact hc)
  have τm : ∀ g h, (τ (h * g)).hom = (τ g).hom ≫ (τ h).hom := fun g h => by rw [map_mul]; rfl
  have ρm : ∀ g h, (ρ (h * g)).hom = (ρ g).hom ≫ (ρ h).hom := fun g h => by rw [map_mul]; rfl
  have coc : ∀ g h (Z : Scheme.{0}) (s : Z ⟶ P.left) (z : Z) (J), Good L z J → val (u (h * g)) s z J =
      val (LB.mulGen L _ _ _ _ (u g) (LB.pullGen L _ _ (u h) (τ g).hom)) s z J := fun g h =>
    val_eq_of_rigid hL (fun U _ k => by
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, τm, Category.comp_id]
        simp) e rig (hu _)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hu g) (DVR.pullGen_isGen _ _ _ _ (hu h) _)) (fun y J hJ => by
        have a₁ := hn (h * g) X (𝟙 X) y J hJ
        have a₂ := hn g X (𝟙 X) y J hJ
        have a₃ := hn h X (ρ g).hom y J hJ
        simp only [Category.id_comp] at a₁ a₂
        rw [val_mul hJ, val_pull hJ, (hcomm g).2, a₁, a₂, a₃, ρm]
        simp)
  refine ⟨u, hu, fun g h => corr_of_val hL fun y J hJ => coc g h _ _ y J hJ, fun k _ _ y g hy => ?_⟩
  have hx : (y ≫ P.hom) ≫ (ρ g).hom = y ≫ P.hom := by
    rw [Category.assoc, ← (hcomm g).1, ← Category.assoc, hy]
  have hf := hfix k _ g hx
  have : IsIntegral (pullback P.hom (y ≫ P.hom)) :=
    hgi.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
  obtain ⟨c, hc⟩ := exists_ratio hL (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ k => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hf, Category.comp_id]
      simp)
    (DVR.pullGen_isGen _ _ _ _ (hu g) (pullback.fst P.hom (y ≫ P.hom))) (u' := LB.oneGen L)
    (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.one_mul _)).symm)
  have hc' : ∀ (Z : Scheme.{0}) (s : Z ⟶ pullback P.hom (y ≫ P.hom)) (z : Z) (J), Good L z J →
      (val (u g) (s ≫ pullback.fst _ _) z J).val = gs s z ⊤ c := fun Z s z J hJ => by
    rw [← hc Z s z J hJ, val_pull hJ, val_one, inv_one, _root_.mul_one]
  have pw : ∀ (Z : Scheme.{0}) (s : Z ⟶ P.left) (z : Z) (J), Good L z J → s ≫ (τ g).hom = s →
      val (u g) s z J ^ orderOf g = 1 := fun Z s z J hJ hs => by
    have one : val (u 1) s z J = 1 := by
      have := coc 1 1 Z s z J hJ
      rw [val_mul hJ, val_pull hJ, _root_.mul_one, show s ≫ (τ 1).hom = s by rw [map_one]; exact Category.comp_id s] at this
      exact mul_eq_left.1 this.symm
    have all : ∀ n : ℕ, val (u (g ^ n)) s z J = val (u g) s z J ^ n := fun n => by
      induction n with
      | zero => rw [pow_zero, pow_zero, one]
      | succ n ih => rw [pow_succ, coc g (g ^ n) Z s z J hJ, val_mul hJ, val_pull hJ, hs, ih, pow_succ']
    rw [← all, pow_orderOf_eq_one, one]
  have cn : c ^ orderOf g = 1 := fn_ext fun z _ => by
    obtain ⟨J, hJ⟩ := exists_good' hL z
    rw [gs_pow, gs_one, ← hc' _ _ z J hJ, ← Units.val_pow_eq_pow_val,
      pw _ _ z J hJ (by rw [Category.assoc, hf]), Units.val_one]
  obtain ⟨a, ha⟩ := exists_const (pullback.snd P.hom (y ≫ P.hom)) c (orderOf_pos g).ne' cn
  have sec : ∀ (s : Sp k ⟶ pullback P.hom (y ≫ P.hom)) (z : Sp k), s ≫ pullback.snd _ _ = 𝟙 _ →
      gs s z ⊤ c = gs (𝟙 _) z ⊤ a := fun s z hs => by
    rw [← ha, ← hs]
    exact gs_pull s _ z ⊤ trivial a
  refine corr_of_val hL fun z J hJ => Units.ext ?_
  have b₁ := hc' _ (pullback.lift y (𝟙 _) (Category.id_comp _).symm) z J hJ
  have b₂ := hc' _ (pullback.lift ((y ≫ P.hom) ≫ e) (𝟙 _) (by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp])) z J hJ
  rw [sec _ z (pullback.lift_snd _ _ _), pullback.lift_fst] at b₁ b₂
  rw [hn g _ _ z J hJ, hx, mul_inv_cancel] at b₂
  rw [val_pull hJ, Category.id_comp, val_one, b₁, b₂]

end GlobalTheory.RigidLinearisation
