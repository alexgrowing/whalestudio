import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BiextSym

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_gen_of_iso {X : Scheme.{0}} {L : LB X} {F : X ⟶ X} (h : LBIso L (L.pull F)) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![F, 𝟙 X] ![1, -1]), s.IsGen := by
  obtain ⟨w, hw⟩ := h
  have hp := (isGen_iff w).1 hw
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![F, 𝟙 X] j ≤ (L.pull F).U (fun _ => j 0) ⊓ L.U (j 1) :=
    fun j x hx => ⟨mem_pull.2 (Set.mem_iInter.1 hx 0), Set.mem_iInter.1 hx 1⟩
  refine ⟨⟨fun j => res (le j) (w.s (fun _ => j 0, j 1))⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have a := hp _ (𝟙 X) y (j 0) (j' 0) (j 1) (j' 1) (mem_pull.1 (le j hy.1).1) (mem_pull.1 (le j' hy.2).1)
    (le j hy.1).2 (le j' hy.2).2
  refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 X) y (le j) hy.1 _)).trans (a.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 X) y j j' hy.1 hy.2).trans ?_)
    ((gm_res _ y _ hy _).trans (gm_res (𝟙 X) y (le j') hy.2 _)))
  rw [Fin.prod_univ_two]
  show gm (𝟙 X ≫ F) y _ (L.g (j 0) (j' 0)) ^ (1 : ℤ) * gm (𝟙 X ≫ 𝟙 X) y _ (L.g (j 1) (j' 1)) ^ (-1 : ℤ) = _
  rw [_root_.zpow_neg, _root_.zpow_one, _root_.zpow_one, Category.id_comp (𝟙 X)]

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

omit [GrpObj A] [IsCommMonObj A] in
theorem prod_sym {T : Over S} (x y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i : Fin 2, h ((lift x y).left ≫ ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] i) ^ (![1, -1] i : ℤ) =
      h (lift y x).left * (h (lift x y).left)⁻¹ := by
  have e : lift x y ≫ lift (snd A A) (fst A A) = lift y x := by rw [comp_lift, lift_fst, lift_snd]
  rw [Fin.prod_univ_two]
  show h (lift x y ≫ lift (snd A A) (fst A A)).left ^ (1 : ℤ) * h ((lift x y).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
  rw [e, Category.comp_id, _root_.zpow_neg, _root_.zpow_one, _root_.zpow_one]

theorem biextension_first_law_product {T : Over S} (x x' y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i, h ((lift x (lift x' y)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) i) ^ lawε i =
      h (lift (x * x') y).left * (h (lift x y).left)⁻¹ * (h (lift x' y).left)⁻¹ := by
  have a₀ : lift x (lift x' y) ≫ x3 A 0 = x := by simp [x3]
  have a₁ : lift x (lift x' y) ≫ x3 A 1 = x' := by simp [x3]
  have a₂ : lift x (lift x' y) ≫ x3 A 2 = y := by simp [x3]
  have b : lift x (lift x' y) ≫ padd A (x3 A 0) (x3 A 1) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift x' y)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift x' y) ≫ lift (padd A (x3 A 0) (x3 A 1)) (x3 A 2)).left ^ (1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 A 1) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]

theorem biextension_second_law_product {T : Over S} (x y y' : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i, h ((lift x (lift y y')).left ≫ law2φ A (x3 A 0) (x3 A 1) (x3 A 2) i) ^ lawε i =
      h (lift x (y * y')).left * (h (lift x y).left)⁻¹ * (h (lift x y').left)⁻¹ := by
  have a₀ : lift x (lift y y') ≫ x3 A 0 = x := by simp [x3]
  have a₁ : lift x (lift y y') ≫ x3 A 1 = y := by simp [x3]
  have a₂ : lift x (lift y y') ≫ x3 A 2 = y' := by simp [x3]
  have b : lift x (lift y y') ≫ padd A (x3 A 1) (x3 A 2) = y * y' := (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift y y')).left ≫ law2φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift y y') ≫ lift (x3 A 0) (padd A (x3 A 1) (x3 A 2))).left ^ (1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 A 0) (x3 A 1)).left ^ (-1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]

theorem exists_norm {P : LB (A ⊗ A).left} (hP : P.IsLB) (h : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) :
    ∃ s : LB.Gen (LB.LinComb P (K := Fin 2) ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] ![1, -1]), s.IsGen ∧
      ∀ (T : Over S) (z : T.left) (J), Good P z J → val s (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  obtain ⟨t, ht⟩ := exists_gen_of_iso h
  obtain ⟨s, hs, hv⟩ := exists_gen hP (K' := Fin 2) (φ' := ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left])
    (ε' := ![1, -1]) (fun V _ k => by
      have p := prod_sym (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A) k
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _
        (c := ∏ i : Fin 2, k (![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] i) ^ (![1, -1] i : ℤ)) rfl
        (DVR.prod_neg _ _ p)) ?_
      rw [mul_inv_cancel, inv_one, _root_.mul_one])
    (LB.mulGen P _ _ _ _ t (LB.invGen P _ _ (LB.pullGen P _ _ t (lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨s, hs, fun T z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, ← Over.comp_left, comp_lift, MonObj.comp_one, mul_inv_cancel]

theorem val_pull₂ {X : Scheme.{0}} {P : LB X} {K : Type} [Fintype K] {B C : Over S} {φ : K → ((B ⊗ C).left ⟶ X)}
    {ε : K → ℤ} (u : LB.Gen (LB.LinComb P φ ε)) {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good P z J)
    (a : T ⟶ B) (b : T ⟶ C) :
    val (LB.pullGen P φ ε u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]

theorem val_pull₃ {X : Scheme.{0}} {P : LB X} {K : Type} [Fintype K] {B C D : Over S}
    {φ : K → ((B ⊗ C ⊗ D).left ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb P φ ε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good P z J) (a : T ⟶ B) (b : T ⟶ C) (c : T ⟶ D) :
    val (LB.pullGen P φ ε u (lift a (lift b c)).left) ρ.left z J =
      val u (lift (ρ ≫ a) (lift (ρ ≫ b) (ρ ≫ c))).left z J := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift, comp_lift]

theorem law_origin {P : LB (A ⊗ A).left} (β : IsBiext A P) {T : Over S} {z : T.left} {J} (hJ : Good P z J) :
    val β.law1 (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A))).left z J =
      val β.law2 (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A))).left z J := by
  let ρ := lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A)))
  have a₀ : ρ ≫ x4 A 0 = 1 := by simp [ρ, x4]
  have a₁ : ρ ≫ x4 A 1 = 1 := by simp [ρ, x4]
  have a₂ : ρ ≫ x4 A 2 = 1 := by simp [ρ, x4]
  have a₃ : ρ ≫ x4 A 3 = 1 := by simp [ρ, x4]
  have b₀ : ρ ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁, _root_.mul_one])
  have b₁ : ρ ≫ padd A (x4 A 2) (x4 A 3) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₂, a₃, _root_.mul_one])
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    (val_pull₃ β.law1 ρ hJ _ _ _) (val_pull₃ β.law2 ρ hJ _ _ _))) (val_pull₃ β.law2 ρ hJ _ _ _))).symm.trans
    ((val_corr hJ β.compat ρ.left).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull₃ β.law2 ρ hJ _ _ _) (val_pull₃ β.law1 ρ hJ _ _ _))) (val_pull₃ β.law1 ρ hJ _ _ _))))
  rw [b₀, b₁, a₀, a₁, a₂, a₃, mul_comm (val β.law2 _ z J) (val β.law1 _ z J)] at e
  exact (mul_left_cancel e).symm

theorem main :
  (ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme A →
    ∀ (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (A ⊗ A).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext A P),
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∃ s : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := Fin 2) ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] ![1, -1]), s.IsGen ∧ ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ (A ⊗ A).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ x x' y : T ⟶ A,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift y x).left z J = 1 ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift (x * x') y).left z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x' y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift y (lift x x')).left z J) := by
  intro hG S A _ _ hA P β hs
  obtain ⟨s, hs, h1⟩ := exists_norm β.isLB hs
  refine ⟨s, hs, fun T z J hJ x x' y => ⟨?_, ?_⟩⟩
  · have ev : ∀ {T' : Over S} (σ : T' ⟶ A ⊗ A) {z : T'.left} {J}, Good P z J →
        val (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ s (lift (fst A A) (snd A A)).left)
          (LB.pullGen P _ _ s (lift (snd A A) (fst A A)).left)) σ.left z J =
          val s (lift (σ ≫ fst A A) (σ ≫ snd A A)).left z J * val s (lift (σ ≫ snd A A) (σ ≫ fst A A)).left z J :=
      fun σ z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ s σ hJ _ _) (val_pull₂ s σ hJ _ _))
    let e : 𝟙_ (Over S) ⟶ A ⊗ A := lift 1 1
    have sj : Function.Surjective ((snd A A).left ≫ A.hom).appTop.hom := surj_comp (surj_snd hG hA _) (hG _ _ hA).2
    have he : e.left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by rw [Over.w]; exact Over.w e
    have key := gen_unique' β.isLB (u' := LB.oneGen P (Y := (A ⊗ A).left)) (fun V _ k => by
        refine (Fintype.prod_empty _).trans (Eq.symm ?_)
        refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym (fst A A) (snd A A) k)
          (prod_sym (snd A A) (fst A A) k)).trans ?_
        rw [_root_.mul_assoc, inv_mul_cancel_left, mul_inv_cancel]) _ e.left he sj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hs _) (DVR.pullGen_isGen _ _ _ _ hs _))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
      (fun y I hI => by
        refine (ev e hI).trans (Eq.trans ?_ (val_one _).symm)
        rw [lift_fst, lift_snd, h1 _ y I hI, _root_.mul_one]) _ (lift x y).left z J hJ
    have := (ev (lift x y) hJ).symm.trans (key.trans (val_one _))
    rwa [lift_fst, lift_snd] at this
  · let p₀ := x3 A 0
    let p₁ := x3 A 1
    let p₂ := x3 A 2
    have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 A) {z : T'.left} {J}, Good P z J →
        val (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ β.law1 (lift p₀ (lift p₁ p₂)).left)
          (LB.pullGen P _ _ s (lift (p₀ * p₁) p₂).left)) σ.left z J =
          val β.law1 (lift (σ ≫ p₀) (lift (σ ≫ p₁) (σ ≫ p₂))).left z J * val s (lift (σ ≫ (p₀ * p₁)) (σ ≫ p₂)).left z J ∧
        val (LB.mulGen P _ _ _ _ (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ s (lift p₀ p₂).left)
          (LB.pullGen P _ _ s (lift p₁ p₂).left)) (LB.pullGen P _ _ β.law2 (lift p₂ (lift p₀ p₁)).left)) σ.left z J =
          val s (lift (σ ≫ p₀) (σ ≫ p₂)).left z J * val s (lift (σ ≫ p₁) (σ ≫ p₂)).left z J *
            val β.law2 (lift (σ ≫ p₂) (lift (σ ≫ p₀) (σ ≫ p₁))).left z J := fun σ z J hJ =>
      ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₃ β.law1 σ hJ _ _ _) (val_pull₂ s σ hJ _ _)),
        (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (val_pull₂ s σ hJ _ _) (val_pull₂ s σ hJ _ _))) (val_pull₃ β.law2 σ hJ _ _ _))⟩
    let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
    have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
    have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
    have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
    have sj : Function.Surjective ((snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom).appTop.hom :=
      surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
    have he : e.left ≫ (snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
      rw [Over.w, Over.w]; exact Over.w e
    let ρ : T ⟶ G3 A := lift x (lift x' y)
    have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
    have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
    have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
    have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
    have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
    have := (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' β.isLB (fun V _ k => by
        refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := ULift.{0} (Fin 3)) (U := V) _
          (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym p₀ p₂ k) (prod_sym p₁ p₂ k))
          (biextension_second_law_product p₂ p₀ p₁ k)).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := ULift.{0} (Fin 3)) (K' := Fin 2) (U := V) _
            (biextension_first_law_product p₀ p₁ p₂ k) (prod_sym (p₀ * p₁) p₂ k)).symm)
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) _ e.left he sj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen1 _) (DVR.pullGen_isGen _ _ _ _ hs _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ hs _) (DVR.pullGen_isGen _ _ _ _ hs _)) (DVR.pullGen_isGen _ _ _ _ β.isGen2 _))
      (fun y I hI => by
        refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
        rw [o₁, e₀, e₁, e₂, h1 _ y I hI, law_origin β hI, _root_.mul_one, _root_.one_mul, _root_.one_mul])
      _ ρ.left z J hJ) (ev ρ hJ).2)
    rwa [s₁, r₀, r₁, r₂] at this

end GlobalTheory.BiextSym
