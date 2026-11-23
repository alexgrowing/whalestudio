import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePsiW0
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPowDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransferThroughTensorIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataMumfordSideGeneratorValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensPsi

theorem tensorData_symmetric_pullback_and_psi_eq_tau : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (A₀ : Matrix (Fin r) (Fin r) ℤ) (O : Type) [CommRing O] [StarRing O] [Module O D'.toPre.X] (o : D'.toPre.OAct O) (w₀ : O), o.onB.act w₀ = GlobalTheory.TensAct.matAct T A₀ → (∀ y : D'.toPre.X, w₀ • y = GlobalTheory.TensAct.latAct T A₀ y) → W = (W + W.transpose) * A₀ → TraceFormTwistIso D'.toPre o w₀ := by
  intro R _ _ I D D' r W T A₀ O _ _ _ o w₀ hact hlat hW
  have := o.onB.hom w₀
  obtain ⟨t, ht, vt⟩ := GlobalTheory.T.tensorData_mumfordSide_generator_values R I D D'.toPre W T A₀ (o.onB.act w₀) hact hW
  obtain ⟨u₀, hu₀, vu₀⟩ := GlobalTheory.T.exists_generator_transfer_through_tensorIso R D.toPre D'.toPre W T
    (![(padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left, 𝟙 D'.toPre.P.A.left, (o.onB.act w₀).left,
      (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left] : Fin 4 → (D'.toPre.P.A.left ⟶ D'.toPre.P.A.left))
    ![1, -2, -1, 2] t ht
  obtain ⟨u, hu, hv⟩ := exists_gen D'.toPre.P.isLB
    (φ' := (![(padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left, 𝟙 D'.toPre.P.A.left, (o.onB.act w₀).left,
      (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left] : Fin 4 → _)) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ rfl
        (DVR.prod_neg _ _ (GlobalTheory.PsiWZeroPull.prod_four (o.onB.act w₀) (1 : D'.toPre.P.A ⟶ D'.toPre.P.A) k))) ?_
      rw [MonObj.one_comp, _root_.mul_one (1 : D'.toPre.P.A ⟶ D'.toPre.P.A)]
      refine mul_eq_left.2 (inv_eq_one.2 ?_)
      group)
    (LB.mulGen D'.toPre.P.L _ _ _ _ u₀ (LB.invGen D'.toPre.P.L _ _ (LB.pullGen D'.toPre.P.L _ _ u₀ (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _)))
  refine ⟨u, hu, corr_of_val D'.toPre.P.isLB fun y J hJ => ?_, fun y => corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_⟩
  · have e : eSec D'.toPre.P.A ≫ (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left = eSec D'.toPre.P.A :=
      congrArg (fun q : 𝟙_ (Over _) ⟶ D'.toPre.P.A => q.left) ((MonObj.comp_one (M := D'.toPre.P.A) η[D'.toPre.P.A]).trans (by simp [Hom.one_def]))
    rw [val_pull hJ, val_one, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, e, mul_inv_cancel]

  · choose J hJ using fun ψ : (TK R).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
    let ω : ((TK R).left ⟶ D'.toPre.P.A.left) → ((TK R).left.presheaf.stalk z)ˣ := fun ψ =>
      gm ψ z _ (T.w.s (fun k => J (ψ ≫ tensφ T.pr k), J' ψ))
    let Tv : D'.toPre.X → ((TK R).left.presheaf.stalk z)ˣ := fun v =>
      ∏ i, ∏ j, val (D.toPre.tau (T.xe v i) (T.xe v j)) (𝟙 _) z J ^ W i j
    have hψ : ∀ v, val (D'.toPre.psi v) (𝟙 _) z J' = ω (D'.toPre.xK v) * Tv v := fun v => T.psi v z J J' hJ hJ'
    have k0 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left =
        D'.toPre.xK (x + w₀ • x) := by
      intro x
      show ((toUnit (TK R) ≫ D'.toPre.c x) ≫ padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left =
        (toUnit (TK R) ≫ D'.toPre.c (x + w₀ • x)).left
      congr 1
      rw [D'.toPre.c_add, o.c_lin]
      simp only [padd, ← Category.assoc, comp_lift, Category.comp_id]
    have k2 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (o.onB.act w₀).left = D'.toPre.xK (w₀ • x) := by
      intro x
      show ((toUnit (TK R) ≫ D'.toPre.c x) ≫ o.onB.act w₀).left = (toUnit (TK R) ≫ D'.toPre.c (w₀ • x)).left
      rw [o.c_lin, Category.assoc]
    have k3 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left = D'.toPre.xK 0 := by
      intro x
      have c0 : (toUnit (TK R) ≫ D'.toPre.c 0 : TK R ⟶ D'.toPre.P.A) = 1 := cPoint_zero (D := D'.toPre) (TK R)
      show ((toUnit (TK R) ≫ D'.toPre.c x) ≫ toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left = (toUnit (TK R) ≫ D'.toPre.c 0).left
      rw [c0, ← Category.assoc, toUnit_unique ((toUnit (TK R) ≫ D'.toPre.c x) ≫ toUnit D'.toPre.P.A) (toUnit (TK R))]
      simp [Hom.one_def]
    have k1 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left = D'.toPre.xK 0 := by
      intro x
      have := k3 x
      rwa [← Hom.one_def] at this
    have F : ∀ x : D'.toPre.X, val u₀ (D'.toPre.xK x) z J' = (val (D'.toPre.psi (x + w₀ • x)) (𝟙 _) z J')⁻¹ *
        val (D'.toPre.psi x) (𝟙 _) z J' ^ (2 : ℤ) * val (D'.toPre.psi (w₀ • x)) (𝟙 _) z J' *
        (val (D'.toPre.psi 0) (𝟙 _) z J') ^ (-2 : ℤ) := by
      intro x
      have e1 : ω (D'.toPre.xK (x + w₀ • x)) ^ (1 : ℤ) * ω (D'.toPre.xK x) ^ (-2 : ℤ) *
          ω (D'.toPre.xK (w₀ • x)) ^ (-1 : ℤ) * ω (D'.toPre.xK 0) ^ (2 : ℤ) * val u₀ (D'.toPre.xK x) z J' =
          val t (D'.toPre.xK x) z J := by
        have h₀ := vu₀ _ (D'.toPre.xK x) z J J' hJ hJ'
        have h₁ : (∏ a : Fin 4, ω (D'.toPre.xK x ≫ (![(padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left, 𝟙 D'.toPre.P.A.left,
            (o.onB.act w₀).left, (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left] : Fin 4 → (D'.toPre.P.A.left ⟶ D'.toPre.P.A.left)) a) ^
            (![1, -2, -1, 2] : Fin 4 → ℤ) a) * val u₀ (D'.toPre.xK x) z J' = val t (D'.toPre.xK x) z J := h₀
        rw [Fin.prod_univ_four] at h₁
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, neg_neg, Category.comp_id] at h₁
        rw [k0, k2, k3] at h₁
        exact h₁
      have e2 : val t (D'.toPre.xK x) z J = Tv (x + w₀ • x) ^ (-1 : ℤ) * Tv x ^ (2 : ℤ) * Tv (w₀ • x) ^ (1 : ℤ) *
          Tv 0 ^ (-2 : ℤ) := by
        have h₀ := vt x z J hJ
        rw [Fin.prod_univ_four] at h₀
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, neg_neg] at h₀
        simp only [Tv, hlat]
        exact h₀
      rw [hψ, hψ, hψ, hψ]
      rw [e2] at e1
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e1
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
      linear_combination (norm := abel) e'
    have hu_y : ∀ x, val u (D'.toPre.xK x) z J' = val u₀ (D'.toPre.xK x) z J' * (val u₀ (D'.toPre.xK 0) z J')⁻¹ := by
      intro x
      rw [hv _ _ z J' hJ', val_mul hJ', val_inv, val_pull hJ', k1]
    have tau_e : ∀ a b : D'.toPre.X, val (D'.toPre.tau a b) (𝟙 _) z J' = val (D'.toPre.psi (a + b)) (𝟙 _) z J' *
        (val (D'.toPre.psi a) (𝟙 _) z J')⁻¹ * (val (D'.toPre.psi b) (𝟙 _) z J')⁻¹ * (val D'.toPre.rigK (𝟙 _) z J')⁻¹ :=
      fun a b => (val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    have p0 := GlobalTheory.PsiInPow.val_psi_zero D'.toPre D'.tau_bimult hJ'
    have f0 := F 0
    rw [smul_zero, add_zero] at f0
    rw [val_mul hJ', val_mul hJ', val_pull hJ', Category.id_comp, hu_y, F y, f0, tau_e, p0]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel

end GlobalTheory.TensPsi
