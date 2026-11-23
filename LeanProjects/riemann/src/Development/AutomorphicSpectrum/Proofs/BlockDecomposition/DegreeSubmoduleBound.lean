import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegreeSubmod

theorem exists_leftInv {K ι κ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ K) (h : LinearIndependent K Mᵀ) : ∃ Y : Matrix κ ι K, Y * M = 1 := by
  have hinj : Function.Injective M.mulVecLin := by
    have : Function.Injective M.mulVec := Matrix.mulVec_injective_iff.2 h
    exact this
  obtain ⟨g, hg⟩ := M.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h2 : LinearMap.toMatrix' (g ∘ₗ M.mulVecLin) = LinearMap.toMatrix' g * M := by
    rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rw [← h2, hg]
  simp

theorem map_fromCols {R S ι κ κ' : Type} (f : R → S) (P : Matrix ι κ R) (Q : Matrix ι κ' R) :
    (fromCols P Q).map f = fromCols (P.map f) (Q.map f) := by
  ext i (j | j) <;> rfl

theorem log_ineq {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (N : Fam K ι) (hN : IsWedge N) (hS : WedgeSub)
    {κ₀ κ₁ κ₂ : Type} [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (B : Matrix ι κ₀ K) (A : Matrix ι κ₁ K) (C : Matrix ι κ₂ K)
    (h0 : N (κ₀ ⊕ (κ₁ ⊕ κ₂)) (fromCols B (fromCols A C)) ≠ 0) (h1 : N κ₀ B ≠ 0)
    (h2 : N (κ₀ ⊕ κ₁) (fromCols B A) ≠ 0) (h3 : N (κ₀ ⊕ κ₂) (fromCols B C) ≠ 0) :
    Real.log (N (κ₀ ⊕ (κ₁ ⊕ κ₂)) (fromCols B (fromCols A C))) + Real.log (N κ₀ B) ≤
      Real.log (N (κ₀ ⊕ κ₁) (fromCols B A)) + Real.log (N (κ₀ ⊕ κ₂) (fromCols B C)) := by
  have p0 := lt_of_le_of_ne (hN.nonneg _ (fromCols B (fromCols A C))) h0.symm
  have p1 := lt_of_le_of_ne (hN.nonneg _ B) h1.symm
  rw [← Real.log_mul h0 h1, ← Real.log_mul h2 h3]
  exact Real.log_le_log (mul_pos p0 p1) (hS K ι N hN _ _ _ B A C)

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

theorem frame_leftInv {κ : Type} [Fintype κ] [DecidableEq κ] (x : GA E n) (M : Matrix (Fin n) κ E)
    (h : LinearIndependent E Mᵀ) :
    ∃ Y : Matrix κ (Fin n) (Ad E), Y * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))) = 1 := by
  obtain ⟨Y, hY⟩ := exists_leftInv M h
  refine ⟨Y.map (algebraMap E (Ad E)) * x.val, ?_⟩
  have hx : x.val * (x⁻¹ : GA E n).val = 1 := Units.mul_inv x
  have hm : Y.map (algebraMap E (Ad E)) * M.map (algebraMap E (Ad E)) = 1 := by
    rw [← Matrix.map_mul, hY, Matrix.map_one _ (map_zero _) (map_one _)]
  calc Y.map (algebraMap E (Ad E)) * x.val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)))
      = Y.map (algebraMap E (Ad E)) * (x.val * (x⁻¹ : GA E n).val) * M.map (algebraMap E (Ad E)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hx, Matrix.mul_one, hm]

theorem frame_fromCols {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : GA E n) (P : Matrix (Fin n) κ E)
    (Q : Matrix (Fin n) κ' E) :
    (x⁻¹ : GA E n).val * (fromCols P Q).map (algebraMap E (Ad E)) =
      fromCols ((x⁻¹ : GA E n).val * P.map (algebraMap E (Ad E))) ((x⁻¹ : GA E n).val * Q.map (algebraMap E (Ad E))) := by
  rw [map_fromCols, Matrix.mul_fromCols]

theorem sum_ineq (hF : WedgeF) (hI : WedgeI) (hS : WedgeSub) (hFS : FinSupp)
    {κ₀ κ₁ κ₂ : Type} [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (P : Matrix (Fin n) κ₀ (Ad E)) (Q : Matrix (Fin n) κ₁ (Ad E)) (R : Matrix (Fin n) κ₂ (Ad E))
    {Y₀ : Matrix (κ₀ ⊕ (κ₁ ⊕ κ₂)) (Fin n) (Ad E)} (h₀ : Y₀ * fromCols P (fromCols Q R) = 1)
    {Y₁ : Matrix κ₀ (Fin n) (Ad E)} (h₁ : Y₁ * P = 1)
    {Y₂ : Matrix (κ₀ ⊕ κ₁) (Fin n) (Ad E)} (h₂ : Y₂ * fromCols P Q = 1)
    {Y₃ : Matrix (κ₀ ⊕ κ₂) (Fin n) (Ad E)} (h₃ : Y₃ * fromCols P R = 1) :
    (∑ v, Real.log (nI ((fromCols P (fromCols Q R)).map (cV v))) +
        ∑ᶠ w, Real.log (nF ((fromCols P (fromCols Q R)).map (cW w)))) +
      (∑ v, Real.log (nI (P.map (cV v))) + ∑ᶠ w, Real.log (nF (P.map (cW w)))) ≤
    (∑ v, Real.log (nI ((fromCols P Q).map (cV v))) + ∑ᶠ w, Real.log (nF ((fromCols P Q).map (cW w)))) +
      (∑ v, Real.log (nI ((fromCols P R).map (cV v))) + ∑ᶠ w, Real.log (nF ((fromCols P R).map (cW w)))) := by
  obtain ⟨i₀, f₀, s₀⟩ := hFS E _ _ _ Y₀ h₀
  obtain ⟨i₁, f₁, s₁⟩ := hFS E _ _ _ Y₁ h₁
  obtain ⟨i₂, f₂, s₂⟩ := hFS E _ _ _ Y₂ h₂
  obtain ⟨i₃, f₃, s₃⟩ := hFS E _ _ _ Y₃ h₃
  have fin : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (T : Matrix (Fin n) κ (Ad E)),
      {w | nF (T.map (cW w)) ≠ 1}.Finite →
      (Function.support fun w => Real.log (nF (T.map (cW w)))).Finite := by
    intro κ _ _ T hT
    refine hT.subset fun w hw h1 => hw ?_
    simp only [Function.mem_support] at hw
    exact absurd (by rw [h1, Real.log_one]) hw
  have inf : ∑ v, Real.log (nI ((fromCols P (fromCols Q R)).map (cV v))) + ∑ v, Real.log (nI (P.map (cV v))) ≤
      ∑ v, Real.log (nI ((fromCols P Q).map (cV v))) + ∑ v, Real.log (nI ((fromCols P R).map (cV v))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have a₀ := i₀ v
    have a₂ := i₂ v
    have a₃ := i₃ v
    rw [map_fromCols] at a₂ a₃
    rw [map_fromCols, map_fromCols] at a₀
    rw [map_fromCols, map_fromCols, map_fromCols, map_fromCols]
    exact log_ineq (fun _ _ _ A => nI A) (hI _) hS _ _ _ a₀ (i₁ v) a₂ a₃
  have finp : ∑ᶠ w, Real.log (nF ((fromCols P (fromCols Q R)).map (cW w))) + ∑ᶠ w, Real.log (nF (P.map (cW w))) ≤
      ∑ᶠ w, Real.log (nF ((fromCols P Q).map (cW w))) + ∑ᶠ w, Real.log (nF ((fromCols P R).map (cW w))) := by
    rw [← finsum_add_distrib (fin _ s₀) (fin _ s₁), ← finsum_add_distrib (fin _ s₂) (fin _ s₃)]
    refine finsum_le_finsum' ((fin _ s₀).union (fin _ s₁) |>.subset (Function.support_add _ _))
      ((fin _ s₂).union (fin _ s₃) |>.subset (Function.support_add _ _)) fun w => ?_
    have a₀ := f₀ w
    have a₂ := f₂ w
    have a₃ := f₃ w
    rw [map_fromCols] at a₂ a₃
    rw [map_fromCols, map_fromCols] at a₀
    simp only [Pi.add_apply]
    rw [map_fromCols, map_fromCols, map_fromCols, map_fromCols]
    exact log_ineq (fun _ _ _ A => nF A) (hF _ _) hS _ _ _ a₀ (f₁ w) a₂ a₃
  linarith

theorem degG_ineq (hF : WedgeF) (hI : WedgeI) (hS : WedgeSub) (hFS : FinSupp) (x : GA E n)
    {κ₀ κ₁ κ₂ : Type} [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (B : Matrix (Fin n) κ₀ E) (A : Matrix (Fin n) κ₁ E) (C : Matrix (Fin n) κ₂ E)
    (l₀ : LinearIndependent E (fromCols B (fromCols A C))ᵀ) (l₁ : LinearIndependent E Bᵀ)
    (l₂ : LinearIndependent E (fromCols B A)ᵀ) (l₃ : LinearIndependent E (fromCols B C)ᵀ) :
    degG x (fromCols B A) + degG x (fromCols B C) ≤ degG x B + degG x (fromCols B (fromCols A C)) := by
  obtain ⟨Y₀, h₀⟩ := frame_leftInv x _ l₀
  obtain ⟨Y₁, h₁⟩ := frame_leftInv x _ l₁
  obtain ⟨Y₂, h₂⟩ := frame_leftInv x _ l₂
  obtain ⟨Y₃, h₃⟩ := frame_leftInv x _ l₃
  rw [frame_fromCols, frame_fromCols] at h₀
  rw [frame_fromCols] at h₂ h₃
  have key := sum_ineq hF hI hS hFS _ _ _ h₀ h₁ h₂ h₃
  simp only [degG, frame_fromCols]
  linarith

theorem degSubmod_of (hF : WedgeF) (hI : WedgeI) (hS : WedgeSub) (hFS : FinSupp) (hB : DegBasisG) (hT : TwoBases) :
    DegSubmod := by
  intro E _ _ _ n x W W'
  obtain ⟨a, b, c, B, A, C, l₀, e₁, e₂, e₃, e₄⟩ := hT E n W W'
  have l₂ : LinearIndependent E (fromCols B A)ᵀ := by
    have : (fromCols B A)ᵀ = (fromCols B (fromCols A C))ᵀ ∘ Sum.map id Sum.inl := by
      funext j; rcases j with j | j <;> rfl
    rw [this]
    exact l₀.comp _ (Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩)
  have l₃ : LinearIndependent E (fromCols B C)ᵀ := by
    have : (fromCols B C)ᵀ = (fromCols B (fromCols A C))ᵀ ∘ Sum.map id Sum.inr := by
      funext j; rcases j with j | j <;> rfl
    rw [this]
    exact l₀.comp _ (Sum.map_injective.2 ⟨Function.injective_id, Sum.inr_injective⟩)
  have l₁ : LinearIndependent E Bᵀ := by
    have : Bᵀ = (fromCols B (fromCols A C))ᵀ ∘ Sum.inl := by
      funext j; rfl
    rw [this]
    exact l₀.comp _ Sum.inl_injective
  have d₀ := hB E n _ x _ l₀
  have d₁ := hB E n _ x _ l₁
  have d₂ := hB E n _ x _ l₂
  have d₃ := hB E n _ x _ l₃
  rw [e₄] at d₀
  rw [e₁] at d₁
  rw [e₂] at d₂
  rw [e₃] at d₃
  rw [← d₀, ← d₁, ← d₂, ← d₃]
  exact degG_ineq hF hI hS hFS x B A C l₀ l₁ l₂ l₃

end GlobalTheory.CompanionTheory.DegreeSubmod

end
