import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SumSquaresNeThreeThreeAdic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited

noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.SplitUnitary.Model

open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
open GlobalTheory.HermLocal.Model (conjSqrt conjSqrt_apply)

theorem isQuad_sqrt {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] :
    IsQuad (conjSqrt d : QuadraticAlgebra K d 0 →ₐ[K] QuadraticAlgebra K d 0) QuadraticAlgebra.omega where
  unit := by
    refine IsUnit.mk0 _ fun h => ?_
    simpa using congrArg QuadraticAlgebra.im h
  anti := by
    change star _ = _
    ext <;> simp
  basis := ⟨QuadraticAlgebra.basis d 0, by
    ext <;> simp [QuadraticAlgebra.basis, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one], by
    ext <;> simp [QuadraticAlgebra.basis]⟩

theorem isQuad_isHerm_continuous_resEtaPow (K : Type) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] (k : ℕ) :
    ∃ (_ : TopologicalSpace (QuadraticAlgebra K d 0)) (_ : IsModuleTopology K (QuadraticAlgebra K d 0))
      (c : QuadraticAlgebra K d 0 →ₐ[K] QuadraticAlgebra K d 0) (δ : QuadraticAlgebra K d 0)
      (Q : Matrix (Fin (2 * k)) (Fin (2 * k)) (QuadraticAlgebra K d 0)) (ψ : AddChar K ℂ)
      (χ : (QuadraticAlgebra K d 0)ˣ →* Circle),
      IsQuad c δ ∧ IsHerm c Q ∧ Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ψ ≠ 1 ∧ Continuous χ ∧
        ResEtaPow (R := K) ⊥ χ (Fintype.card (Fin (2 * k))) := by
  obtain ⟨ψ, hψ⟩ := SplitWeil.exists_hasConductor_one K
  letI : TopologicalSpace (QuadraticAlgebra K d 0) := moduleTopology K _
  refine ⟨this, ⟨rfl⟩, _, _, 1, Circle.coeHom.compAddChar ψ, 1, isQuad_sqrt d, ⟨fun i j => ?_, by simp⟩,
    continuous_subtype_val.comp hψ.continuous, fun t => Circle.norm_coe _, fun h => hψ.ne_one ?_, ?_, fun a => ?_⟩
  · by_cases h : i = j
    · subst h; simp
    · simp [one_apply_ne h, one_apply_ne (Ne.symm h)]
  · ext x
    exact DFunLike.congr_fun h x
  · exact continuous_const
  · simp [pow_mul]

theorem hyps_dyadic : ∃ (_ : IsNonarchimedeanLocalField ℚ_[2]) (_ : TopologicalSpace (QuadraticAlgebra ℚ_[2] 2 0))
      (_ : IsModuleTopology ℚ_[2] (QuadraticAlgebra ℚ_[2] 2 0))
      (c : QuadraticAlgebra ℚ_[2] 2 0 →ₐ[ℚ_[2]] QuadraticAlgebra ℚ_[2] 2 0) (δ : QuadraticAlgebra ℚ_[2] 2 0)
      (Q : Matrix (Fin (2 * 1)) (Fin (2 * 1)) (QuadraticAlgebra ℚ_[2] 2 0)) (ψ : AddChar ℚ_[2] ℂ)
      (χ : (QuadraticAlgebra ℚ_[2] 2 0)ˣ →* Circle),
      IsQuad c δ ∧ IsHerm c Q ∧ Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ψ ≠ 1 ∧ Continuous χ ∧
        ResEtaPow (R := ℚ_[2]) ⊥ χ (Fintype.card (Fin (2 * 1))) :=
  ⟨GlobalTheory.SplitWeil.Model.padic_localField 2, @isQuad_isHerm_continuous_resEtaPow ℚ_[2] _ _ _ _ (GlobalTheory.SplitWeil.Model.padic_localField 2) 2 _ 1⟩

section Form

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)

theorem form_rank_one (q x y : E) :
    form (α := Unit) (ν := Unit) c (fun _ _ => q) (fromCols (fun _ _ => x) 0) (fromCols 0 (fun _ _ => y)) =
      2⁻¹ * Algebra.trace F E (x * q * c y) := by
  simp [form, hTens, stdJ, Fintype.sum_sum_type, fromCols]

end Form

section Edge

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def Concl (hc : ∀ z, c (c z) = z) (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) {ψ : AddChar F ℂ}
    (hψ : Continuous ψ) (χ : Eˣ →* Circle) : Prop :=
  ∃ ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E)),
      IsSmoothRep ω ∧
      (∀ μ : @Measure (Matrix α ν E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)),
          ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ) ∧
      (∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E),
        Heisenberg₂ c hψ Q w * ω g =
          ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) ∧
      ∀ (a : GL ν E) (φ : SB (Matrix α ν E)) (x : Matrix α ν E),
        (ω (levi c hc a) φ : Matrix α ν E → ℂ) x =
          (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
            ((nabs F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det a)) ^
              ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) *
            (φ : Matrix α ν E → ℂ) (x * (a : Matrix ν ν E))

theorem concl_of [CharZero F] (h : GlobalTheory.Published.KudlaSplittingSplitUnitary) {δ : E} (hE : IsQuad c δ) (Q : Matrix α α E)
    (hQ : IsHerm c Q) {ψ : AddChar F ℂ} (hψ : Continuous ψ) (h1 : ∀ t, ‖ψ t‖ = 1) (h2 : ψ ≠ 1) (χ : Eˣ →* Circle)
    (hχ : Continuous χ) (hr : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) : Concl c hE.invol ν Q hψ χ :=
  h F E c δ hE α ν Q hQ ψ hψ h1 h2 χ hχ hr

theorem concl_rank_zero_right [IsEmpty ν] (hc : ∀ z, c (c z) = z) (Q : Matrix α α E) {ψ : AddChar F ℂ}
    (hψ : Continuous ψ) (χ : Eˣ →* Circle) : Concl c hc ν Q hψ χ := by
  refine ⟨1, fun v => by simp, fun μ _ g φ => rfl, fun g w => ?_, fun a φ x => ?_⟩
  · rw [Subsingleton.elim (w * _) w]; simp
  · have : Matrix.GeneralLinearGroup.det a = 1 := Units.ext (by simp)
    rw [this, Subsingleton.elim (x * _) x]
    simp [nabs]

theorem concl_rank_zero_left [IsEmpty α] (hc : ∀ z, c (c z) = z) (Q : Matrix α α E) {ψ : AddChar F ℂ}
    (hψ : Continuous ψ) : Concl c hc ν Q hψ 1 := by
  refine ⟨1, fun v => by simp, fun μ _ g φ => rfl, fun g w => ?_, fun a φ x => ?_⟩
  · rw [Subsingleton.elim (w * _) w]; simp
  · rw [Subsingleton.elim (x * _) x]
    simp

end Edge

end GlobalTheory.SplitUnitary.Model

end
