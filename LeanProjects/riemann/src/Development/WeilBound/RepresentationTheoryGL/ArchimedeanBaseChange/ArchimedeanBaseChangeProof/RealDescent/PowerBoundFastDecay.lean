import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.ArchBaseChangeOfHyp
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.CutTrDZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PowerBoundNonzeroCoefficient
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotIntegralZero

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F
open scoped Classical

namespace PositivityTheory.Rg.BcB.Desc

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def ldet (x : H E n 0) : ℝ := logAbs x.1.val.det

def IsPiVec (D : Dom E n 0) (π : CuspSub E n) {ι : Type} (f : Hs (ι := ι) D) : Prop :=
  ∀ i, ∃ ψ ∈ π.V, ∃ u : ℝ → ℂ, Continuous u ∧ HasCompactSupport u ∧
    (f i : H E n 0 → ℂ) =ᵐ[D.ν] fun x => ψ.1 x.1 * u (ldet x)

def piSp (D : Dom E n 0) (π : CuspSub E n) (ι : Type) [Fintype ι] : Submodule ℂ (Hs (ι := ι) D) :=
  (Submodule.span ℂ {f | IsPiVec D π f}).topologicalClosure

instance (D : Dom E n 0) (π : CuspSub E n) (ι : Type) [Fintype ι] : CompleteSpace (piSp D π ι) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def ThetaFix (π : CuspSub E n) : Prop :=
  (∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g) ∧ ∀ ψ ∈ π.V, ∃ ψ' ∈ π.V, ∀ g, ψ'.1 g = ψ.1 (thetaA E n g)

def ThetaFixOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → ThetaFix π

def PiVecEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ ψ ∈ π.V, ∀ u : ℝ → ℂ, Continuous u → HasCompactSupport u →
    MemLp (fun x : H E n 0 => ψ.1 x.1 * u (ldet x)) 2 D.ν ∧
      ∀ M : ℕ, ∫⁻ x, ENNReal.ofReal (wt x ^ (2 * M)) * ‖ψ.1 x.1 * u (ldet x)‖ₑ ^ 2 ∂D.ν < ⊤

def PiInv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ : Matrix ι ι (H E n 0 → ℂ)) (T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D),
    IsTestM Φ → IsROp D Φ T → ∀ f ∈ piSp D π ι, T f ∈ piSp D π ι

def IsTwTr (μ : Measure (H E n 0)) (π : CuspSub E n) (φ : H E n 0 → ℂ) (t : ℂ) : Prop :=
  ∃ L : π.V →ₗ[ℂ] π.V, (∀ (ψ : π.V) x, (L ψ).1.1 x = ∫ y, φ y * ψ.1.1 (thetaA E n (x * y.1)) ∂μ) ∧
    FiniteDimensional ℂ (LinearMap.range L) ∧
    t = LinearMap.trace ℂ (LinearMap.range L) (L.restrict fun x _ => LinearMap.mem_range_self L x)

def FinOn (μ : Measure (H E n 0)) (π : CuspSub E n) (φ : H E n 0 → ℂ) : Prop :=
  ∃ W : Submodule ℂ (Sm E n), W ≤ π.V ∧ FiniteDimensional ℂ W ∧ ∀ u : ℝ → ℂ, Continuous u → ∀ ψ ∈ π.V,
    ∃ ψ' ∈ W, ∀ x, ψ'.1 x = ∫ y, φ y * u (ldet y) * ψ.1 (x * y.1) ∂μ

def GrowthPi : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (n : ℕ), 1 ≤ n →
  ∀ [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] [MeasurableSpace (GA E 0)] [BorelSpace (GA E 0)]
  (μ₁ : Measure (GA E n)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E 0)) [μ₂.IsHaarMeasure],
  ∃ D : Dom E n 0, (∀ F : H E n 0 → ℂ, Continuous F → HasCompactSupport F → ∫ x, F x ∂D.μ = ∫ x₁, ∫ x₂, F (x₁, x₂) ∂μ₂ ∂μ₁) ∧
    ∀ π : CuspSub E n, ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
    (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (r₀ r₁ ε : ℝ), IsTestM Φ₁ → IsTestM Φ₂ →
    (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ → 0 ≤ r₀ → 0 ≤ r₁ → 0 < ε → ∃ (C : ℝ) (N : ℕ), ∀ (k : ℕ)
      (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)) (t : ℂ), IsTestM Φ → IsROp D Φ (T₁ * U * T₂) →
      (∀ f ∈ piSp D π ι, U f ∈ piSp D π ι) → (∀ f ∈ (piSp D π ι)ᗮ, U f ∈ (piSp D π ι)ᗮ) →
      D4.IsTest2J (trM Φ M) (r₀ + k * r₁) → IsTwTr D.μ π (trM Φ M) t →
      ‖ellSum2 μ₁ μ₂ (trM Φ M) - t / 2‖ ≤ C * (1 + k) ^ N * ‖U ∘L (piSp D π ι)ᗮ.subtypeL‖ + C * ‖U‖ * ε ^ k

def PiSeen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ W : Submodule ℂ (Sm E n), W ≤ π.V → FiniteDimensional ℂ W →
    ∃ (ψ : ℕ → Sm E n) (u : ℕ → ℝ → ℂ), (∀ j, ψ j ∈ π.V ∧ Continuous (u j) ∧ HasCompactSupport (u j)) ∧
      ∀ φ ∈ W, ∀ z : ℂ, (∀ j, ∫ x, starRingEnd ℂ ((ψ j).1 x.1 * u j (ldet x)) * (φ.1 x.1 * Complex.exp (z * ldet x)) ∂D.ν = 0) →
        φ = 0

def PowerBoundFastDecay : Prop := ∀ (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
  (ι : Type) [Fintype ι] [Nonempty ι] (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] (R : ∀ s, B →⋆ₐ[ℂ] (H s →L[ℂ] H s)) (J : Type) [Fintype J] (c : J → ℂ) (q : J → (B →ₐ[ℂ] ℂ)),
  (∀ b, ∀ ε : ℝ, 0 < ε → ∃ (C : ℝ) (N : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
    ‖∑ j, c j * q j b ^ k‖ ≤
      C * (1 + k) ^ N * (Finset.univ.sup' Finset.univ_nonempty fun s => ‖R s b‖) ^ k + C * ε ^ k) →
  ∀ p : B →⋆ₐ[ℂ] ℂ, ∑ j with q j = (p : B →ₐ[ℂ] ℂ), c j ≠ 0 → ∃ s, ∀ b, ‖p b‖ ≤ ‖R s b‖

def SwapTrace : Prop := ∀ (A₁ A₂ : Type) [Ring A₁] [Algebra ℂ A₁] [Ring A₂] [Algebra ℂ A₂] (Y : Type) [AddCommGroup Y]
  [Module ℂ Y] [FiniteDimensional ℂ Y] [Nontrivial Y] (ρ₁ : A₁ →ₐ[ℂ] Module.End ℂ Y) (ρ₂ : A₂ →ₐ[ℂ] Module.End ℂ Y)
  (s : A₁ ≃ₐ[ℂ] A₂) (T : Module.End ℂ Y), (∀ a b, Commute (ρ₁ a) (ρ₂ b)) →
  (∀ W : Submodule ℂ Y, (∀ a, ∀ y ∈ W, ρ₁ a y ∈ W) → (∀ b, ∀ y ∈ W, ρ₂ b y ∈ W) → W = ⊥ ∨ W = ⊤) →
  T * T = 1 → (∀ a, T * ρ₁ a = ρ₂ (s a) * T) →
  ∃ c : ℂ, c ≠ 0 ∧ ∀ a, LinearMap.trace ℂ Y (ρ₁ a * T) = c * LinearMap.trace ℂ Y (ρ₁ a)

end PositivityTheory.Rg.BcB.Desc

end
