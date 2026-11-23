import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
import Development.WeilBound.RepresentationTheoryGL.StandardBasisDerivatives.ArchimedeanBasisDerivatives.StBasDeriv
import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth

noncomputable section

open MeasureTheory Filter Topology Matrix GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open PositivityTheory.Rg.Pc1 (IsProfile)

namespace PositivityTheory.RgTw

variable {n : ℕ}

def KU (n : ℕ) : Subgroup (G n) where
  carrier := {k | th k = k}
  one_mem' := th_one
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, th, star_mul, _root_.mul_inv_rev] at *
    rw [hx, hy]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq, th, star_inv] at *
    rw [hx]

def RegN (d : G n) : Prop := IsRegSS (d * th d : G n).val

section

variable (n) [MeasurableSpace (G n)] [BorelSpace (G n)]

def HasTO (μ : Measure (G n)) (d : G n) (dt : Measure (twCent d)) (f : G n → ℂ) (c : ℂ) : Prop :=
  HasQuotInt (twCent d) dt μ (fun x => f (tw x d)) c

def IsThetaOp {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : G n →* (U →L[ℂ] U)) (A : U →L[ℂ] U) : Prop :=
  (∀ v, ‖A v‖ = ‖v‖) ∧ Function.Surjective A ∧ ∀ x, A ∘L π x = π (th x) ∘L A

def TwLefAt (μ : Measure (G n)) (κ : Measure (KU n)) (τ : Poly n) (f : G n → ℂ) (c : ℂ) : Prop :=
  (∃ m, f ∈ Shape n m) ∧ Continuous f ∧ HasCompactSupport f ∧ IsBiFinite (KU n) f ∧
  (∀ d : G n, RegN d → ∀ (dt : Measure (twCent d)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
    ((∃ x, tw x d ∈ KU n) → HasTO n μ d dt f (c * ev d.val τ / dt.real Set.univ)) ∧
    ((∀ x, tw x d ∉ KU n) → HasTO n μ d dt f 0)) ∧
  ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : G n →* (U →L[ℂ] U)) (A : U →L[ℂ] U),
    IsUnitaryRep π → IsTopIrreducible π → IsThetaOp n π A → ∃ (B : U →L[ℂ] U) (b : ℂ),
      (∀ v, B v = ∫ k : KU n, (ev (k : G n).val (topP n * τ) / (-4) ^ (n * n)) • π k v ∂κ) ∧
      HasTrace (B ∘L A) b ∧ HasTrace (repOp π μ f ∘L A) (c * b)

end

def TwLef : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (κ : Measure (KU n))
    [κ.IsHaarMeasure] [IsProbabilityMeasure κ], ∃ c : ℂ, c ≠ 0 ∧ ∀ τ : Poly n, IsInv τ → ∃ f, TwLefAt n μ κ τ f c

def StShape : Prop :=
  ∀ (n m : ℕ) (φ : G n → ℂ), φ ∈ Shape n m → Continuous φ ∧ HasCompactSupport φ ∧ IsBiFinite (KU n) φ

def StFam : Prop :=
  ∀ (n : ℕ) (F : ℝ → ℝ) (τ : Poly n) (P : ℕ → Poly n), IsProfile (n * n) F →
    ∃ m, ∀ t : ℝ, 0 < t → fam F τ P t ∈ Shape n m ∧ ∀ d : G n, 1 < t ^ 2 * uM d.val → fam F τ P t d = 0

def StOrbAd : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (d : G n), RegN d →
    ∀ (dt : Measure (twCent d)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (φ : G n → ℂ), φ ∈ AdSpan n → HasTO n μ d dt φ 0

def StOrbCpt : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (d : G n), RegN d →
    (∃ x, tw x d ∈ KU n) → ∃ (y : G n) (z : Fin n → ℂ), (tw y d).val = diagonal z ∧ (∀ a, ‖z a‖ = 1) ∧
      (Function.Injective fun a => z a ^ 2) ∧ ∀ (dt : Measure (twCent d)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant]
        (f : G n → ℂ), Continuous f → HasCompactSupport f →
          HasTO n μ d dt f ((∫ x, f (tw x (tw y d)) ∂μ) / dt.real Set.univ)

def StNonEll : Prop :=
  ∀ (n : ℕ) (d : G n), RegN d → (∀ x, tw x d ∉ KU n) → ∃ η : ℝ, 0 < η ∧ ∀ x, η ≤ uM (tw x d).val

def StTr : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (κ : Measure (KU n))
    [κ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    (π : G n →* (U →L[ℂ] U)) (A : U →L[ℂ] U), IsUnitaryRep π → IsTopIrreducible π → IsThetaOp n π A → ∀ m : ℕ,
      ∃ w : G n → ℂ, Continuous w ∧ (∀ φ ∈ Shape n m, HasTrace (repOp π μ φ ∘L A) (∫ g, φ g * w g ∂μ)) ∧
        ∀ P : Poly n, P.totalDegree ≤ m → ∃ B : U →L[ℂ] U, (∀ v, B v = ∫ k : KU n, ev (k : G n).val P • π k v ∂κ) ∧
          HasTrace (B ∘L A) (∫ k : KU n, ev (k : G n).val P * w k ∂κ)

def StTrAd : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (U : Type)
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : G n →* (U →L[ℂ] U)) (A : U →L[ℂ] U),
    IsUnitaryRep π → IsTopIrreducible π → IsThetaOp n π A → ∀ φ ∈ AdSpan n, HasTrace (repOp π μ φ ∘L A) 0

def StLim : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (κ : Measure (KU n))
    [κ.IsHaarMeasure] [IsProbabilityMeasure κ] (F : ℝ → ℝ), IsProfile (n * n) F → ∃ c : ℂ, c ≠ 0 ∧
      ∀ (τ : Poly n) (P : ℕ → Poly n),
      (∀ w : G n → ℂ, Continuous w → Tendsto (fun t : ℝ => ∫ g, fam F τ P t g * w g ∂μ) atTop
        (𝓝 (c * ∫ k : KU n, ev (k : G n).val (τ * P (n * n)) * w k ∂κ))) ∧
      ∀ (s : G n) (z : Fin n → ℂ), s.val = diagonal z → (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) →
        (∀ k ∈ KU n, ev (tw k s).val (τ * P (n * n)) = ev s.val (τ * P (n * n))) →
        Tendsto (fun t : ℝ => ∫ x, fam F τ P t (tw x s) ∂μ) atTop
          (𝓝 (c * ev s.val (τ * P (n * n)) / ∏ a, ∏ b, (1 + z a / z b)))

def StTopClass : Prop := ∀ (n : ℕ), ∀ k ∈ KU n, ∀ s ∈ KU n, ev (tw k s).val (topP n) = ev s.val (topP n)

def StAsm : Prop :=
  MQAlg → StInst → StTopVal → StTopClass → StHomot → PositivityTheory.Rg.Pc1.StProfile → StShape → StFam → StOrbAd → StOrbCpt → StNonEll →
    StTr → StTrAd → StLim → TwLef

end PositivityTheory.RgTw
