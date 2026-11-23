import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.D1

def LogAbsBasic : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E],
  (∀ u : Ad E, IsUnit u → (Function.support fun w => Real.log ‖cW w u‖).Finite) ∧
  (∀ u u' : Ad E, IsUnit u → IsUnit u' → logAbs (u * u') = logAbs u + logAbs u') ∧
  ∀ c : E, c ≠ 0 → logAbs (algebraMap E (Ad E) c) = 0

def FinSupp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (ι κ : Type) [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] (A : Matrix ι κ (Ad E)) (Y : Matrix κ ι (Ad E)), Y * A = 1 →
    (∀ v, nI (A.map (cV v)) ≠ 0) ∧ (∀ w, nF (A.map (cW w)) ≠ 0) ∧ {w | nF (A.map (cW w)) ≠ 1}.Finite

def SzFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (ι κ : Type) [Fintype ι] [Fintype κ]
  (A : Matrix ι κ (Ad E)), {w | 1 < sz (A.map (cW w))}.Finite

def degG {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (x : GA E n) (M : Matrix (Fin n) κ E) : ℝ :=
  -(∑ v, Real.log (nI (((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))).map (cV v))) +
    ∑ᶠ w, Real.log (nF (((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))).map (cW w))))

theorem degG_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n k : ℕ} (x : GA E n)
    (M : Matrix (Fin n) (Fin k) E) : degG x M = degM x M := rfl

def DegBasisG : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (κ : Type) [Fintype κ]
  [DecidableEq κ] (x : GA E n) (M : Matrix (Fin n) κ E), LinearIndependent E Mᵀ →
    degG x M = deg x (Submodule.span E (Set.range Mᵀ))

def TwoBases : Prop := ∀ (K : Type) [Field K] (n : ℕ) (W W' : Submodule K (Fin n → K)),
  ∃ (a b c : ℕ) (B : Matrix (Fin n) (Fin a) K) (A : Matrix (Fin n) (Fin b) K) (C : Matrix (Fin n) (Fin c) K),
    LinearIndependent K (fromCols B (fromCols A C))ᵀ ∧ Submodule.span K (Set.range Bᵀ) = W ⊓ W' ∧
    Submodule.span K (Set.range (fromCols B A)ᵀ) = W ∧ Submodule.span K (Set.range (fromCols B C)ᵀ) = W' ∧
    Submodule.span K (Set.range (fromCols B (fromCols A C))ᵀ) = W ⊔ W'

def Radical : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E)
  (W : Submodule E (Fin n → E)), img (nrm d) W = W →
    ∃ (a b : ℕ) (B : Matrix (Fin n) (Fin a) E) (A : Matrix (Fin n) (Fin b) E), LinearIndependent E (fromCols B A)ᵀ ∧
      Submodule.span E (Set.range Bᵀ) = W ⊓ perpD (conjE E) d W ∧ Submodule.span E (Set.range (fromCols B A)ᵀ) = W ∧
      ((fromCols B A).map (conjE E))ᵀ * (d⁻¹).val * B = 0 ∧ (B.map (conjE E))ᵀ * (d⁻¹).val * fromCols B A = 0 ∧
      ((A.map (conjE E))ᵀ * (d⁻¹).val * A).det ≠ 0

def ConjPlaces : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
  (∀ v (u : Ad E), cV v (conjAd E u) = starRingEnd ℂ (cV v u)) ∧
  (∀ c : E, conjAd E (algebraMap E (Ad E) c) = algebraMap E (Ad E) (conjE E c)) ∧
  ∃ (π : Equiv.Perm (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w, (π w).adicCompletion E ≃+* w.adicCompletion E),
    (∀ w y, ‖ψ w y‖ = ‖y‖) ∧ ∀ w (u : Ad E), cW w (conjAd E u) = ψ w (cW (π w) u)

def MahlerC : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (c : ℝ),
  ∃ C : Set (GA E n), IsCompact C ∧ ∀ x : GA E n,
    (∀ W : Submodule E (Fin n → E), Module.finrank E W = 1 → deg x W ≤ c) → |deg x ⊤| ≤ c →
      x ∈ ((ratGL E n).range : Set (GA E n)) * C

end PositivityTheory.Rg.BcB.D1

end
