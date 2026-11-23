import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul

section

noncomputable section

open MeasureTheory GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG)
open Formalism.MainNotions.S (IsDS allPos)
open GlobalTheory.HCChar (dsChar torusPt)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.Pc

def GapG (r : ℕ) (lam : Fin r → ℤ) : Prop :=
  ∀ i j : Fin r, (j : ℕ) = i + 1 → 100 * (r : ℤ) ^ 4 ≤ lam i - lam j

def IsPC' {r : ℕ} (ε : Fin r → Bool) (lam : Fin r → ℤ) (μ : Measure (UJ ε)) {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X))
    (hD : IsDS ε (fun a => (lam a : ℝ)) D) (f : UJ ε → ℂ) : Prop :=
  haveI := hD.1
  f ∈ CcMat (ujMat ε) ∧ IsBiFinite (KG ε) f ∧ HasTrace (repOp (ujRep hD.2.2.1) μ f) 1 ∧
    (∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)),
      IsUnitaryRep π → IsTopIrreducible π → ¬ IsUnitEquiv π (ujRep hD.2.2.1) → HasTrace (repOp π μ f) 0) ∧
    (∀ s, IsRegSS (ujMat ε s) → ¬ IsCompact (cent s : Set (UJ ε)) →
      ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant], HasOrbInt μ s dt f 0) ∧
    (∀ s, IsRegSS (ujMat ε s) → IsCompact (cent s : Set (UJ ε)) → ∀ (y : UJ ε) (θ : Fin r → ℝ),
      y⁻¹ * s * y = torusPt ε θ →
      ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
        HasOrbInt μ s dt f (conj (dsChar ε (fun a => (lam a : ℝ)) θ) / dt.real Set.univ))

def LocalPC : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ), GapG r lam →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X))
      (hD : IsDS ε (fun a => (lam a : ℝ)) D) (μ : Measure (UJ ε)) [μ.IsHaarMeasure], ∃ f, IsPC' ε lam μ D hD f

end GlobalTheory.PsCo.Pc

end
end

section

noncomputable section

open MeasureTheory Filter Topology
open Formalism.REAL (UJ KG toM toMK muK)

namespace GlobalTheory.PsCo.Pc1

def StLim : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (G : ℝ → ℝ), IsProfile (nMode ε) G →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ p : ℕ → Poly n,
      (∀ w : UJ ε → ℂ, Continuous w →
        Tendsto (fun t : ℝ => ∫ g, famF ε G p t (toM g) * w g ∂μ) atTop
          (𝓝 (c * ∫ k, ev (toMK k) (p (nMode ε)) * w k ∂(muK ε)))) ∧
      ∀ (θ : Fin n → ℝ) (s : UJ ε), toM s = Matrix.diagonal (fun a => Complex.exp (θ a * Complex.I)) →
        Function.Injective (fun a => Complex.exp (θ a * Complex.I)) →
        (∀ k : KG ε, ev (toM ((k : UJ ε)⁻¹ * s * (k : UJ ε))) (p (nMode ε)) = ev (toM s) (p (nMode ε))) →
        Tendsto (fun t : ℝ => ∫ x, famF ε G p t (toM (x⁻¹ * s * x)) ∂μ) atTop
          (𝓝 (c * ev (toM s) (p (nMode ε)) / (dMode ε θ : ℂ)))

end GlobalTheory.PsCo.Pc1

end
end

section

noncomputable section

open MeasureTheory Filter Topology GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open Formalism.MainNotions.S (IsDS)
open GlobalTheory.HCChar (dsChar torusPt)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.Pc1

def Gap4 (r : ℕ) (lam : Fin r → ℤ) : Prop :=
  ∀ i j : Fin r, (j : ℕ) = i + 1 → 100 * (r : ℤ) ^ 4 ≤ lam i - lam j

def StShape : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ) (φ : Mat n → ℂ), φ ∈ ShapeM ε d →
    (fun g : UJ ε => φ (toM g)) ∈ CcMat (ujMat ε) ∧ IsBiFinite (KG ε) (fun g : UJ ε => φ (toM g)) ∧
      Continuous (fun g : UJ ε => φ (toM g)) ∧ HasCompactSupport (fun g : UJ ε => φ (toM g))

def StOrbAd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (s : UJ ε), IsRegSS (ujMat ε s) →
    ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (φ : Mat n → ℂ), φ ∈ AdSpanM ε →
      HasOrbInt μ s dt (fun g => φ (toM g)) 0

def StOrbCpt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (s : UJ ε), IsRegSS (ujMat ε s) →
    IsCompact (cent s : Set (UJ ε)) → ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant]
      (y : UJ ε) (f : UJ ε → ℂ), Continuous f → HasCompactSupport f →
      HasOrbInt μ s dt f ((∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) / dt.real Set.univ)

def StNonEll : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (s : UJ ε), IsRegSS (ujMat ε s) → ¬ IsCompact (cent s : Set (UJ ε)) →
    ∃ R : ℝ, 0 < R ∧ ∀ x : UJ ε, R ≤ rM ε (toM (x⁻¹ * s * x))

def StTr : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π →
    ∀ d : ℕ, ∃ w : UJ ε → ℂ, Continuous w ∧
      (∀ φ ∈ ShapeM ε d, HasTrace (repOp π μ fun g => φ (toM g)) (∫ g, φ (toM g) * w g ∂μ)) ∧
      ∀ P : Poly n, P.totalDegree ≤ d → ∃ B : U →L[ℂ] U,
        (∀ v, B v = ∫ k : KG ε, ev (toMK k) P • π k v ∂(muK ε)) ∧
          HasTrace B (∫ k : KG ε, ev (toMK k) P * w k ∂(muK ε))

def StTrAd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π →
    ∀ φ ∈ AdSpanM ε, HasTrace (repOp π μ fun g => φ (toM g)) 0

def StKData : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ), Gap4 r lam →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X))
      (hD : IsDS ε (fun a => (lam a : ℝ)) D), haveI := hD.1
      ∃ (M : ℕ) (P : Poly r), P ∈ blockAlg ε ∧
        (∀ k k' : KG ε, ev (toMK (k'⁻¹ * k * k')) (topP ε M P) = ev (toMK k) (topP ε M P)) ∧
        (∀ θ : Fin r → ℝ, Function.Injective (fun a => Complex.exp (θ a * Complex.I)) →
          ev (toM (torusPt ε θ)) (topP ε M P) = conj (dsChar ε (fun a => (lam a : ℝ)) θ) * (dMode ε θ : ℂ)) ∧
        (∀ (B : X →L[ℂ] X) (c : ℂ), (∀ v, B v = ∫ k : KG ε, ev (toMK k) (topP ε M P) • D (toMK k) v ∂(muK ε)) →
          HasTrace B c → c = 1) ∧
        ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)),
          IsUnitaryRep π → IsTopIrreducible π → ¬ IsUnitEquiv π (ujRep hD.2.2.1) → ∀ (B : U →L[ℂ] U) (c : ℂ),
            (∀ v, B v = ∫ k : KG ε, ev (toMK k) (topP ε M P) • π k v ∂(muK ε)) → HasTrace B c → c = 0

end GlobalTheory.PsCo.Pc1

end
end

section

noncomputable section

open MeasureTheory Filter Topology
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc3

variable {n : ℕ}

def pB (ε : Fin n → Bool) (B : Mode ε → ℂ) : Mat n := fun a b =>
  if h : ε a = true ∧ ε b = false then B ⟨(a, b), h⟩
  else if h' : ε b = true ∧ ε a = false then star (B ⟨(b, a), h'⟩) else 0

def blkM (ε : Fin n → Bool) (g : Mat n) : Mode ε → ℂ := fun x => g x.1.1 x.1.2

def eB (ε : Fin n → Bool) (B : Mode ε → ℂ) : UJ ε := Formalism.REAL.expG ε (pB ε B) 1

def StEB : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), Continuous (eB ε) ∧ eB ε 0 = 1 ∧ ∀ B, toM (eB ε B) = NormedSpace.exp (pB ε B) ∧
    toM (eB ε B)⁻¹ = NormedSpace.exp (-pB ε B)

def StR : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), (Continuous fun g : UJ ε => rM ε (toM g)) ∧
    (∀ (k k' : KG ε) (g : UJ ε), rM ε (toM ((k : UJ ε) * g * (k' : UJ ε))) = rM ε (toM g)) ∧
    (∀ g : UJ ε, rM ε (toM g) = 0 ↔ g ∈ KG ε) ∧ ∀ C : ℝ, IsCompact {g : UJ ε | rM ε (toM g) ≤ C}

def StPolar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure], ∃ J : (Mode ε → ℂ) → ℝ, Continuous J ∧ 0 < J 0 ∧
    ∀ f : UJ ε → ℂ, Continuous f → HasCompactSupport f →
      ∫ g, f g ∂μ = ∫ B, (J B : ℂ) * ∫ k : KG ε, f (k * eB ε B) ∂(muK ε) ∧
      ∫ g, f g ∂μ = ∫ B, (J B : ℂ) * ∫ k : KG ε, f (eB ε B * k) ∂(muK ε)

def StExpLow : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (B : Mode ε → ℂ), ∑ x, ‖B x‖ ^ 2 ≤ rM ε (NormedSpace.exp (pB ε B))

def StExpDeriv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    HasFDerivAt (fun B => blkM ε (NormedSpace.exp (pB ε B))) (ContinuousLinearMap.id ℝ (Mode ε → ℂ)) 0 ∧
    ∀ s : Fin n → ℂ, ∃ L : (Mode ε → ℂ) →L[ℝ] (Mode ε → ℂ), (∀ w x, L w x = (s x.1.1 - s x.1.2) * w x) ∧
      HasFDerivAt (fun B => blkM ε (NormedSpace.exp (-pB ε B) * Matrix.diagonal s * NormedSpace.exp (pB ε B))) L 0

def StConjLow : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (s : UJ ε) (d : Fin n → ℂ), toM s = Matrix.diagonal d → Function.Injective d →
    ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ x : UJ ε, rM ε (toM (x⁻¹ * s * x)) ≤ η → rM ε (toM x) ≤ δ

def StBlow : Prop :=
  ∀ (ι : Type) [Fintype ι] (β : (ι → ℂ) → (ι → ℂ)) (d : ι → ℂ) (L : (ι → ℂ) →L[ℝ] (ι → ℂ)), (∀ x, d x ≠ 0) →
    (∀ w x, L w x = d x * w x) → Continuous β → β 0 = 0 → HasFDerivAt β L 0 →
    (∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ B, ∑ x, ‖β B x‖ ^ 2 ≤ η → ‖B‖ ≤ δ) →
    ∀ (F : ℝ → ℝ), Continuous F → (∀ x, 1 ≤ x → F x = 0) → ∀ ψ : (ι → ℂ) → ℂ, Continuous ψ →
      (∀ᶠ t : ℝ in atTop, Integrable fun B => (F (t * ∑ x, ‖β B x‖ ^ 2) : ℂ) * ψ B) ∧
      Tendsto (fun t : ℝ => (t : ℂ) ^ Fintype.card ι * ∫ B, (F (t * ∑ x, ‖β B x‖ ^ 2) : ℂ) * ψ B) atTop
        (𝓝 (ψ 0 * ((∫ w : ι → ℂ, F (∑ x, ‖w x‖ ^ 2) : ℝ) : ℂ) / ((∏ x, ‖d x‖ ^ 2 : ℝ) : ℂ)))

def StConst : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : ℝ → ℝ), IsProfile (Fintype.card ι) G →
    ∫ w : ι → ℂ, iteratedDeriv (Fintype.card ι) G (∑ x, ‖w x‖ ^ 2) ≠ 0

def StFamBlow : Prop :=
  ∀ (ι : Type) [Fintype ι] (β : (ι → ℂ) → (ι → ℂ)) (d : ι → ℂ) (L : (ι → ℂ) →L[ℝ] (ι → ℂ)), (∀ x, d x ≠ 0) →
    (∀ w x, L w x = d x * w x) → Continuous β → β 0 = 0 → HasFDerivAt β L 0 →
    (∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ B, ∑ x, ‖β B x‖ ^ 2 ≤ η → ‖B‖ ≤ δ) →
    ∀ (G : ℝ → ℝ), IsProfile (Fintype.card ι) G → ∀ ψ : ℕ → (ι → ℂ) → ℂ, (∀ k, Continuous (ψ k)) →
      Tendsto (fun t : ℝ => ∫ B, ∑ k ∈ Finset.range (Fintype.card ι + 1),
          ((iteratedDeriv k (fun x => G (t * x)) (∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) * ψ k B) atTop
        (𝓝 (ψ (Fintype.card ι) 0 * ((∫ w : ι → ℂ, iteratedDeriv (Fintype.card ι) G (∑ x, ‖w x‖ ^ 2) : ℝ) : ℂ) /
          ((∏ x, ‖d x‖ ^ 2 : ℝ) : ℂ)))

end GlobalTheory.PsCo.Pc3

end
end

section

noncomputable section

open MeasureTheory Filter Topology GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK expG inG)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3

def PolyVec {n : ℕ} (ε : Fin n → Bool) (d : ℕ) {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    (π : UJ ε →* (U →L[ℂ] U)) (v : U) : Prop :=
  ∀ l : U, ∃ P : Poly n, P.totalDegree ≤ d ∧ ∀ k : KG ε, ⟪l, π k v⟫_ℂ = ev (toMK k) P

def Repro : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ Q : Poly n, Q.totalDegree ≤ d ∧ ∀ P : Poly n, P.totalDegree ≤ d →
    ev 1 P = ∫ k : KG ε, ev (toMK k) Q * ev (toMK k) P ∂(muK ε)

def UFin : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → ∀ d : ℕ,
    ∃ L : Submodule ℂ U, FiniteDimensional ℂ L ∧ (∀ v, PolyVec ε d π v → v ∈ L) ∧
      ∀ v ∈ L, ∀ Z, inG ε Z → ∃ w, HasDerivAt (fun t : ℝ => π (expG ε Z t) v) w 0

def RangeShape : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ d : ℕ, ∀ φ ∈ ShapeM ε d,
    IsRepOp π μ (fun g => φ (toM g)) (repOp π μ fun g => φ (toM g)) ∧
    ∀ u, PolyVec ε d π (repOp π μ (fun g => φ (toM g)) u) ∧
      PolyVec ε d π (ContinuousLinearMap.adjoint (repOp π μ fun g => φ (toM g)) u)

def RangeK : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ P : Poly n, ∃ B : U →L[ℂ] U,
    (∀ v, (Integrable (fun k : KG ε => ev (toMK k) P • π k v) (muK ε)) ∧
      B v = ∫ k : KG ε, ev (toMK k) P • π k v ∂(muK ε)) ∧ ∀ u, PolyVec ε P.totalDegree π (B u)

def TraceSum : Prop :=
  ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (L : Submodule ℂ U)
    [FiniteDimensional ℂ L] (T : U →L[ℂ] U), (∀ u, T u ∈ L) →
    HasTrace T (∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), T (stdOrthonormalBasis ℂ L j : U)⟫_ℂ)

def ConjDeriv : Prop :=
  ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (L : Submodule ℂ U)
    [FiniteDimensional ℂ L] (x y : ℝ → U →L[ℂ] U) (A : U →L[ℂ] U), x 0 = 1 → (∀ t v w, ⟪x t v, x t w⟫_ℂ = ⟪v, w⟫_ℂ) →
    (∀ t v w, ⟪v, y t w⟫_ℂ = ⟪x t v, w⟫_ℂ) → (∀ v ∈ L, ∃ w, HasDerivAt (fun t => x t v) w 0) →
    (∀ u, A u ∈ L) → (∀ u, ContinuousLinearMap.adjoint A u ∈ L) →
    HasDerivAt (fun t => ∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), x t (A (y t (stdOrthonormalBasis ℂ L j : U)))⟫_ℂ) 0 0

end GlobalTheory.PsCo.Pc3

end
end
