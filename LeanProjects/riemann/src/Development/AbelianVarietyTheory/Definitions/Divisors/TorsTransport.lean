import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (ValGe_vp IsFieldData IsIntLattice IsClassZetaVals betaBound_vp c_vp cE_vp a0)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsInvIdealOf IsLatOf)
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.LatVal

def Sz (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (r : ℝ) (x : ℂ) : Prop :=
  ∃ h : x ∈ algebraicClosure ℚ ℂ, ‖lam ⟨x, h⟩‖ ≤ (l : ℝ) ^ r

def OneOver {E : Type} [Field E] [NumberField E] (l : ℕ) (y : (Af E)ˣ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → (y : Af E) w = 1

abbrev LP := ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (_ : ℕ) (_ : I → E →+* ℂ) (_ : ℕ)
  (_ : ClassGroup (OF E) → ℚ) (_ : Ideal (OF E)) (_ : PeriodPair) (_ : ℕ) (_ : Set E), Prop

def AllLat (P : LP) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I]
    (d : ℕ) (φ : I → E →+* ℂ) (s : ℕ), IsFieldData d φ → 1 ≤ s → ∀ z : ClassGroup (OF E) → ℚ, IsClassZetaVals (2 * s) z →
    ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → IsIntLattice d Λ → ∀ l : ℕ, l.Prime →
    ∀ Q : Finset (HeightOneSpectrum (OF E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → P E I d φ s z 𝔣 Λ l (lattice (condQ 𝔣 Q) y)

def LatIntRam : Prop := AllLat fun E _ _ I _ d φ s z 𝔣 Λ l L => c_vp 𝔣 l ≠ 0 → ∀ (κ : I → ℕ) (S : ℂ → ℂ),
  IsLatSum φ (2 * s) κ L S → ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (beta E d s κ Λ (S 0))

def LatIntUnr : Prop := AllLat fun E _ _ I _ d φ s z 𝔣 Λ l L => c_vp 𝔣 l = 0 → ∀ (κ : I → ℕ) (S : ℂ → ℂ),
  IsLatSum φ (2 * s) κ L S → ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (beta E d s κ Λ (S 0))

open Classical in

def Expansion : Prop := AllLat fun _ _ _ I _ d φ s z 𝔣 Λ l L => c_vp 𝔣 l ≠ 0 →
  ∀ [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
  ∃ a b : I → ℂ, (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹) ∧
    ∀ (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), IsDefSum φ (2 * s) L g → (∀ i, u.count i = κ i) →
      Sz l lam ((cE_vp l z : ℝ) + ((2 * s * Fintype.card I : ℕ) : ℝ) * c_vp 𝔣 l +
          ((∑ i, κ i : ℕ) : ℝ) * (c_vp 𝔣 l + 1 + if l = 2 then 1 else 0))
        (iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ))))

section Transport

variable {K : Type} [Field K] [NumberField K]

def TorsTransport (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) : Prop :=
  Ω₀ ≠ 0 ∧ Ω₁ ≠ 0 ∧ (∀ x, g (ι x) = ι x) ∧ IsLatOf ι 1 Λ₀ ∧ (∃ 𝔞, IsInvIdealOf t 𝔞 ∧ IsLatOf ι 𝔞 Λ₁) ∧
    g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4 ∧ g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6 ∧
    ∀ x x' : K, ι x ∉ Λ₀.lattice →
      (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) v) ≤ 1) →
      g (Λ₀.weierstrassP (ι x) / Ω₀ ^ 2) = Λ₁.weierstrassP (ι x') / Ω₁ ^ 2 ∧
        g (Λ₀.derivWeierstrassP (ι x) / Ω₀ ^ 3) = Λ₁.derivWeierstrassP (ι x') / Ω₁ ^ 3

def IsLatDatum {E : Type} [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I] (ι : K →+* ℂ)
    (φ : I → E →+* ℂ) (s : ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Prop :=
  UnramFin E ∧ IsCMType φ ∧ (∀ i, (φ i).comp (algebraMap K E) = ι) ∧ 1 ≤ s ∧ IsBaseCond 𝔣 ∧ IsFinSetSplitPlacesCoprimeConductor 𝔣 Q

end Transport

def PeriodEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : K →+* ℂ), Module.finrank ℚ K = 2 →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), IsLatOf ι 1 Λ₀ → Ω₀ ≠ 0 →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (j : Ω →+* ℂ)
      (art : Ideles K →* Gab K Ω), j.comp (algebraMap K Ω) = ι → IsGlobalArtin art →
      ∀ (g : ℂ ≃+* ℂ) (σ : Formalism.ConjugateSelfDual.G K Ω) (t : (Af K)ˣ), (∀ x, j (σ x) = g (j x)) → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsSymbol art t σ →
      ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁

def LatAlg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), IsLatOf ι 1 Λ₀ → Ω₀ ^ 12 = latDisc Λ₀ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
      (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsLatDatum ι φ s 𝔣 Q →
      ∀ (κ : I → ℕ) (y : (Af E)ˣ) (S : ℂ → ℂ), IsLatSum φ (2 * s) κ (lattice (condQ 𝔣 Q) y) S →
        IsAlgebraic ℚ (coordIn E d s κ Ω₀ (S 0))

def LatConj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
      (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsLatDatum ι φ s 𝔣 Q →
      ∀ (κ κ' : I → ℕ), IsConjWt φ g κ κ' → ∀ (y : (Af E)ˣ) (S S' : ℂ → ℂ),
        IsLatSum φ (2 * s) κ (lattice (condQ 𝔣 Q) y) S →
        IsLatSum φ (2 * s) κ' (lattice (condQ 𝔣 Q) (y * (upIdele K E t)⁻¹)) S' →
        g (coordIn E d s κ Ω₀ (S 0)) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' 0)

def LatClaims : Prop := LatIntRam ∧ LatIntUnr ∧ Expansion ∧ PeriodEx ∧ LatAlg ∧ LatConj

end GlobalTheory.LatVal
