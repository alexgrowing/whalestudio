import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SmoothCartan
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

noncomputable section

open GlobalTheory.BorelCoh GroundTheory.Automorphic MeasureTheory
open scoped Matrix ComplexOrder

namespace GlobalTheory.Mt

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

namespace CartanData

variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (D : CartanData G 𝔤)

def IsAdm {d : ℕ} (ξ : G →* Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ i j, D.lie.IsSmoothFun (F := ℂ) fun g => ξ g i j) ∧
  ∃ Q : Matrix (Fin d) (Fin d) ℂ, Q.PosDef ∧ (∀ X ∈ D.p, Q * D.dξ ξ X = (D.dξ ξ X)ᴴ * Q) ∧
    ∀ X ∈ D.k, Q * D.dξ ξ X = -((D.dξ ξ X)ᴴ * Q)

def IsCCR {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) : Prop :=
  ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    ∀ f : CompactlySupportedContinuousMap G ℂ, IsCompactOperator (π.integrated μ (UnitaryRep.ccToL1 μ f))

def repξ (Γ : Subgroup G) {d : ℕ} (ξ : G →* Matrix (Fin d) (Fin d) ℂ) : Representation ℂ Γ (Fin d → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toRingEquiv.toMonoidHom.comp
    (ξ.comp Γ.subtype)

def MatsushimaAbs : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (d : ℕ) (ξ : G →* Matrix (Fin d) (Fin d) ℂ), IsCCR π → D.IsAdm ξ →
  ∀ (s : Set (Submodule ℂ H)) (hc : ∀ V : s, CompleteSpace (V : Submodule ℂ H)) (hinv : ∀ V : s, π.IsInvariant V),
    IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ H)) (fun V => (V : Submodule ℂ H).subtypeₗᵢ) →
    (∀ V : s, letI := hc V; (π.restrict V (hinv V)).IsIrreducible) →
    ∀ q, FiniteDimensional ℂ (D.HGK π ξ q) ∧
      {V : s | letI := hc V; Nontrivial (D.HGK (π.restrict V (hinv V)) ξ q)}.Finite ∧
      Module.finrank ℂ (D.HGK π ξ q) = ∑ᶠ V : s, letI := hc V; Module.finrank ℂ (D.HGK (π.restrict V (hinv V)) ξ q)

def MatsushimaLattice : Prop :=
  ∀ (Γ : Subgroup G) [DiscreteTopology Γ] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant], CompactSpace (GlobalTheory.AutomorphicL2Unitary.Quot Γ) →
  ∀ (π : UnitaryRep G (GlobalTheory.AutomorphicL2Unitary.L2 Γ μ)), (∀ g, (π.toHom g : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ →L[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) = GlobalTheory.AutomorphicL2Unitary.R Γ μ g) →
  ∀ (d : ℕ) (ξ : G →* Matrix (Fin d) (Fin d) ℂ), D.IsAdm ξ →
  ∀ q, Nonempty (groupCohomology (Rep.of (repξ Γ ξ)) q ≃ₗ[ℂ] D.HGK π ξ q)

end CartanData

end GlobalTheory.Mt
