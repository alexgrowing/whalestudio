import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdelicSplit

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def AdelicLatticeDictionary.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∃ (K : Subgroup (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) (D : ℕ)
    (L : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) → AddSubgroup W),
    IsCompact (K : Set (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) ∧
    IsOpen (K : Set (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) ∧
    (∀ g, IsDIntegral h D (L g)) ∧
    (∀ (γ : h.unitaryGroup) g, L ((adeleSplit h v (hermitianDiagonal h v γ)).2 * g) = γ • L g) ∧
    ∀ g g', L g = L g' ↔ g⁻¹ * g' ∈ K

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
