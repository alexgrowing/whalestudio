import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalEigenvectorGeneratesIrreducibleSubrepre
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_eigenvector_generates_irreducible_subrepresentation : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G), IsOpen (K : Set G) → IsCommensurated K → IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ K → (∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec ρ K h x = c • x) → ∃ (U : Submodule ℂ V) (hU : ∀ g, ∀ y ∈ U, ρ g y ∈ U) (hx : x ∈ U), IsIrrSmooth (GlobalTheory.PRep.sub ρ U hU) ∧ IsUnitarisable (GlobalTheory.PRep.sub ρ U hU) ∧ ∀ y ∈ fixed (GlobalTheory.PRep.sub ρ U hU) K, ∃ c : ℂ, y = c • (⟨x, hx⟩ : U) := by
  first | exact @GlobalTheory.spherical_eigenvector_generates_irreducible | exact GlobalTheory.spherical_eigenvector_generates_irreducible | (intros; apply GlobalTheory.spherical_eigenvector_generates_irreducible <;> assumption)
