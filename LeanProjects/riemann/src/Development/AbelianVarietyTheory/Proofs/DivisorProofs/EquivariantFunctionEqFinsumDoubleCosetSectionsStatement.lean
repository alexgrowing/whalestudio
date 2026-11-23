import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantFunctionEqFinsumDoubleCosetSections
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariantFunction_eq_finsum_doubleCosetSections : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G), Function.Injective ι → ∀ (ρ : Representation ℂ H V) (K' : Subgroup G), Finite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)) → (∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G)) → ∀ φ ∈ eqvM ι ρ K', ∑ᶠ q : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G), secM ι ρ K' (Quotient.out q) (φ (Quotient.out q)) = φ := by
  first | exact @GlobalTheory.BCT.TraceBlocks.eqvM_eq_finsum_secM | exact GlobalTheory.BCT.TraceBlocks.eqvM_eq_finsum_secM | (intros; apply GlobalTheory.BCT.TraceBlocks.eqvM_eq_finsum_secM <;> assumption)
