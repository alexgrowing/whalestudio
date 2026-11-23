import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularTwistedOrbit_local_finiteness : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ K' : Subgroup (GLw n w), IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) K' → (∀ x : GLw n w, twCent (thL n w) y ⊓ (GlobalTheory.LFun.KGL w n).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (thL n w) y) ∧ (twCent (thL n w) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (thL n w) y)) ≠ 0) ∧ ∀ C : Set (GLw n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (thL n w) y : Set (GLw n w)) (K' : Set (GLw n w)) | (Quotient.out q)⁻¹ * y * thL n w (Quotient.out q) ∈ C}.Finite := by
  first | exact @GlobalTheory.LocFin.main | exact GlobalTheory.LocFin.main | (intros; apply GlobalTheory.LocFin.main <;> assumption)
