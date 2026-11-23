import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLevelIffLatticeStable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruenceLevel_iff_lattice_stable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (t : K.O) (k : ℕ), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ g N : GLw m w, N.val = GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.O B.A t * B.g) → ((g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) := by
  first | exact @GlobalTheory.TwLat.Lv.level_iff | exact GlobalTheory.TwLat.Lv.level_iff | (intros; apply GlobalTheory.TwLat.Lv.level_iff <;> assumption)
