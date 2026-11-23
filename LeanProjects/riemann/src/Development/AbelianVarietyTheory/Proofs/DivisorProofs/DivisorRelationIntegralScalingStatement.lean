import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorRelationIntegralScaling
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_relation_integral_scaling : ∀ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {Φ : s.Flag} {hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)} {h0 : RefMets Φ} (P : PolDat s Φ hm h0) (k : s.Comp), ∃ (d : ℕ) (kb ka : ℤ) (kx : DV.Rt D.what₂.Tau N → ℤ), 0 < d ∧ (kb : ℝ) = d ∧ (ka : ℝ) = d * (((P.ab k).n : ℕ) : ℝ)⁻¹ ∧ (∀ x, (kx x : ℝ) = d * P.dir x.1 x.2) ∧ kb • P.bd k + ka • (P.ab k).D + ∑ x, kx x • divOf (Φ.C k) (rootExp S x) = 0 := by
  first | exact @GlobalTheory.ShFam.PolDat.exists_intRel_bd_ab_roots | exact GlobalTheory.ShFam.PolDat.exists_intRel_bd_ab_roots | (intros; apply GlobalTheory.ShFam.PolDat.exists_intRel_bd_ab_roots <;> assumption)
