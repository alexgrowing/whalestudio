import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem record_facts : ∀ (D : D7) (u : D.what₂.Word), SplitsIn D.host.E (D.mem u).A.T ∧ (∀ i, SplitsIn D.host.E (D.host.g i)) ∧ (∀ i, (D.mem u).A.T ≠ D.host.g i) ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ D.R.N 0 = D.R.k ∧ IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧ (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  intro D u
  refine ⟨(GlobalTheory.HostSplit.split_of_one_mod D.R D.host _ (D.mem u).A.T_prime (D.T_mod_cond u)).1,
    D.nd.g_split, D.T_ne_g u, ?_, D.R.N_zero, ?_,
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D 0 (Nat.zero_le _)).ne_zero⟩
  · rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
    ring
  · let _ := D.host.cmStar
    have h := D.sp.baseGram_isHermitian
    refine Matrix.ext fun i j => ?_
    exact congrFun (congrFun h (Fin.cast D.R.N_zero i)) (Fin.cast D.R.N_zero j)

end GlobalTheory.St.G
