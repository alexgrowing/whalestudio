import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.StandardSeqPointCompSplitSeqDifferential
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.StabilizerStdSeqIsoGLOfComplement
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GLTransitiveSplitSetOfStableRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ShapiroLemmaTransitiveGroupHomology

noncomputable section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

theorem stab_smul_stdSeq (R : Type) [CommRing R] (n p : ℕ) (h : p ≤ n) (x : GL (Fin (n - p)) R) :
    stab R (n - p) n (Nat.sub_le _ _) x • stdSeq R n p h = stdSeq R n p h := by
  have hmem : stab R (n - p) n (Nat.sub_le n p) x ∈ (stab R (n - p) n (Nat.sub_le n p)).range := ⟨x, rfl⟩
  rw [(GlobalTheory.T.stabilizer_stdSeq_iso_GL_of_complement R n p h).2] at hmem
  exact hmem

theorem firstPage_split : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ,
    ∃ e : ∀ p q, grpH (GL (Fin (n - p)) R) q ⟶ groupHomology (splitRep R n p) q,
      (∀ p q, p + s ≤ n → IsIso (e p q)) ∧
      ∀ p q, p + 1 ≤ n → e (p + 1) q ≫ hMap (splitD R n p) q =
        if Even p then grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ e p q else 0 := by
  intro R _ s hs n
  refine ⟨fun p q => if h : p ≤ n then
      ptH ℤ (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p h) (stab_smul_stdSeq R n p h) q else 0, ?_, ?_⟩
  · intro p q hp
    have h : p ≤ n := by omega
    simp only [dif_pos h]
    exact (GlobalTheory.T.shapiro_lemma_transitive_groupHomology ℤ (GL (Fin n) R) (GL (Fin (n - p)) R) (SplitSet R n p)
      (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p h) (stab_smul_stdSeq R n p h)
      (GlobalTheory.T.stabilizer_stdSeq_iso_GL_of_complement R n p h).1 (GlobalTheory.T.stabilizer_stdSeq_iso_GL_of_complement R n p h).2
      (fun y => GlobalTheory.T.GL_transitive_splitSet_of_stableRangeLe R s hs n p h hp y)).2 q
  · intro p q hp
    have h0 : p ≤ n := by omega
    simp only [dif_pos hp, dif_pos h0]
    exact GlobalTheory.T.standardSeqPoint_comp_splitSeqDifferential R n p q hp (stab_smul_stdSeq R n (p + 1) hp) (stab_smul_stdSeq R n p h0)

end GlobalTheory.HomStab

end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.splitSeq_firstPage_iso_and_differential : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, ∃ e : ∀ p q, grpH (GL (Fin (n - p)) R) q ⟶ groupHomology (splitRep R n p) q, (∀ p q, p + s ≤ n → IsIso (e p q)) ∧ ∀ p q, p + 1 ≤ n → e (p + 1) q ≫ hMap (splitD R n p) q = if Even p then grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ e p q else 0 := by
  first
  | exact @GlobalTheory.HomStab.firstPage_split
  | exact @GlobalTheory.HomStab.stab_smul_stdSeq
end
