import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LocAddOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

theorem UpperTheory.Reformulated.B.Glb2.fock_dec_k :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {d : PositivityTheory.SiegelWeilFormula.SD_k σ} (R : PositivityTheory.SiegelWeilFormula.RD_k d)
      (w : NumberField.InfinitePlace F),
      ∀ f ∈ R.fock,
        ∃ (k : ℕ) (P : Fin k → PositivityTheory.Rg.Sw.PX d.m d.n) (Ψ : Fin k → PositivityTheory.SiegelWeilFormula.Mx F E d.m d.n → ℂ),
          (∀ (i : Fin k), Ψ i ∈ R.away w) ∧ f = ∑ i : Fin k, R.tens w (PositivityTheory.SiegelWeilFormula.fP (P i)) (Ψ i) := by
  intro F E _ _ _ _ _ σ d R w f hf
  obtain ⟨k, c, u, rfl⟩ := Submodule.mem_span_set'.1 hf
  choose P g hg hu using fun i => (u i).2
  refine ⟨k, fun i => P i w, fun i => c i • _, fun i => Submodule.smul_mem _ (c i)
    (Submodule.subset_span ⟨P i, g i, hg i, rfl⟩), Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hu i]
  funext X
  simp only [PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm (PositivityTheory.SiegelWeilFormula.fP _ _), ← mul_assoc (PositivityTheory.SiegelWeilFormula.fP _ _),
    @Finset.mul_prod_erase _ _ _ (_) _ (fun v => PositivityTheory.SiegelWeilFormula.fP (P i v) (R.loc v X)) _
      (Finset.mem_univ w)]
