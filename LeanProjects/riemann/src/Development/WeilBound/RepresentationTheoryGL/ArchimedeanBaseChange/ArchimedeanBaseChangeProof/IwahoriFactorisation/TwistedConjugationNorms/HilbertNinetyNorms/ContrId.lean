import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.IwFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIwahoriFirstIdentityStatement

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_dcos_of_ne (w : Pl E) (n : ℕ) (t δ : GLw n w) (hδ : dcos n w t δ ≠ 0) :
    δ ∈ PositivityTheory.Lbc.dcos (iwGL n w) t := by
  unfold dcos at hδ
  split_ifs at hδ with h
  · exact h
  · exact absurd rfl hδ

private theorem apply_eq_zero_of_mem_tor_of_ne {k : Type} [Field k] (N : ℕ) (x : GL (Fin N) k) (hx : x ∈ PositivityTheory.Lbc.Tor k N)
    (i j : Fin N) (h : i ≠ j) : (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨s, rfl⟩ := hx
  simp [PositivityTheory.Lbc.torEmb, GlobalTheory.SmGL.leviEmb, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hne : ((GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm i).1 ≠ ((GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm j).1 := by
    intro hfst
    apply h
    have hs : (GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm i = (GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm j := by
      refine Sigma.ext hfst ?_
      apply (Fin.heq_ext_iff (congrArg _ hfst)).2
      have h1 : (((GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm i).2 : ℕ) < 1 :=
        ((GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm i).2.isLt
      have h2 : (((GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm j).2 : ℕ) < 1 :=
        ((GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)).symm j).2.isLt
      omega
    simpa using congrArg (GlobalTheory.SmGL.stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N)) hs
  convert Matrix.blockDiagonal'_apply_ne (fun (a : Fin N) ↦ (s a).val) _ _ hne

private theorem mem_TO_of_mem_iwGL_inf_tor (w : Pl E) (n : ℕ) (κ : GLw n w)
    (hκ : κ ∈ iwGL n w ⊓ PositivityTheory.Lbc.Tor (w.adicCompletion E) n) : κ ∈ TO n w := by
  refine ⟨fun i j hij => apply_eq_zero_of_mem_tor_of_ne n κ hκ.2 i j hij, fun i => ?_⟩
  have hmul : κ.val i i * (κ⁻¹ : GLw n w).val i i = 1 := by
    have h1 : (κ * κ⁻¹ : GLw n w).val i i = 1 := by simp
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · exact h1
    · intro b _ hb
      rw [apply_eq_zero_of_mem_tor_of_ne n κ hκ.2 i b (Ne.symm hb), zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have ha := iw_entry_le hκ.1 i i
  have hb := iw_entry_le (inv_mem hκ.1) i i
  have hv : ValuativeRel.valuation _ (κ.val i i) = 1 := by
    have hm := congrArg (ValuativeRel.valuation (w.adicCompletion E)) hmul
    rw [map_mul, map_one] at hm
    refine le_antisymm ha ?_
    calc (1 : ValuativeRel.ValueGroupWithZero _) = _ := hm.symm
      _ ≤ _ * 1 := by gcongr
      _ = _ := mul_one _
  haveI := Valuation.Compatible.ofValuation (Valued.v : Valuation (w.adicCompletion E) _)
  exact (ValuativeRel.isEquiv (Valued.v : Valuation (w.adicCompletion E) _)
    (ValuativeRel.valuation _)).eq_one_iff_eq_one.2 hv

theorem contr_id_pf (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (n : ℕ) (y : Fin n → ℤ)
    (hy : StrictAnti y) (δ : GLw n w) (hδ : dcos n w (tdiag ϖ y) δ ≠ 0) :
    ∃ m ∈ iwGL n w, ∃ τ ∈ TO n w, m⁻¹ * δ * m = tdiag ϖ y * τ := by
  obtain ⟨j, hj, κ, hκ, he⟩ := GlobalTheory.T.twisted_iwahori_first_identity n (iwGL n w) 1 1 (tdiag ϖ y) (iwahori_GL_trivial_admissible w n)
    (goodT_id w ϖ hϖ n y hy) δ (mem_dcos_of_ne w n _ δ hδ)
  refine ⟨j⁻¹, inv_mem hj, κ, mem_TO_of_mem_iwGL_inf_tor w n κ hκ, ?_⟩
  simp only [inv_inv, MulAut.one_apply] at he ⊢
  rw [he]
  group

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
