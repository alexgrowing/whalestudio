import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIwahoriFirstIdentityStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.IwFacts

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel Matrix

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

section General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tl_iw_goodT_two (n : ℕ) (θ : MulAut (GL (Fin n) k)) (t : GL (Fin n) k) (ht : t ∈ PositivityTheory.Lbc.Tor k n)
    (hinc : PositivityTheory.Lbc.IncrV k n t) (hθt : θ t ∈ PositivityTheory.Lbc.Tor k n) (hinc' : PositivityTheory.Lbc.IncrV k n (θ t))
    (hN : PositivityTheory.Lbc.IncrV k n (t * θ t)) : PositivityTheory.Lbc.GoodT k n (iwahori k (Fin n)) θ 2 t := by
  refine ⟨ht, fun i hi => ?_, ?_⟩
  · interval_cases i
    · simpa using (iw_domT_strDomT n t ht hinc).1
    · simpa using (iw_domT_strDomT n (θ t) hθt hinc').1
  · have e : PositivityTheory.Lbc.tnorm θ 2 t = t * θ t := by
      simp [PositivityTheory.Lbc.tnorm, List.ofFn_succ]
    rw [e]
    exact (iw_domT_strDomT n _ (Subgroup.mul_mem _ ht hθt) hN).2

end General

section Completion

open NumberField IsDedekindDomain GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tl_tdiag_mul {w : Pl E} {n : ℕ} (ϖ : (w.adicCompletion E)ˣ) (a b : Fin n → ℤ) :
    GlobalTheory.BCT.tdiag ϖ a * GlobalTheory.BCT.tdiag ϖ b = GlobalTheory.BCT.tdiag ϖ (a + b) := by
  unfold GlobalTheory.BCT.tdiag
  rw [← map_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply, Pi.add_apply]
  exact (_root_.zpow_add ϖ (a i) (b i)).symm

private theorem valued_v_lt_one_of_ordL_eq_one (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : ordL (ϖ : w.adicCompletion E) = 1) :
    Valued.v (ϖ : w.adicCompletion E) < 1 := by
  have h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0 := by simp
  unfold ordL at hϖ
  rw [dif_neg h0] at hϖ
  have h1 : Multiplicative.toAdd (WithZero.unzero h0) = -1 := by linarith
  have h2 : WithZero.unzero h0 = Multiplicative.ofAdd (-1 : ℤ) := by rw [← h1]; rfl
  rw [← WithZero.coe_unzero h0, h2, ← WithZero.coe_one, WithZero.coe_lt_coe]
  exact Multiplicative.ofAdd_lt.mpr (by norm_num)

private theorem incrV_tdiag_of_strictAnti_of_ordL_eq_one (w : Pl E) (n : ℕ) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : ordL (ϖ : w.adicCompletion E) = 1) (a : Fin n → ℤ) (ha : StrictAnti a) :
    PositivityTheory.Lbc.IncrV (w.adicCompletion E) n (GlobalTheory.BCT.tdiag ϖ a) := by
  show PositivityTheory.Lbc.IncrV _ n (diagT _ (Fin n) fun i => ϖ ^ a i)
  apply diagT_incrV
  intro i j hij
  rw [(ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).lt_iff_lt]
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  have hpos : 0 < Valued.v (ϖ : w.adicCompletion E) := by
    rw [zero_lt_iff]
    simp
  exact zpow_lt_zpow_right_of_lt_one₀ hpos (valued_v_lt_one_of_ordL_eq_one w ϖ hϖ) (ha hij)

theorem tl_goodT_of (w : Pl E) (n : ℕ) (θ : MulAut (GLw n w)) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : ordL (ϖ : w.adicCompletion E) = 1) (y : Fin n → ℤ) (hy : StrictAnti y)
    (hθ : θ (GlobalTheory.BCT.tdiag ϖ y) = GlobalTheory.BCT.tdiag ϖ (fun i => -y (Fin.rev i))) :
    PositivityTheory.Lbc.GoodT (w.adicCompletion E) n (iwGL n w) θ 2 (GlobalTheory.BCT.tdiag ϖ y) := by
  have hrev : StrictAnti (fun i => -y (Fin.rev i)) := fun i j hij =>
    neg_lt_neg (hy (Fin.rev_lt_rev.mpr hij))
  have hsum : StrictAnti (y + fun i => -y (Fin.rev i)) := hy.add hrev
  have h1 : θ (GlobalTheory.BCT.tdiag ϖ y) ∈ PositivityTheory.Lbc.Tor (w.adicCompletion E) n := by
    rw [hθ]
    exact diagT_mem_Tor n _
  have h2 : PositivityTheory.Lbc.IncrV (w.adicCompletion E) n (θ (GlobalTheory.BCT.tdiag ϖ y)) := by
    rw [hθ]
    exact incrV_tdiag_of_strictAnti_of_ordL_eq_one w n ϖ hϖ _ hrev
  have h3 : PositivityTheory.Lbc.IncrV (w.adicCompletion E) n (GlobalTheory.BCT.tdiag ϖ y * θ (GlobalTheory.BCT.tdiag ϖ y)) := by
    rw [hθ, tl_tdiag_mul]
    exact incrV_tdiag_of_strictAnti_of_ordL_eq_one w n ϖ hϖ _ hsum
  exact tl_iw_goodT_two n θ (GlobalTheory.BCT.tdiag ϖ y) (diagT_mem_Tor n _) (incrV_tdiag_of_strictAnti_of_ordL_eq_one w n ϖ hϖ y hy) h1 h2 h3

theorem tl_contr_of (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : ordL (ϖ : w.adicCompletion E) = 1) (n : ℕ)
    (θ : MulAut (GLw n w)) (hadm : PositivityTheory.Lbc.admitted (w.adicCompletion E) n (iwGL n w) θ 2)
    (y : Fin n → ℤ) (hy : StrictAnti y)
    (hθ : θ (GlobalTheory.BCT.tdiag ϖ y) = GlobalTheory.BCT.tdiag ϖ (fun i => -y (Fin.rev i)))
    (δ : GLw n w) (hδ : GlobalTheory.BCT.dcos n w (GlobalTheory.BCT.tdiag ϖ y) δ ≠ 0) :
    ∃ m ∈ iwGL n w, ∃ τ ∈ TO n w, m⁻¹ * δ * θ m = GlobalTheory.BCT.tdiag ϖ y * τ := by
  have hmem : δ ∈ PositivityTheory.Lbc.dcos (iwGL n w) (GlobalTheory.BCT.tdiag ϖ y) := by
    unfold GlobalTheory.BCT.dcos at hδ
    split_ifs at hδ with h
    · exact h
    · exact absurd rfl hδ
  obtain ⟨j, hj, κ, hκ, hg⟩ := (GlobalTheory.T.twisted_iwahori_first_identity (k := w.adicCompletion E)) n (iwGL n w) θ 2 (GlobalTheory.BCT.tdiag ϖ y)
    hadm (tl_goodT_of w n θ ϖ hϖ y hy hθ) δ hmem
  refine ⟨j⁻¹, (iwGL n w).inv_mem hj, κ, iw_tor_TO w n κ hκ, ?_⟩
  rw [hg, map_inv]
  group

end Completion

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
