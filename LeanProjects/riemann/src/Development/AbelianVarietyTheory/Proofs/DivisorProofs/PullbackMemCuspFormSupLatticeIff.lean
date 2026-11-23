import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NvalNonnegIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIffStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CovTop.PullLat

variable {D : D7}

theorem levPull_of_pull {T : Core D} {j : ℕ} (Y : Deep T j) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : T.R j}
    (hf : f ∈ sec (T.Q.Xo j) T.Q.c a n) {g : Rul Y.d.Xo₂ Y.d.c₂} (hp : Y.Pull f g) :
    GlobalTheory.LevPull.Pull Y.d (GlobalTheory.FieldBC.rulBC Y.hle f) g := by
  intro k _ _ _ _ hk y₂ y hov
  letI : Algebra T.Q.c.F k := GlobalTheory.FieldBC.resAlg Y.hle k
  have ho : AlgOver T.Q.c Y.c' Y.hle k := fun _ => rfl
  rw [((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ _ _ _ Y.hle).1 a n f hf).2 k ho y]
  exact hp k ho hk y₂ y (y.res Y.hle ho) hov rfl rfl HEq.rfl

theorem pull_mem_latW : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j →
    Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n))
      (g : Y.V (wtZ a n)), Y.Pull f g → (g ∈ latW Y.U (wtZ a n) ↔ f ∈ latW (T.U j) (wtZ a n)) := by
  intro D T j Y e o hT hj hY a n f g hp
  have hpos := GlobalTheory.CovTop.Inhab.rank_pos T.toCore hT.pins j hj
  have hfs : (f : T.R j) ∈ sec (T.Q.Xo j) T.Q.c a n := by
    have h : (f : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) a n := by rw [← cuspW_wtZ]; exact f.2
    exact cusp_le_sec _ _ _ _ _ h
  have hgs : (g : Rul Y.d.Xo₂ Y.d.c₂) ∈ sec Y.d.Xo₂ Y.d.c₂ a n := by
    have h : (g : Rul Y.d.Xo₂ Y.d.c₂) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by rw [← cuspW_wtZ]; exact g.2
    exact cusp_le_sec _ _ _ _ _ h
  have hfs' := ((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ (T.Q.Xo j) _ _ Y.hle).1 a n _ hfs).1
  have hL := GlobalTheory.LevGeo.laws_core D T j hT hj
  have hne : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  have h1 := GlobalTheory.CoverInt.pull_intAt_iff _ _ _ _ _ _ Y.d hpos hY.lev.1 (Or.inl ⟨hne, hL.levA⟩) a n _ hfs' _ hgs (levPull_of_pull Y hfs hp)
  have h2 := GlobalTheory.T.isIntegralRule_ruleBaseChangeCoeffField_iff _ _ _ _ _ _ _ Y.hle a n _ hfs
  exact h1.trans h2

end GlobalTheory.CovTop.PullLat
