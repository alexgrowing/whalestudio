import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSatEqOfIsCT

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

private theorem sc_scale (A : Multiset ℂˣ) (c : ℂˣ) (k : ℕ) :
    ((A.map (· * c)).map fun b : ℂˣ => (b : ℂ)).esymm k =
      (c : ℂ) ^ k * (A.map fun b : ℂˣ => (b : ℂ)).esymm k := by
  rw [← smul_eq_mul, Multiset.pow_smul_esymm]
  simp [Multiset.map_map, mul_comm]

private theorem sc_const (q n i : ℕ) : ∃ a : ℂ, (q ≠ 0 → a ≠ 0) ∧
    ∀ B : Multiset ℂˣ, satEig q n B i = a * (B.map fun b : ℂˣ => (b : ℂ)).esymm i := by
  refine ⟨(q : ℂ) ^ (((i : ℂ) * ((n : ℂ) - i)) / 2), fun hq => ?_, fun B => by rw [satEig]⟩
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => hq' h.1

private theorem sc_lim {q n : ℕ} (hq : q ≠ 0) {B : ℕ → Multiset ℂˣ} {C : Multiset ℂˣ} (h : STo q n B C) (i : ℕ) :
    Tendsto (fun k => ((B k).map fun b : ℂˣ => (b : ℂ)).esymm i) atTop
      (𝓝 ((C.map fun b : ℂˣ => (b : ℂ)).esymm i)) := by
  obtain ⟨a, ha, e⟩ := sc_const q n i
  have := (h i).const_mul a⁻¹
  simpa only [e, inv_mul_cancel_left₀ (ha hq)] using this

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.satComb :
    SatComb := by
  refine ⟨fun q n B c c₀ hc i => ?_, fun q r s B₁ B₂ C₁ C₂ α β hq h₁ h₂ j => ?_⟩
  · obtain ⟨a, -, e⟩ := sc_const q n i
    simp only [e, sc_scale]
    exact ((hc.pow i).mul_const _).const_mul a
  · obtain ⟨a, -, e⟩ := sc_const q (r + s) j
    simp only [e, Multiset.map_add, GlobalTheory.ResW.SatWordAt.esymm_add, sc_scale]
    exact (tendsto_finset_sum _ fun p _ =>
      ((sc_lim hq h₁ p.1).const_mul _).mul ((sc_lim hq h₂ p.2).const_mul _)).const_mul a
