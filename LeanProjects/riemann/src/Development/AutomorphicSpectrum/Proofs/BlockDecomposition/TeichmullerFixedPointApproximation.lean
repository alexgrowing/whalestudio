import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem exists_fixed_near : ∀ {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ), 0 < f → ‖(l : ℂ_[l])‖ ≤ ρ → ρ < 1 → ∀ c : ℂ_[l],
    ‖c‖ ≤ 1 → ‖c ^ l ^ f - c‖ ≤ ρ → ∃ y : Tl l, y ^ l ^ f = y ∧ ‖sh y - c‖ ≤ ρ := by
  intro l _ f ρ hf hρ hρ1 c hc hcf
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  obtain ⟨a, ha⟩ := exists_sh_near c hc
  have ha' : ‖sh a - c‖ ≤ ρ := ha.trans hρ
  have hq1 : 1 ≤ l ^ f := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hq2 : 2 ≤ l ^ f := Nat.one_lt_pow hf.ne' (Fact.out : l.Prime).one_lt

  have h0 : ‖a ^ l ^ f - a‖ ≤ ρ := by
    refine norm_sub_le_of_near hρ ?_
    have e : sh (a ^ l ^ f) - sh a =
        (sh (a ^ l ^ f) - c ^ l ^ f) + ((c ^ l ^ f - c) + -(sh a - c)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (near_pow hρ hc ha' _) ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hcf ?_)
    rwa [norm_neg]
  let u : ℕ → Tl l := fun n => a ^ l ^ (f * n)
  have hstep : ∀ n, u (n + 1) = u n ^ l ^ f := by
    intro n
    show a ^ l ^ (f * (n + 1)) = (a ^ l ^ (f * n)) ^ l ^ f
    rw [← pow_mul, ← pow_add, Nat.mul_succ]
  have hdiff : ∀ n, ‖u (n + 1) - u n‖ ≤ ρ ^ (l ^ (f * n)) := by
    intro n
    have e : u (n + 1) - u n = (a ^ l ^ f) ^ l ^ (f * n) - a ^ l ^ (f * n) := by
      show a ^ l ^ (f * (n + 1)) - a ^ l ^ (f * n) = _
      rw [← pow_mul, ← pow_add, Nat.mul_succ, Nat.add_comm]
    rw [e, norm_sub_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h0 _
  have hdiff1 : ∀ n, ‖u (n + 1) - u n‖ ≤ ρ := by
    intro n
    refine (hdiff n).trans ?_
    have : 1 ≤ l ^ (f * n) := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
    simpa using pow_le_pow_of_le_one hρ0 hρ1.le this
  have hgeom : ∀ n, dist (u n) (u (n + 1)) ≤ 1 * ρ ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, one_mul]
    refine (hdiff n).trans (pow_le_pow_of_le_one hρ0 hρ1.le ?_)
    have h1 : n < l ^ n := Nat.lt_pow_self (Fact.out : l.Prime).one_lt
    have h2 : l ^ n ≤ l ^ (f * n) :=
      Nat.pow_le_pow_right (Fact.out : l.Prime).pos (Nat.le_mul_of_pos_left n hf)
    omega
  have hcau : CauchySeq u := cauchySeq_of_le_geometric ρ 1 hρ1 hgeom
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcau
  have hclose : ∀ n, ‖u n - a‖ ≤ ρ := by
    intro n
    induction n with
    | zero => simpa [u] using hρ0
    | succ n ih =>
      have e : u (n + 1) - a = (u (n + 1) - u n) + (u n - a) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hdiff1 n) ih)
  have hya : ‖y - a‖ ≤ ρ :=
    le_of_tendsto ((hy.sub_const a).norm) (Filter.Eventually.of_forall hclose)
  refine ⟨y, ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun n => u n ^ l ^ f) Filter.atTop (nhds (y ^ l ^ f)) := hy.pow _
    have h2 : Filter.Tendsto (fun n => u n ^ l ^ f) Filter.atTop (nhds y) := by
      simpa only [hstep] using (Filter.tendsto_add_atTop_iff_nat 1).2 hy
    exact tendsto_nhds_unique h1 h2
  · have e : sh y - c = (sh y - sh a) + (sh a - c) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (near_of_norm_sub_le hρ hya) ha')

end GlobalTheory.CompanionTheory.LTPer.Tilt
