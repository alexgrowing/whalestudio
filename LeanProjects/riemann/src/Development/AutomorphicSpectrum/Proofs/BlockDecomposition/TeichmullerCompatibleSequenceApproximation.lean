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

variable {l : ℕ} [Fact l.Prime]

private def vv (a : ℕ → Tl l) (f n m : ℕ) : Tl l := a (n + m) ^ l ^ (f * m)

private theorem vv_step (a : ℕ → Tl l) {f : ℕ} {ρ : ℝ} (h : ∀ n, ‖a (n + 1) ^ l ^ f - a n‖ ≤ ρ)
    (n m : ℕ) : ‖vv a f n (m + 1) - vv a f n m‖ ≤ ρ ^ l ^ (f * m) := by
  have e : vv a f n (m + 1) = (a (n + m + 1) ^ l ^ f) ^ l ^ (f * m) := by
    rw [vv, ← pow_mul, ← pow_add, ← add_assoc, mul_add, mul_one, add_comm (f * m) f]
  rw [e, vv, norm_sub_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h _) _

private theorem pow_bound {f : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hf : 0 < f) (m : ℕ) :
    ρ ^ l ^ (f * m) ≤ ρ ^ m := by
  refine pow_le_pow_of_le_one hρ0 hρ1.le ?_
  have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h3 : m ≤ f * m := Nat.le_mul_of_pos_left m hf
  exact h3.trans (Nat.lt_pow_self h2).le

private theorem vv_near (a : ℕ → Tl l) {f : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ n, ‖a (n + 1) ^ l ^ f - a n‖ ≤ ρ) (n m : ℕ) : ‖vv a f n m - a n‖ ≤ ρ := by
  induction m with
  | zero => simpa [vv] using hρ0
  | succ m ih =>
    have e : vv a f n (m + 1) - a n = (vv a f n (m + 1) - vv a f n m) + (vv a f n m - a n) := by
      abel
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
    refine (vv_step a h n m).trans ?_
    exact pow_le_of_le_one hρ0 hρ1.le (pow_pos (Fact.out : l.Prime).pos _).ne'

theorem exists_tilt_lift_compat {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ) (hf : 0 < f)
    (hl : ‖(l : ℂ_[l])‖ ≤ ρ) (hρ1 : ρ < 1) (Z : ℕ → ℂ_[l])
    (hZ : ∀ n, ‖Z n‖ ≤ 1) (hc : ∀ n, ‖Z (n + 1) ^ l ^ f - Z n‖ ≤ ρ) :
    ∃ u : ℕ → Tl l, (∀ n, u (n + 1) ^ l ^ f = u n) ∧ ∀ n, ‖sh (u n) - Z n‖ ≤ ρ := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hl
  choose a ha using fun n => exists_sh_near (l := l) (Z n) (hZ n)
  have ha' : ∀ n, ‖sh (a n) - Z n‖ ≤ ρ := fun n => (ha n).trans hl
  have hd : ∀ n, ‖a (n + 1) ^ l ^ f - a n‖ ≤ ρ := by
    intro n
    refine norm_sub_le_of_near hl ?_
    have h1 := near_pow hl (hZ (n + 1)) (ha' (n + 1)) (l ^ f)
    have e : sh (a (n + 1) ^ l ^ f) - sh (a n) =
        (sh (a (n + 1) ^ l ^ f) - Z (n + 1) ^ l ^ f) +
          ((Z (n + 1) ^ l ^ f - Z n) + -(sh (a n) - Z n)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc n) ?_)
    rw [norm_neg]
    exact ha' n
  have hcau : ∀ n, CauchySeq (vv a f n) := by
    intro n
    refine cauchySeq_of_le_geometric ρ 1 hρ1 fun m => ?_
    rw [dist_comm, dist_eq_norm, one_mul]
    exact (vv_step a hd n m).trans (pow_bound hρ0 hρ1 hf m)
  choose u hu using fun n => cauchySeq_tendsto_of_complete (hcau n)
  refine ⟨u, fun n => ?_, fun n => ?_⟩
  · have h1 : Filter.Tendsto (fun m => vv a f (n + 1) m ^ l ^ f) Filter.atTop
        (nhds (u (n + 1) ^ l ^ f)) := (hu (n + 1)).pow _
    have h2 : Filter.Tendsto (fun m => vv a f n (m + 1)) Filter.atTop (nhds (u n)) :=
      (hu n).comp (Filter.tendsto_add_atTop_nat 1)
    have e : (fun m => vv a f (n + 1) m ^ l ^ f) = fun m => vv a f n (m + 1) := by
      funext m
      rw [vv, vv, ← pow_mul, ← pow_add, mul_add, mul_one, add_comm (f * m) f, add_assoc,
        add_comm 1 m]
    rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  · have h1 : ‖u n - a n‖ ≤ ρ :=
      le_of_tendsto (((hu n).sub_const (a n)).norm)
        (Filter.Eventually.of_forall fun m => vv_near a hρ0 hρ1 hd n m)
    have h2 := near_of_norm_sub_le hl h1
    have e : sh (u n) - Z n = (sh (u n) - sh (a n)) + (sh (a n) - Z n) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (ha' n))

end GlobalTheory.CompanionTheory.LTPer.Tilt
