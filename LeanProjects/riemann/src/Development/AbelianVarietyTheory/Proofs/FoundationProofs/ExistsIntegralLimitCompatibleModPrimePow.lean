import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallNormLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

variable {l : ℕ} [Fact l.Prime]

theorem norm_l_pow_anti {m n : ℕ} (h : n ≤ m) :
    ‖((l : ℕ) : Qbar l) ^ m‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_natCast_l_lt_one.le h

theorem isCompact_coef (c : Coef l) : IsCompact (c.O : Set (Qbar l)) := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  let f : (Fin k → ℤ_[l]) → Qbar l :=
    fun v => ∑ i, algebraMap ℤ_[l] (Qbar l) (v i) * (s i : Qbar l)
  have hcont : Continuous f := by
    have ha : Continuous (algebraMap ℤ_[l] (Qbar l)) := by
      have : ⇑(algebraMap ℤ_[l] (Qbar l)) = fun a : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) := by
        funext a; exact IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) a
      rw [this]
      exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
    exact continuous_finset_sum _ fun i _ => (ha.comp (continuous_apply i)).mul continuous_const
  have heq : (c.O : Set (Qbar l)) = Set.range f := by
    ext x
    constructor
    · intro hx
      have hmem : (⟨x, hx⟩ : c.O) ∈ Submodule.span ℤ_[l] (Set.range s) := by rw [hs]; trivial
      obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 hmem
      refine ⟨v, ?_⟩
      have := congrArg (fun y : c.O => (y : Qbar l)) hv
      simp only [AddSubmonoidClass.coe_finset_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Algebra.smul_def]
      rfl
    · rintro ⟨v, rfl⟩
      exact c.O.sum_mem fun i _ => c.O.mul_mem (c.O.algebraMap_mem _) (s i).2
  rw [heq]
  exact isCompact_range hcont

theorem cg_of_le {a : ℕ → Qbar l} (h : ∀ n, Cg n (a (n + 1)) (a n)) {n m : ℕ} (hnm : n ≤ m) :
    Cg n (a m) (a n) := by
  induction m, hnm using Nat.le_induction with
  | base => unfold Cg; simp
  | succ m hm ih =>
    have h1 : Cg n (a (m + 1)) (a m) := by
      unfold Cg at *; exact (h m).trans (norm_l_pow_anti hm)
    exact cg_trans h1 ih

theorem exists_limit_coef : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (X : Type) (a : ℕ → X → Qbar l),
    (∀ n x, a n x ∈ c.O) → (∀ n x, Cg n (a (n + 1) x) (a n x)) →
    ∃ z : X → Qbar l, (∀ x, z x ∈ c.O) ∧ ∀ n x, Cg n (z x) (a n x) := by
  intro l _ c X a hO hC
  have key : ∀ x, ∃ y ∈ (c.O : Set (Qbar l)), ∀ n, Cg n y (a n x) := by
    intro x
    have hle : ∀ n m, n ≤ m → ‖a m x - a n x‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ :=
      fun n m h => cg_of_le (a := fun k => a k x) (fun k => hC k x) h
    have hcs : CauchySeq (fun m => a m x) := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨N, hN⟩ := (tendsto_norm_l_pow (l := l)).eventually (gt_mem_nhds hε) |>.exists_forall_of_atTop
      refine ⟨N, fun m hm => ?_⟩
      rw [dist_eq_norm]
      exact (hle N m hm).trans_lt (hN N le_rfl)
    obtain ⟨y, hy, hlim⟩ := cauchySeq_tendsto_of_isComplete (isCompact_coef c).isComplete
      (fun m => hO m x) hcs
    refine ⟨y, hy, fun n => ?_⟩
    unfold Cg
    have ht : Filter.Tendsto (fun m => ‖a m x - a n x‖) Filter.atTop (nhds ‖y - a n x‖) :=
      (hlim.sub_const _).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨n, fun m hm => hle n m hm⟩)
  choose z hz using key
  exact ⟨z, fun x => (hz x).1, fun n x => (hz x).2 n⟩

end GlobalTheory.Ord2

end
