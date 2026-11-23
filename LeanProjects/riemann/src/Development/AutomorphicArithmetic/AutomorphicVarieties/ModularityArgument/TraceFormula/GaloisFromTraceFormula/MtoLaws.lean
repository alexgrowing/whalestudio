import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem rel_comp {r s t : ℂ → ℂ → Prop} (h : ∀ x y z, r x y → s y z → t x z)
    {a b c : Multiset ℂ} (hab : Multiset.Rel r a b) :
    Multiset.Rel s b c → Multiset.Rel t a c := by
  induction hab generalizing c with
  | zero =>
    intro h0
    rw [Multiset.rel_zero_left] at h0
    subst h0
    exact Multiset.Rel.zero
  | cons hxy _ ih =>
    intro hc
    obtain ⟨z, zs, hz, hzs, rfl⟩ := Multiset.rel_cons_left.1 hc
    exact Multiset.Rel.cons (h _ _ _ hxy hz) (ih hzs)

private theorem exists_sep (S : Finset (ℂ × ℂ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ S, p.1 ≠ p.2 → ε < ‖p.1 - p.2‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert p S _ ih =>
    obtain ⟨ε, h0, hε⟩ := ih
    by_cases hp : p.1 = p.2
    · refine ⟨ε, h0, fun q hq hne => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact absurd hp hne
      · exact hε q hq hne
    · have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hp)
      refine ⟨min ε (‖p.1 - p.2‖ / 2), lt_min h0 (half_pos hpos), fun q hq hne => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact (min_le_right _ _).trans_lt (half_lt_self hpos)
      · exact (min_le_left _ _).trans_lt (hε q hq hne)

private theorem eq_of_rel {a b : Multiset ℂ}
    (h : ∀ ε : ℝ, 0 < ε → Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) a b) : a = b := by
  classical
  obtain ⟨ε, h0, hε⟩ := exists_sep (a.toFinset ×ˢ b.toFinset)
  refine Multiset.rel_eq.1 ((h ε h0).mono fun x hx y hy hxy => ?_)
  by_contra hne
  exact absurd hxy (not_le.2 (hε (x, y) (by simp [hx, hy]) hne))

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.mtoLaws :
    MToLaws := by
  intro E _ _ _
  refine ⟨fun m x y hx hy => ?_, fun m x z z₀ hx hz τ ε hε => ?_,
    fun m m' x x' hx hx' τ ε hε => ?_⟩
  · funext τ
    refine eq_of_rel fun ε hε => ?_
    obtain ⟨k, h1, h2⟩ := ((hx τ (ε / 2) (half_pos hε)).and (hy τ (ε / 2) (half_pos hε))).exists
    refine rel_comp (fun p q w (hpq : ‖q - p‖ ≤ ε / 2) (hqw : ‖q - w‖ ≤ ε / 2) => ?_)
      (Multiset.rel_flip.2 h1) h2
    calc ‖p - w‖ = ‖(q - w) - (q - p)‖ := by congr 1; ring
      _ ≤ ‖q - w‖ + ‖q - p‖ := norm_sub_le _ _
      _ ≤ ε := by linarith
  · have hz' : ∀ᶠ k in atTop, ‖z k - z₀‖ ≤ ε / 2 :=
      (Metric.tendsto_nhds.1 hz (ε / 2) (half_pos hε)).mono fun k hk => by
        rw [dist_eq_norm] at hk
        exact hk.le
    filter_upwards [hx τ (ε / 2) (half_pos hε), hz'] with k h1 h2
    refine Multiset.rel_map.2 (h1.mono fun p _ q _ hpq => ?_)
    calc ‖(p + z k) - (q + z₀)‖ = ‖(p - q) + (z k - z₀)‖ := by congr 1; ring
      _ ≤ ‖p - q‖ + ‖z k - z₀‖ := norm_add_le _ _
      _ ≤ ε := by linarith
  · filter_upwards [hx τ ε hε, hx' τ ε hε] with k h1 h2
    exact h1.add h2
