import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import Formalism.LocalRingCardinality.ConjSqrtMinusD

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cuspTie : CuspTieSt := by
  intro D T h j hj w hlast x P hP f hf
  exact h.thCusp j hj _ _ (dom_wtA w) hlast f ⟨x, P, hP, hf⟩

lemma sum_extendByZero_le_sum {p : ℕ} (g : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, ext0 g i ≤ ∑ i : Fin p, g i := by
  unfold ext0
  have hF : ∀ n : ℕ, (∑ i : Fin n, (if h : (i : ℕ) < p then g ⟨i, h⟩ else 0)) =
      ∑ k ∈ Finset.range n, (if h : k < p then g ⟨k, h⟩ else 0) := fun n =>
    Fin.sum_univ_eq_sum_range (fun k => if h : k < p then g ⟨k, h⟩ else 0) n
  have hg : (∑ i : Fin p, g i) = ∑ i : Fin p, (if h : (i : ℕ) < p then g ⟨i, h⟩ else 0) :=
    Finset.sum_congr rfl (fun i _ => by simp)
  rw [hg, hF m, hF p]
  calc ∑ k ∈ Finset.range m, (if h : k < p then g ⟨k, h⟩ else 0)
      ≤ ∑ k ∈ Finset.range (max m p), (if h : k < p then g ⟨k, h⟩ else 0) :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_left m p))
    _ = ∑ k ∈ Finset.range p, (if h : k < p then g ⟨k, h⟩ else 0) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (le_max_right m p))
        intro k _ hk
        rw [Finset.mem_range] at hk
        rw [dif_neg hk]

open Classical in
lemma sum_single_embedding_extend_le {E : Type} [Field E] [NumberField E] (e : E →+* ℂ) (mult : (E →+* ℂ) → ℕ) {p : ℕ}
    (g : Fin p → ℕ) :
    ∑ τ : E →+* ℂ, ∑ i : Fin (mult τ), (if τ = e then ext0 g i else 0) ≤ ∑ i, g i := by
  rw [Finset.sum_eq_single e]
  · simp only [eq_self_iff_true, if_true]
    exact sum_extendByZero_le_sum g (mult e)
  · intro τ _ hτ
    exact Finset.sum_eq_zero (fun i _ => if_neg hτ)
  · intro h
    exact absurd (Finset.mem_univ e) h

open Classical in
lemma DF_wtA_le {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H)
    (w : WeightFamilies.Wt D j) :
    DF Dw (wtA w) ≤ ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) := by
  have hswap : ∀ F : (τ : D.host.E →+* ℂ) → Fin (Dw.mult τ) → D.what₂.Tau → ℕ,
      ∑ τ, ∑ i : Fin (Dw.mult τ), ∑ t, F τ i t = ∑ t, ∑ τ, ∑ i : Fin (Dw.mult τ), F τ i t := by
    intro F
    calc ∑ τ, ∑ i : Fin (Dw.mult τ), ∑ t, F τ i t = ∑ τ, ∑ t, ∑ i : Fin (Dw.mult τ), F τ i t :=
          Finset.sum_congr rfl (fun τ _ => Finset.sum_comm)
      _ = ∑ t, ∑ τ, ∑ i : Fin (Dw.mult τ), F τ i t := Finset.sum_comm
  unfold Formalism.L2.Pj.DF wtA
  rw [hswap]
  apply Finset.sum_le_sum
  intro t _
  simp only [Finset.sum_add_distrib]
  exact add_le_add (by convert sum_single_embedding_extend_le (DV.tauEmb D t) Dw.mult (w.aP t))
    (by convert sum_single_embedding_extend_le (conjEmb (DV.tauEmb D t)) Dw.mult (w.aM t))

theorem deg : DegSt := by
  intro D T h j hj w P hP
  have hrow := hP.1.2.2
  have h1 : P.totalDegree ≤ DF (T.Q.Dw j) (wtA w) := by
    refine Finset.sup_le (fun m hm => ?_)
    rw [Finsupp.sum_fintype _ _ (by simp)]
    rw [Fintype.sum_sigma]
    refine le_of_eq (Finset.sum_congr rfl (fun σ _ => ?_))
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => hrow m hm σ i)
  have h2 := DF_wtA_le (T.Q.Dw j) w
  have h3 : (((∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) : ℕ)) : ℝ) = absA w := by
    simp [absA]
  rw [← h3]
  exact_mod_cast h1.trans h2

theorem dimPos_fr (D : D7) : 1 ≤ D.R.f ∧ 1 ≤ D.R.r := by
  refine ⟨?_, ?_⟩
  · have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    exact le_trans (by omega : 1 ≤ D.R.m) h2
  · have h3 := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1
