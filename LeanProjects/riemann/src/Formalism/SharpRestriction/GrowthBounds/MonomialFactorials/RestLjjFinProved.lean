import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiAddLeft
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankLjjSpan
import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.G.CountingStatementReduction

section Lvl

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem mem_xiMons_of (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ)
    (hsupp : ∀ v ∈ m.support, ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c)
    (hsum : ∑ c, m (Formalism.GM.M.xiVar N r G.T.t c) = n) : m ∈ xiMons (r := r) G n := by
  classical
  unfold xiMons
  rw [Finset.mem_image]
  refine ⟨fun c => m (Formalism.GM.M.xiVar N r G.T.t c), (CountingStatementReduction.mem_Ev _).2 hsum, ?_⟩
  ext v
  rw [Finsupp.finsetSum_apply]
  by_cases hv : ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c
  · obtain ⟨c, rfl⟩ := hv
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hd (xiVar_inj G h)
    · intro h; exact absurd (Finset.mem_univ c) h
  · have h0 : m v = 0 := by
      by_contra hne
      exact hv (hsupp v (Finsupp.mem_support_iff.2 hne))
    rw [h0]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hv ⟨c, h.symm⟩

theorem xi_mem_spanZ (n : ℕ) (g : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (hg : g ∈ Formalism.GM.M.XiPolZ p N r G.T.t n) :
    g ∈ Submodule.span ℤ_[p] ((fun m => (monomial m (1 : ℚ_[p]))) '' (xiMons (r := r) G n : Set _)) := by
  classical
  obtain ⟨hs, hint⟩ := Submodule.mem_inf.1 hg
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at hs
  obtain ⟨g0, hg0⟩ := hint
  have hc : ∀ m, coeff m g = algebraMap ℤ_[p] ℚ_[p] (coeff m g0) := by
    intro m
    rw [← hg0]
    simp [MvPolynomial.coeff_map]
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  obtain ⟨hsupp, hsum⟩ := hs hm
  have hmono : monomial m (coeff m g) = (coeff m g0) • monomial m (1 : ℚ_[p]) := by
    rw [hc m, smul_monomial, Algebra.smul_def, mul_one]
  rw [hmono]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, mem_xiMons_of G n m hsupp hsum, rfl⟩)

theorem Ljj_fg (j : Fin G.T.t → ℕ) (jp : ℕ) : (Ljj p (r := r) G j jp).FG := by
  classical
  obtain ⟨A, hA⟩ := Formalism.GM.TM.yZ_fg (p := p) (r := r) (G.lettersAt j jp) G.T.J G.T.thr
  let S : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :=
    (fun am : _ × _ => rename (Formalism.GM.M.chainEmb N r G.T.t) am.1 * monomial am.2 (1 : ℚ_[p])) ''
      ((A : Set _) ×ˢ (xiMons (r := r) G (G.B - jp) : Set _))
  have hS : S.Finite := (A.finite_toSet.prod (xiMons (r := r) G (G.B - jp)).finite_toSet).image _
  have hle : Ljj p (r := r) G j jp ≤ Submodule.span ℤ_[p] S := by
    unfold Ljj
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, g, hg, rfl⟩
    have hy' : y ∈ Submodule.span ℤ_[p] (A : Set _) := by rw [hA]; exact hy
    have hg' := xi_mem_spanZ G (G.B - jp) g hg
    clear hy hg
    induction hy' using Submodule.span_induction with
    | mem a ha =>
      induction hg' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, hm, rfl⟩ := hx
        exact Submodule.subset_span ⟨(a, m), ⟨ha, hm⟩, rfl⟩
      | zero => simp
      | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ c hu
    | zero => simp
    | add u v _ _ hu hv => rw [map_add, add_mul]; exact Submodule.add_mem _ hu hv
    | smul c u _ hu =>
      have : rename (Formalism.GM.M.chainEmb N r G.T.t) (c • u) = c • rename (Formalism.GM.M.chainEmb N r G.T.t) u := by
        rw [← algebraMap_smul ℚ_[p] c u, ← algebraMap_smul ℚ_[p] c (rename (Formalism.GM.M.chainEmb N r G.T.t) u)]
        exact map_smul (rename (Formalism.GM.M.chainEmb N r G.T.t)) _ _
      rw [this, smul_mul_assoc]
      exact Submodule.smul_mem _ c hu
  exact Submodule.FG.of_le (Submodule.fg_span hS) hle

end Lvl

section Lvl2

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem ljjFin_gen (j : Fin G.T.t → ℕ) (jp : ℕ) :
    (Ljj p (r := r) G j jp).FG ∧
    ∃ W : Submodule ℚ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]),
      FiniteDimensional ℚ_[p] W ∧ ∀ u ∈ Ljj p (r := r) G j jp, u ∈ W :=
  ⟨Ljj_fg G j jp, _, Ljj_span_fd G j jp, fun _ hu => Submodule.subset_span hu⟩

end Lvl2

theorem restLjjFin_proved (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : RestLjjFin C0 CE1 CE2 X :=
  fun _ _ aTop _ x _ => ljjFin_gen (p := X.p) (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
