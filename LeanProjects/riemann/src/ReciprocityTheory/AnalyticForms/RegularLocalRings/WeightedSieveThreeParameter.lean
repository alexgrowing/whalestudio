import ReciprocityTheory.AnalyticForms.RegularLocalRings.ContinuousOnOfCharts
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsClosedOfChartIdeal

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem WData.t2Space (w : WData P D hP) : T2Space w.M := by
  refine ⟨fun x y hxy => ?_⟩
  by_cases hcom : ∃ d, x ∈ w.src d ∧ y ∈ w.src d
  · obtain ⟨d, hxd, hyd⟩ := hcom
    have hne : w.coord d x ≠ w.coord d y := by
      intro h
      have h' : (⟨x, hxd⟩ : w.src d) = ⟨y, hyd⟩ := (w.isEmbedding d).injective h
      exact hxy (congrArg Subtype.val h')
    exact sep_of_continuousOn (w.isOpen_alt_bis d) (w.continuousOn_coord d) hxd hyd hne
  push Not at hcom
  obtain ⟨c, hxc⟩ := w.cover x
  obtain ⟨c', hyc'⟩ := w.cover y
  by_cases hblk : ∃ q, w.blk q x ≠ w.blk q y
  · obtain ⟨q, hq⟩ := hblk
    exact sep_of_continuousOn isOpen_univ (w.continuous_blk q).continuousOn trivial trivial hq
  push Not at hblk
  have hy1 : ∀ k, eval (w.coord c' y) (w.lift c' ⟨k, c.1 k⟩) ≠ 0 := by
    intro k
    have h1 : w.blk ⟨k, c.1 k⟩ x ≠ 0 := by
      rw [w.blk_eq _ c x hxc, blkNorm_ne_zero_iff, w.lv_self]
      exact one_ne_zero
    rw [hblk, w.blk_eq _ c' y hyc', blkNorm_ne_zero_iff] at h1
    exact h1
  have hyp : w.π.base y.1 ∈ (chartOpen hP c.1).1 := (w.mem_chartOpen_iff c' y hyc' c.1).mpr hy1
  obtain ⟨j, hyj⟩ : ∃ j, y ∈ w.src ⟨c.1, j⟩ := by
    have h : y.1 ∈ w.π ⁻¹ᵁ (chartOpen hP c.1).1 := hyp
    rw [← w.iSup_pres] at h
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp h
    exact ⟨j, hj⟩
  by_cases hfib : ∃ l, w.fib c.1 l x ≠ w.fib c.1 l y
  · obtain ⟨l, hl⟩ := hfib
    exact sep_of_continuousOn (w.isOpen_overP c.1) (w.continuousOn_fib c.1 l) ⟨c.2, hxc⟩
      ⟨j, hyj⟩ hl
  push Not at hfib
  have h1 : w.fib c.1 j y ≠ 0 := by
    rw [w.fib_eq c.1 j j y hyj, vecNorm_ne_zero_iff, w.tv_self c.1 j y hyj]
    exact one_ne_zero
  rw [← hfib j, w.fib_eq c.1 j c.2 x hxc, vecNorm_ne_zero_iff, w.tv_ne_zero_iff c.1 c.2 j x hxc] at h1
  exact (hcom _ h1 hyj).elim

end ReciprocityTheory.AnForm.R
