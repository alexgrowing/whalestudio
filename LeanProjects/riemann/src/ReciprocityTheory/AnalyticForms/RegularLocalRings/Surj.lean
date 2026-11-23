import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsClosedOfChartIdeal
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BijOnClosedPointsOfIsIso

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

namespace WData

variable (w : WData P D hP)

theorem surj' (hD : IsMultiHomogIdeal D) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts P)
    (hzD : z ∉ conePts D) :
    ∃ c, ∃ x ∈ w.src c, SameOrbit (fun q => eval (w.coord c x) (w.lift c q)) z := by
  have := w.isIso_off
  obtain ⟨p, hzp, -⟩ := exists_chart z hz.1
  have hzc : ∀ h ∈ chartIdeal P p, eval (affCoord p z) h = 0 :=
    (mem_conePts_iff_chartIdeal hP p z hzp).1 hz
  obtain ⟨y, hy, hyc, hyv⟩ := exists_closed_of_chartIdeal (hP := hP) p (affCoord p z) hzc
  have hyB : y ∈ projBCompl P D hP := by
    intro hB
    have h1 := (mem_projB_iff_val hD p y hy hyc).1 hB
    rw [funext hyv] at h1
    exact hzD ((mem_conePts_iff_affCoord hD p z hzp).2 h1)
  obtain ⟨x, ⟨hxc, -⟩, hxy⟩ := (bijOn_closedPoints_of_isIso (sW := w.π ≫ toSpecC hP)
    (sX := toSpecC hP) w.π rfl (projBCompl P D hP)).2.2 ⟨hyc, hyB⟩
  subst hxy
  have hxp : x ∈ w.π ⁻¹ᵁ (chartOpen hP p).1 := hy
  rw [← w.iSup_pres p] at hxp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hxp
  refine ⟨⟨p, i⟩, ⟨x, hxc⟩, hi, ?_⟩
  have hl : (fun q => eval (w.coord ⟨p, i⟩ ⟨x, hxc⟩) (w.lift ⟨p, i⟩ q)) = affCoord p z := by
    funext q
    rw [w.lift_eval_eq_val ⟨p, i⟩ ⟨x, hxc⟩ hi q]
    exact hyv q
  rw [hl]
  exact sameOrbit_symm' (sameOrbit_affCoord p z hzp)

theorem inj' (hD : IsMultiHomogIdeal D) (c c' : w.Idx) (x : w.M) (hx : x ∈ w.src c) (x' : w.M)
    (hx' : x' ∈ w.src c') (hxD : (fun q => eval (w.coord c x) (w.lift c q)) ∉ conePts D)
    (ho : SameOrbit (fun q => eval (w.coord c x) (w.lift c q))
      (fun q => eval (w.coord c' x') (w.lift c' q))) : x = x' := by
  have := w.isIso_off
  obtain ⟨a, ha0, ha⟩ := ho
  have hxc : w.π.base x.1 ∈ (chartOpen hP c.1).1 := w.le_pres c.1 c.2 hx
  have hone : ∀ k, eval (w.coord c x) (w.lift c ⟨k, c.1 k⟩) = 1 := fun k => by simp [lift]
  have hx'c : ∀ k, eval (w.coord c' x') (w.lift c' ⟨k, c.1 k⟩) ≠ 0 := by
    intro k h0
    have := congrFun ha ⟨k, c.1 k⟩
    simp only [hone k, h0, mul_zero] at this
    exact one_ne_zero this
  have hpx' : w.π.base x'.1 ∈ (chartOpen hP c.1).1 := (w.mem_chartOpen_iff c' x' hx' c.1).2 hx'c
  have heq : w.π.base x.1 = w.π.base x'.1 := by
    refine eq_of_val_chartCoord c.1 _ _ hxc hpx' (w.isClosed_image c x hx)
      (w.isClosed_image c' x' hx') fun q => ?_
    rw [w.val_chartCoord c x hx c.1 hxc q, w.val_chartCoord c' x' hx' c.1 hpx' q,
      affCoord_eq_of_sameOrbit c.1 ⟨a, ha0, ha⟩]
  have hxU : w.π.base x.1 ∈ projBCompl P D hP :=
    fun h => hxD ((w.mem_projB_iff_lift hD c x hx).1 h)
  have hbij := bijOn_closedPoints_of_isIso (sW := w.π ≫ toSpecC hP) (sX := toSpecC hP) w.π rfl
    (projBCompl P D hP)
  exact Subtype.ext (hbij.injOn ⟨x.2, hxU⟩ ⟨x'.2, heq ▸ hxU⟩ heq)

end WData

end

end ReciprocityTheory.AnForm.R
