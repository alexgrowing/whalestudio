import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PairZero
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ProperRatH
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic

noncomputable section

open NumberField MeasureTheory
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal InnerProductSpace

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

theorem memLp_rt (X : PositivityTheory.Rg.BcB.E1.Ctx) (hr : X.μ.IsMulRightInvariant) {f : X.G → ℂ}
    (hinv : ∀ γ : X.Γ, ∀ y, f ((γ : X.G) * y) = f y) (hf : MemLp f 2 X.ν) (z : X.G) :
    MemLp (fun x => f (x * z)) 2 X.ν := by
  haveI := hr
  have hνμ : X.ν ≪ X.μ := Measure.absolutelyContinuous_of_le (Measure.restrict_le_self : X.μ.restrict X.F ≤ X.μ)
  refine ⟨((aesm_of_inv X hinv hf.1).comp_measurePreserving (measurePreserving_mul_right X.μ z)).mono_ac hνμ, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
    lint_rt X hr (g := fun y => ‖f y‖ₑ ^ (2 : ℝ≥0∞).toReal) (fun γ y => by simp only [hinv γ y]) z,
    ← eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
  exact hf.2

theorem piInv_of (hC : PiClosureInv) : PiInv := by
  intro E _ _ _ n hn D π hθ ι _ Φ T hΦ hT
  classical
  let X := PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D
  have hr : X.μ.IsMulRightInvariant := D.haar.2.1
  have hdet : ∀ g : GA E n, IsUnit (g : Matrix (Fin n) (Fin n) (Ad E)).det := fun g => by
    simp
  have hldet : ∀ (γ : ratH E n 0) (y : H E n 0), ldet ((γ : H E n 0) * y) = ldet y := by
    intro γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    have hb := PositivityTheory.Rg.BcB.D1.logAbsBasic E
    have hd : ((ratGL E n γ₁ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)).det =
        algebraMap E (Ad E) (γ₁ : Matrix (Fin n) (Fin n) E).det := by
      simp [ratGL, RingHom.map_det]
    have hne : (γ₁ : Matrix (Fin n) (Fin n) E).det ≠ 0 := by
      simpa using (Matrix.GeneralLinearGroup.det γ₁).ne_zero
    simp only [ldet, Prod.fst_mul, h1]
    rw [Units.val_mul, Matrix.det_mul, hb.2.1 _ _ (hdet _) (hdet _), hd, hb.2.2 _ hne, zero_add]
  have hpsi0 : True := trivial
  have hpsi : ∀ ψ ∈ π.V, ∀ (γ : ratH E n 0) (y : H E n 0), ψ.1 ((γ : H E n 0) * y).1 = ψ.1 y.1 := by
    intro ψ hψ γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (π.cusp ψ hψ).1.left γ₁ y.1
  have key : ∀ g : Hs (ι := ι) D, IsPiVec D π g → T g ∈ piSp D π ι := by
    intro g hg
    choose ψ hψ u hu hu' hgu using hg
    set Ft : ι → H E n 0 → ℂ := fun j x => (ψ j).1 x.1 * u j (ldet x) with hFt
    have hinv : ∀ j, ∀ γ : ratH E n 0, ∀ y : H E n 0, Ft j ((γ : H E n 0) * y) = Ft j y := fun j γ y => by
      show (ψ j).1 ((γ : H E n 0) * y).1 * u j (ldet ((γ : H E n 0) * y)) = (ψ j).1 y.1 * u j (ldet y)
      rw [hpsi _ (hψ j) γ y, hldet γ y]
    have hmem : ∀ j, MemLp (Ft j) 2 X.ν := fun j => (Lp.memLp (g j)).ae_eq (hgu j)
    rw [← Submodule.orthogonal_orthogonal (piSp D π ι), Submodule.mem_orthogonal]
    intro h hh
    have hz : ∀ i j (z : H E n 0),
        ∫ x, starRingEnd ℂ ((h i : H E n 0 → ℂ) x) * Ft j (x * z) ∂D.ν = 0 := by
      intro i j z
      have hw := memLp_rt X hr (hinv j) (hmem j) z
      let w : Lp ℂ 2 D.ν := hw.toLp _
      let v : Hs (ι := ι) D := WithLp.toLp 2 (Pi.single i w)
      have hvl : ∀ l, v l = (Pi.single i w : ι → Lp ℂ 2 D.ν) l := fun l => rfl
      have hv : v ∈ piSp D π ι := by
        refine hC E n hn D π hθ ι (fun l => if l = i then ψ j else 0) (fun l => if l = i then u j else 0) z v ?_ ?_
        · intro l
          split_ifs
          · exact ⟨hψ j, hu j, hu' j⟩
          · exact ⟨Submodule.zero_mem _, continuous_zero, HasCompactSupport.zero⟩
        · intro l
          rw [hvl]
          by_cases hl : l = i
          · subst hl
            rw [Pi.single_eq_same]
            filter_upwards [hw.coeFn_toLp] with x hx
            simp only [if_pos rfl]
            exact (show (w : H E n 0 → ℂ) x = Ft j (x * z) from hx)
          · rw [Pi.single_eq_of_ne hl]
            filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := D.ν)] with x hx
            rw [hx]
            simp only [if_neg hl, Submodule.coe_zero, ZeroMemClass.coe_zero, Pi.zero_apply, zero_mul]
      have h0 : ⟪h, v⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal hv hh
      rw [PiLp.inner_apply, Finset.sum_eq_single i (fun l _ hl => by rw [hvl, Pi.single_eq_of_ne hl, inner_zero_right])
        (fun hi => absurd (Finset.mem_univ i) hi), hvl, Pi.single_eq_same, MeasureTheory.L2.inner_def] at h0
      rw [← h0]
      refine integral_congr_ae ?_
      filter_upwards [hw.coeFn_toLp] with x hx
      rw [show (w : H E n 0 → ℂ) x = Ft j (x * z) from hx, RCLike.inner_apply, mul_comm]
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [MeasureTheory.L2.inner_def]
    have hP := fun j => pair_zero X hr PositivityTheory.Rg.BcB.E1.kerBasic PositivityTheory.Rg.BcB.E1.kernel_rows_columns_square_integrable (hΦ i j) (hinv j) (hmem j)
      (Lp.memLp (h i)) (hz i j)
    calc ∫ x, ⟪(h i : H E n 0 → ℂ) x, (T g i : H E n 0 → ℂ) x⟫_ℂ ∂D.ν
        = ∫ x, ∑ j, starRingEnd ℂ ((h i : H E n 0 → ℂ) x) *
            ∫ y, kerH (Φ i j) x y * Ft j y ∂D.ν ∂D.ν := by
          refine integral_congr_ae ?_
          filter_upwards [hT g i] with x hx
          rw [hx, RCLike.inner_apply, mul_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          exact integral_congr_ae ((hgu j).mono fun y hy => by simp only [hy, hFt])
      _ = ∑ j, ∫ x, starRingEnd ℂ ((h i : H E n 0 → ℂ) x) * ∫ y, kerH (Φ i j) x y * Ft j y ∂D.ν ∂D.ν :=
          integral_finset_sum _ fun j _ => (hP j).1
      _ = 0 := Finset.sum_eq_zero fun j _ => (hP j).2
  intro f hf
  have hle : Submodule.span ℂ {f | IsPiVec D π f} ≤ (piSp D π ι).comap (T : Hs (ι := ι) D →ₗ[ℂ] Hs (ι := ι) D) :=
    Submodule.span_le.2 fun g hg => key g hg
  have hcl : IsClosed (((piSp D π ι).comap (T : Hs (ι := ι) D →ₗ[ℂ] Hs (ι := ι) D)) : Set (Hs (ι := ι) D)) :=
    (show IsClosed (piSp D π ι : Set (Hs (ι := ι) D)) from Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact Submodule.topologicalClosure_minimal _ hle hcl hf

end DiscreteGroups.T1.G

end
