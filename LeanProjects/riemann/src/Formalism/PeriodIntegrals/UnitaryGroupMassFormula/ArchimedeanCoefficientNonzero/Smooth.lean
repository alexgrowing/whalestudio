import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Development
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open MeasureTheory Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace PI.BICNZ

open Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.BetaCut

theorem two_le_smooth : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

section curve

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem ofReal_contDiffAt {f : ℝ → ℝ} {x : ℝ} {m : WithTop ℕ∞} (hf : ContDiffAt ℝ m f x) :
    ContDiffAt ℝ m (fun t => (f t : ℂ)) x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hf

theorem dgR_contDiffAt (i : Fin (2 * r + k + 1)) {t₀ : ℝ} (h0 : t₀ ≠ 0) :
    ContDiffAt ℝ 2 (fun t => Formalism.FourierDecayAlt.P.B2x7.dgR k r t i) t₀ := by
  unfold Formalism.FourierDecayAlt.P.B2x7.dgR
  split_ifs
  · exact (contDiff_id.pow _).contDiffAt
  · exact contDiffAt_const
  · exact ((contDiff_id.pow _).contDiffAt).inv (pow_ne_zero _ h0)

theorem curve_eq (n h : Mt k r) {t : ℝ} (ht : t ≠ 0) :
    Matrix.of (conjM (aDil k r t) n) * Matrix.of h =
      Matrix.of fun i j => ∑ l, (((Formalism.FourierDecayAlt.P.B2x7.dgR k r t i : ℝ) : ℂ) * n i l *
        ((Formalism.FourierDecayAlt.P.B2x7.dgR k r t⁻¹ l : ℝ) : ℂ)) * h l j := by
  show aDil k r t * Matrix.of n * (aDil k r t)⁻¹ * Matrix.of h = _
  rw [Formalism.FourierDecayAlt.P.B2.aDil_inv k r t ht, Formalism.FourierDecayAlt.P.B2x7.aDil_eq, Formalism.FourierDecayAlt.P.B2x7.aDil_eq]
  ext i j
  rw [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

theorem curve_contDiffAt (n h : Mt k r) {t₀ : ℝ} (h0 : t₀ ≠ 0) :
    ContDiffAt ℝ 2 (fun t : ℝ => Matrix.of (conjM (aDil k r t) n) * Matrix.of h) t₀ := by
  have hev : (fun t : ℝ => Matrix.of (conjM (aDil k r t) n) * Matrix.of h) =ᶠ[𝓝 t₀]
      (fun t => Matrix.of fun i j => ∑ l, (((Formalism.FourierDecayAlt.P.B2x7.dgR k r t i : ℝ) : ℂ) * n i l *
        ((Formalism.FourierDecayAlt.P.B2x7.dgR k r t⁻¹ l : ℝ) : ℂ)) * h l j) := by
    filter_upwards [isOpen_ne.mem_nhds h0] with t ht
    exact curve_eq n h ht
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  simp only [Matrix.of_apply]
  refine ContDiffAt.sum fun l _ => ?_
  exact (((ofReal_contDiffAt (dgR_contDiffAt i h0)).mul contDiffAt_const).mul
    (ofReal_contDiffAt ((dgR_contDiffAt l (inv_ne_zero h0)).comp t₀ (contDiffAt_inv ℝ h0)))).mul contDiffAt_const

theorem coef_contDiffAt {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (hw : w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (n h : Mt k r)
    (hn : Matrix.of n ∈ UH (Hpk k r)) (hh : Matrix.of h ∈ UH (Hpk k r)) {t₀ : ℝ} (h0 : t₀ ≠ 0) :
    ContDiffAt ℝ 2 (fun t : ℝ => σ (Matrix.of (conjM (aDil k r t) n) * Matrix.of h) w) t₀ := by
  set c : ℝ → Mat k r := fun t => Matrix.of (conjM (aDil k r t) n) * Matrix.of h with hc
  have hmem : ∀ t : ℝ, t ≠ 0 → c t ∈ UH (Hpk k r) := fun t ht =>
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (Formalism.FourierDecayAlt.P.dilation_mem_group k r t ht) hn)
      (WeylGroupFacts.uh_inv (Formalism.FourierDecayAlt.P.dilation_mem_group k r t ht))) hh
  have hw' : PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g => σ g w) := hw
  obtain ⟨U, F, hU, hcU, hF, hFeq⟩ := hw' (c t₀) (hmem t₀ h0)
  have hcd : ContDiffAt ℝ 2 c t₀ := curve_contDiffAt n h h0
  have hFc : ContDiffAt ℝ 2 (F ∘ c) t₀ :=
    ((hF.contDiffAt (hU.mem_nhds hcU)).of_le two_le_smooth).comp t₀ hcd
  refine hFc.congr_of_eventuallyEq ?_
  filter_upwards [hcd.continuousAt.preimage_mem_nhds (hU.mem_nhds hcU), eventually_ne_nhds h0] with t htU ht
  exact hFeq (c t) htU (hmem t ht)

end curve

theorem chi_factor_contDiffAt {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (t₀ : ℝ) :
    ContDiffAt ℝ 2 (fun t : ℝ => ((D.χ t * t ^ kap k r : ℝ) : ℂ)) t₀ := ofReal_contDiffAt ((D.χ_smooth.contDiffAt.of_le two_le_smooth).mul ((contDiff_id.pow _).contDiffAt))

theorem pos_of_mem_tsupport {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) {t₀ : ℝ}
    (ht : t₀ ∈ tsupport D.χ) : t₀ ≠ 0 := fun h => by
  have := D.χ_supp ht
  rw [h] at this
  norm_num at this

theorem left_profile_contDiff_two : LeftProfileContDiffTwo := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hHC hDS v ξ hv x hx1 hx2
  rw [contDiff_iff_contDiffAt]
  intro t₀
  by_cases ht : t₀ ∈ tsupport D.χ
  · have hw := coef_contDiffAt σ v hv x.2 x.1 hx2.1 hx1.1 (pos_of_mem_tsupport D ht)
    have hin : ContDiffAt ℝ 2
        (fun t : ℝ => ⟪σ (Matrix.of (conjM (aDil k r t) x.2) * Matrix.of x.1) v, v⟫_ℂ) t₀ :=
      hw.inner ℂ contDiffAt_const
    show ContDiffAt ℝ 2 (fun t : ℝ => ((D.χ t * t ^ kap k r : ℝ) : ℂ) *
      (⟪ξ, D.π (Matrix.of x.1) ξ⟫_ℂ * ⟪σ (Matrix.of (conjM (aDil k r t) x.2) * Matrix.of x.1) v, v⟫_ℂ)) t₀
    exact (chi_factor_contDiffAt D t₀).mul (contDiffAt_const.mul hin)
  · have hz : D.χ =ᶠ[𝓝 t₀] 0 := notMem_tsupport_iff_eventuallyEq.1 ht
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hz] with t htz
    simp [H1, htz]

theorem right_profile_contDiff_two : RightProfileContDiffTwo := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hHC hDS v' ξ' hv' x hx1 hx2
  rw [contDiff_iff_contDiffAt]
  intro t₀
  by_cases ht : t₀ ∈ tsupport D.χ
  · have hw := coef_contDiffAt σ v' hv' x.2 x.1 hx2.1 hx1.1 (pos_of_mem_tsupport D ht)
    have hin : ContDiffAt ℝ 2
        (fun t : ℝ => ⟪v', σ (Matrix.of (conjM (aDil k r t) x.2) * Matrix.of x.1) v'⟫_ℂ) t₀ :=
      contDiffAt_const.inner ℂ hw
    show ContDiffAt ℝ 2 (fun t : ℝ => ((D.χ t * t ^ kap k r : ℝ) : ℂ) *
      (⟪ξ', D.π' (Matrix.of x.1)⁻¹ ξ'⟫_ℂ * ⟪v', σ (Matrix.of (conjM (aDil k r t) x.2) * Matrix.of x.1) v'⟫_ℂ)) t₀
    exact (chi_factor_contDiffAt D t₀).mul (contDiffAt_const.mul hin)
  · have hz : D.χ =ᶠ[𝓝 t₀] 0 := notMem_tsupport_iff_eventuallyEq.1 ht
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hz] with t htz
    simp [H2, htz]

end PI.BICNZ
