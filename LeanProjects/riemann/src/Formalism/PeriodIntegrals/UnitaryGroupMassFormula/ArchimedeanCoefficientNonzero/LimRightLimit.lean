import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.MeasurableTripleProduct

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.BICNZ

open Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.BetaCut

variable {k r : ℕ}

theorem lim_chi_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) {t : ℝ} (ht : t ≤ 0) : D.χ t = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  have := D.χ_supp hm
  simp only [Set.mem_Ioo] at this
  linarith [this.1]

theorem lim_chi_hcs {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) : HasCompactSupport D.χ :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (D.χ_supp.trans Set.Ioo_subset_Icc_self)

theorem lim_pi_inner {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {U : Set (Mat k r)}
    {π : Mat k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn U π) (hu : ∀ h ∈ U, ∀ v, ‖π h v‖ = ‖v‖)
    {H : Mat k r} (hH : H ∈ U) (hHi : H⁻¹ ∈ U) (hHu : IsUnit H.det) (ξ : Wp) :
    ⟪π H⁻¹ ξ, ξ⟫_ℂ = ⟪ξ, π H ξ⟫_ℂ := by
  let I : Wp →ₗᵢ[ℂ] Wp := ⟨(π H).toLinearMap, hu H hH⟩
  have h1 : π H (π H⁻¹ ξ) = ξ := BesselUnitaryEquiv.rep_inv hπ hH hHi (Matrix.mul_nonsing_inv _ hHu) ξ
  have h2 := I.inner_map_map (π H⁻¹ ξ) ξ
  change ⟪π H (π H⁻¹ ξ), π H ξ⟫_ℂ = _ at h2
  rw [h1] at h2
  exact h2.symm

theorem lim_conj_mul {H M : Mat k r} (hu : IsUnit H.det) : H * (H⁻¹ * M * H⁻¹⁻¹) = M * H := by
  rw [Matrix.nonsing_inv_nonsing_inv _ hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mul]

theorem lim_psi_conj {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {H M : Mat k r} (hH : H ∈ UWset k r z)
    (hM : M ∈ Nset k r) :
    psi k r z cStd (H⁻¹ * M * H⁻¹⁻¹) = Complex.exp (Complex.I * ((lam k r z M : ℝ) : ℂ)) := by
  unfold psi
  rw [(Formalism.QuantumDeterminants.unitary_weyl_normal_holds k r z hz _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hH) M hM).2]
  rfl

theorem lim_left_pt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) (v : H) (ξ : Wp)
    (x : Mt k r × Mt k r) (hh : Matrix.of x.1 ∈ UWset k r D.z) (hm : Matrix.of x.2 ∈ Nset k r) :
    star ⟪ξ, Formalism.FourierDecayAlt.ThreeDimData.beInt D.z cStd D.π σ v v (x.1, conjM (Matrix.of x.1)⁻¹ x.2) ξ⟫_ℂ =
      Lf D σ v ξ x * Complex.exp (Complex.I * ((lam k r D.z (Matrix.of x.2) : ℝ) : ℂ)) := by
  obtain ⟨h, m⟩ := x
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have hi := Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh
  have eM : Matrix.of h * Matrix.of (conjM (Matrix.of h)⁻¹ m) = Matrix.of m * Matrix.of h :=
    lim_conj_mul (M := Matrix.of m) hu
  have eψ : psi k r D.z cStd (Matrix.of (conjM (Matrix.of h)⁻¹ m)) =
      Complex.exp (Complex.I * ((lam k r D.z (Matrix.of m) : ℝ) : ℂ)) :=
    lim_psi_conj D.z_mem hh hm
  have eπ := lim_pi_inner D.π_rep D.π_unitary hh hi hu ξ
  dsimp only [Formalism.FourierDecayAlt.ThreeDimData.beInt, Lf]
  rw [eM, eψ, ContinuousLinearMap.smul_apply, inner_smul_right, star_mul', star_mul', star_star,
    Complex.star_def, inner_conj_symm, inner_conj_symm, eπ]
  ring

theorem lim_right_pt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) (v' : H) (ξ' : Wq)
    (x : Mt k r × Mt k r) (hh : Matrix.of x.1 ∈ UWset k r D.z') (hm : Matrix.of x.2 ∈ Nset k r) :
    ⟪ξ', Formalism.FourierDecayAlt.ThreeDimData.beInt D.z' cStd D.π' σ v' v' (x.1, conjM (Matrix.of x.1)⁻¹ x.2) ξ'⟫_ℂ =
      Rf D σ v' ξ' x * Complex.exp (Complex.I * ((-lam k r D.z' (Matrix.of x.2) : ℝ) : ℂ)) := by
  obtain ⟨h, m⟩ := x
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have eM : Matrix.of h * Matrix.of (conjM (Matrix.of h)⁻¹ m) = Matrix.of m * Matrix.of h :=
    lim_conj_mul (M := Matrix.of m) hu
  have eψ : psi k r D.z' cStd (Matrix.of (conjM (Matrix.of h)⁻¹ m)) =
      Complex.exp (Complex.I * ((lam k r D.z' (Matrix.of m) : ℝ) : ℂ)) :=
    lim_psi_conj D.z'_mem hh hm
  have es : ∀ a : ℝ, star (Complex.exp (Complex.I * (a : ℂ))) = Complex.exp (Complex.I * ((-a : ℝ) : ℂ)) := by
    intro a
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring_nf
  dsimp only [Formalism.FourierDecayAlt.ThreeDimData.beInt, Rf]
  rw [eM, eψ, es, ContinuousLinearMap.smul_apply, inner_smul_right]
  ring

theorem lim_leftLimit : LeftLimit := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hHC hDS v ξ hv hI
  haveI := lim_sf D.haarW
  haveI := lim_sf D.haarN
  set f : Mt k r × Mt k r → ℂ := fun p => star ⟪ξ, Formalism.FourierDecayAlt.ThreeDimData.beInt D.z cStd D.π σ v v p ξ⟫_ℂ with hf
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ Wp ξ)
  have hLi : Integrable (fun p => L (Formalism.FourierDecayAlt.ThreeDimData.beInt D.z cStd D.π σ v v p)) (D.μW.prod D.μN) :=
    L.integrable_comp hI
  have hfi : Integrable f (D.μW.prod D.μN) :=
    (Complex.conjCLE.toContinuousLinearMap).integrable_comp hLi
  have hfint : ∫ p, f p ∂(D.μW.prod D.μN) =
      star ⟪ξ, Formalism.FourierDecayAlt.ThreeDimData.be D.z cStd D.π σ D.μW D.μN v v ξ⟫_ℂ := by
    have h1 : ∫ p, f p ∂(D.μW.prod D.μN) =
        (starRingEnd ℂ) (∫ p, L (Formalism.FourierDecayAlt.ThreeDimData.beInt D.z cStd D.π σ v v p) ∂(D.μW.prod D.μN)) :=
      integral_conj
    rw [h1, L.integral_comp_comm hI]
    rfl
  have hCI := Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D
  have hC : ∀ h : Mt k r, Matrix.of h ∈ UWset k r D.z → D.μN.map (conjM (Matrix.of h)⁻¹) = D.μN :=
    fun h hh => hCI _ (Or.inl (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh))
  have q1 : ∀ᵐ x ∂(D.μW.prod D.μN), Matrix.of x.1 ∈ UWset k r D.z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 D.haarW.conc)
  have q2 : ∀ᵐ x ∂(D.μW.prod D.μN), Matrix.of x.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 D.haarN.conc)
  have hfg : ∀ᵐ x ∂(D.μW.prod D.μN), f (x.1, conjM (Matrix.of x.1)⁻¹ x.2) =
      Lf D σ v ξ x * Complex.exp (Complex.I * ((lam k r D.z (Matrix.of x.2) : ℝ) : ℂ)) := by
    filter_upwards [q1, q2] with x hh hm
    exact lim_left_pt D σ v ξ x hh hm
  obtain ⟨hLi2, hLint⟩ := lim_conj_transfer D.μW D.μN (UWset k r D.z) (ae_iff.2 D.haarW.conc) hC f _ hfi hfg
  have hJ := Formalism.FourierDecayAlt.P.dilation_jacobian_every_setting k r Wp Wq D
  have hΛ : ∀ t : ℝ, 0 < t → ∀ n ∈ {n : Mt k r | Matrix.of n ∈ Nset k r},
      (fun n : Mt k r => lam k r D.z (Matrix.of n)) (conjM (aDil k r t) n) =
        t * (fun n : Mt k r => lam k r D.z (Matrix.of n)) n :=
    fun t ht n hn => (Formalism.FourierDecayAlt.P.dilation_unipotent_measure k r D.z t ht.ne' D.z_mem (Matrix.of n) hn).2.2
  have key := lim_dil_fubini D.μW D.μN hJ D.χ D.χ_smooth.continuous (lim_chi_hcs D) (fun t ht => lim_chi_zero D ht)
    D.χ_int {n : Mt k r | Matrix.of n ∈ Nset k r} (ae_iff.2 D.haarN.conc)
    (fun n : Mt k r => lam k r D.z (Matrix.of n)) hΛ (Lf D σ v ξ) hLi2
  rw [← hfint, ← hLint]
  exact key

theorem lim_rightLimit : RightLimit := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hHC hDS v' ξ' hv' hI
  haveI := lim_sf D.haarW'
  haveI := lim_sf D.haarN
  set f : Mt k r × Mt k r → ℂ := fun p => ⟪ξ', Formalism.FourierDecayAlt.ThreeDimData.beInt D.z' cStd D.π' σ v' v' p ξ'⟫_ℂ with hf
  let L : (Wq →L[ℂ] Wq) →L[ℂ] ℂ := (innerSL ℂ ξ').comp (ContinuousLinearMap.apply ℂ Wq ξ')
  have hfi : Integrable f (D.μW'.prod D.μN) := L.integrable_comp hI
  have hfint : ∫ p, f p ∂(D.μW'.prod D.μN) =
      ⟪ξ', Formalism.FourierDecayAlt.ThreeDimData.be D.z' cStd D.π' σ D.μW' D.μN v' v' ξ'⟫_ℂ :=
    L.integral_comp_comm hI
  have hCI := Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D
  have hC : ∀ h : Mt k r, Matrix.of h ∈ UWset k r D.z' → D.μN.map (conjM (Matrix.of h)⁻¹) = D.μN :=
    fun h hh => hCI _ (Or.inr (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh))
  have q1 : ∀ᵐ x ∂(D.μW'.prod D.μN), Matrix.of x.1 ∈ UWset k r D.z' :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 D.haarW'.conc)
  have q2 : ∀ᵐ x ∂(D.μW'.prod D.μN), Matrix.of x.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 D.haarN.conc)
  have hfg : ∀ᵐ x ∂(D.μW'.prod D.μN), f (x.1, conjM (Matrix.of x.1)⁻¹ x.2) =
      Rf D σ v' ξ' x * Complex.exp (Complex.I * ((-lam k r D.z' (Matrix.of x.2) : ℝ) : ℂ)) := by
    filter_upwards [q1, q2] with x hh hm
    exact lim_right_pt D σ v' ξ' x hh hm
  obtain ⟨hLi2, hLint⟩ := lim_conj_transfer D.μW' D.μN (UWset k r D.z') (ae_iff.2 D.haarW'.conc) hC f _ hfi hfg
  have hJ := Formalism.FourierDecayAlt.P.dilation_jacobian_every_setting k r Wp Wq D
  have hΛ : ∀ t : ℝ, 0 < t → ∀ n ∈ {n : Mt k r | Matrix.of n ∈ Nset k r},
      (fun n : Mt k r => -lam k r D.z' (Matrix.of n)) (conjM (aDil k r t) n) =
        t * (fun n : Mt k r => -lam k r D.z' (Matrix.of n)) n := by
    intro t ht n hn
    have := (Formalism.FourierDecayAlt.P.dilation_unipotent_measure k r D.z' t ht.ne' D.z'_mem (Matrix.of n) hn).2.2
    show -lam k r D.z' (aDil k r t * Matrix.of n * (aDil k r t)⁻¹) = t * -lam k r D.z' (Matrix.of n)
    rw [this]; ring
  have key := lim_dil_fubini D.μW' D.μN hJ D.χ D.χ_smooth.continuous (lim_chi_hcs D) (fun t ht => lim_chi_zero D ht)
    D.χ_int {n : Mt k r | Matrix.of n ∈ Nset k r} (ae_iff.2 D.haarN.conc)
    (fun n : Mt k r => -lam k r D.z' (Matrix.of n)) hΛ (Rf D σ v' ξ') hLi2
  rw [← hfint, ← hLint]
  exact key

end PI.BICNZ
