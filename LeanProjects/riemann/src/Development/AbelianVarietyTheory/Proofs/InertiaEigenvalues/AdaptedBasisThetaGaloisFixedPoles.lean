import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisDeRhamBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaAinfPeriodPowNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeAdaptedBasisInvariantMatrixRatioStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaGaloisFixedOfCongrBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittPowerSeriesApproxMatrixBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxBdRPlusFilMatrixMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTauPowFrameAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeAdaptedBasisGaloisActionBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixComatrixDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowDvdOfBdRPlusDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateOperatorOfGaloisRelationsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportMatrixIdentityInjectiveRingHomStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

theorem GlobalTheory.MapSmul.mapSmul {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (a : R) (M : Matrix m n R) :
    (a • M).map f = f a • M.map f := by
  ext i j; simp

open GlobalTheory.MapSmul in

theorem GlobalTheory.BKLim.adaptedBasis_theta_and_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ (g : ↥(GK K)) (z : ℂ_[l]), IsZ bk g z → ∃ u : Matrix (Fin d) (Fin d) (ℂ_[l]), u * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * (F.ε g).map ((Per.θD l).comp (aDp l)) ∧ u * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal fun i => z ^ ((H.p i : ℤ) - H.q)) ∧ ∀ N₀ : ℕ, N₀ ≤ N → (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → (∀ i j, bk.E ^ (N - N₀) ∣ F.A i j) ∧ ∀ i j, bk.E ^ (N - N₀) ∣ F.A' i j := by
  intro l _ K bk τ hτ C hC N d ρ F Y hDR hY H
  have hdom := GlobalTheory.MemLoc.BdRField.bdR_isField l
  haveI : IsDomain (Per.BdRp l) := hdom.1
  have hι : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := hdom.2.1
  obtain ⟨B, Q, hBu, hQu, hBl, hQ, hQi⟩ := GlobalTheory.T.exists_invariant_basis_deRham_breuilKisin l K bk τ hτ C N d ρ F Y hDR hY
  obtain ⟨Y₁, Y', hY₁, hYY'⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d ρ F.toPre
  have hinj : Function.Injective (inclW l) := WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))
  have hY1 : Y₁ = Y := Matrix.ext fun i j => hinj (by simpa using congrFun (congrFun (hY₁.trans hY.symm) i) j)
  rw [hY1] at hYY'
  obtain ⟨c, c', hc, hc', hcc', hQH⟩ := GlobalTheory.T.hodgeAdaptedBasis_invariant_matrix_ratio l K bk C hC d ρ Q hQu hQi H
  have hθt : Per.θD l (aDp l τ) ≠ 0 := by simpa using GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ 1
  have htu : IsUnit (aDp l τ) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ hθt
  obtain ⟨u, hu⟩ := htu
  have hYY'd : Y.map (aDp l) * Y'.map (aDp l) = aDp l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l)) := by
    rw [← Matrix.map_mul, hYY', mapSmul, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  have hY'Yd : Y'.map (aDp l) * Y.map (aDp l) = aDp l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l)) := by
    have h1 : ((↑u⁻¹ : Per.BdRp l) ^ (2 * N) • Y.map (aDp l)) * Y'.map (aDp l) = 1 := by
      rw [Matrix.smul_mul, hYY'd, smul_smul, ← hu, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have h2 := mul_eq_one_comm.1 h1
    rw [Matrix.mul_smul] at h2
    calc Y'.map (aDp l) * Y.map (aDp l) = (aDp l τ ^ (2 * N)) • ((↑u⁻¹ : Per.BdRp l) ^ (2 * N) • (Y'.map (aDp l) * Y.map (aDp l))) := by
          rw [smul_smul, ← hu, ← mul_pow, Units.mul_inv, one_pow, one_smul]
      _ = _ := by rw [h2]

  have hstar : aDp l (bk.ev bk.E) ^ H.q • (Y.map (aDp l) * (F.A.map bk.ev).map (aDp l) * B * c.map C.o) =
      (aDp l (bk.ev bk.E) * aDp l τ) ^ N • (H.V * Matrix.diagonal (fun j => aDp l (bk.ev bk.E) ^ H.p j)) := by
    refine GlobalTheory.T.transport_matrix_identity_injective_ringHom (algebraMap (Per.BdRp l) (Per.BdR l)) hι d N H.q H.p _ _ Q H.Q _ B _ H.V ?_ H.Q_eq ?_
    · rw [← Matrix.map_mul, ← map_mul]; exact hQ
    · rw [hQH]; rfl

  set V₀ : Matrix (Fin d) (Fin d) (Per.BdRp l) := (↑u⁻¹ : Per.BdRp l) ^ N • (Y'.map (aDp l) * H.V) with hV₀
  have h1 : Y.map (aDp l) * V₀ = aDp l τ ^ N • H.V := by
    rw [hV₀, Matrix.mul_smul, ← Matrix.mul_assoc, hYY'd, Matrix.smul_mul, Matrix.one_mul, smul_smul, ← hu]
    congr 1
    rw [two_mul, pow_add, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  have hY'V : Y'.map (aDp l) * H.V = aDp l τ ^ N • V₀ := by
    rw [hV₀, smul_smul, ← hu, ← mul_pow, Units.mul_inv, one_pow, one_smul]
  have h2 : aDp l (bk.ev bk.E) ^ H.q • ((F.A.map bk.ev).map (aDp l) * B * c.map C.o) =
      aDp l (bk.ev bk.E) ^ N • (V₀ * Matrix.diagonal (fun j => aDp l (bk.ev bk.E) ^ H.p j)) := by
    have e := congrArg (fun M => Y'.map (aDp l) * M) hstar
    simp only [Matrix.mul_smul] at e
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hY'Yd, ← Matrix.mul_assoc, hY'V] at e
    simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul] at e
    have hu2 : IsUnit (aDp l τ ^ (2 * N)) := by rw [← hu]; exact (Units.isUnit u).pow _
    apply (hu2.smul_left_cancel).1
    rw [smul_smul, smul_smul, mul_comm, e, mul_pow, two_mul, pow_add]
    congr 1
    ring

  have h4 : ∀ (g : ↥(GK K)) (i j : Fin d), Per.σC (g : GQ l) (Per.θD l (V₀ i j)) = Per.θD l (V₀ i j) := by
    intro g i j
    obtain ⟨k, s, hs⟩ := GlobalTheory.T.approx_bdRPlus_fil_matrix_mul l K bk (N + H.p j + 1) d ((F.A.map bk.ev).map (aDp l) * B) (c.map C.o)
      (GlobalTheory.T.approx_bdRPlus_fil_matrix_mul l K bk (N + H.p j + 1) d ((F.A.map bk.ev).map (aDp l)) B
        ⟨0, F.A, fun i j => by rw [pow_zero, one_mul, Matrix.map_apply, Matrix.map_apply, sub_self]; exact zero_mem _⟩
        (hBl (N + H.p j + 1)))
      (GlobalTheory.T.exists_wittPowerSeries_approx_matrix_bdRPlus l K bk C d c hc (N + H.p j + 1))
    refine GlobalTheory.T.theta_galois_fixed_of_congr_breuilKisin l K bk (V₀ i j) (N + H.p j) k (bk.E ^ H.q * s i j) ?_ g
    have e := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul] at e
    have hm := Ideal.mul_mem_left _ (-(aDp l (bk.ev bk.E) ^ H.q)) (hs i j)
    have key : (l : Per.BdRp l) ^ k * aDp l (bk.ev bk.E) ^ (N + H.p j) * V₀ i j - aDp l (bk.ev (bk.E ^ H.q * s i j)) =
        -(aDp l (bk.ev bk.E) ^ H.q) * (aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * ((F.A.map bk.ev).map (aDp l) * B * c.map C.o) i j) := by
      rw [map_mul, map_mul, map_pow, map_pow]
      linear_combination -((l : Per.BdRp l) ^ k) * e
    rw [key]
    exact hm
  refine ⟨fun g z hz => ?_, fun N₀ hN₀ hp => ?_⟩
  · obtain ⟨w, hw, hzw⟩ := hz
    have hG1 := GlobalTheory.T.galois_tauPow_frame_ainf l K bk τ N d ρ F Y hY g
    have hG2 := GlobalTheory.T.hodgeAdaptedBasis_galois_action_bdRPlus l K bk C d ρ H g w hw
    have hb : Per.θD l (aDp l (Per.σA (g : GQ l) τ)) ≠ 0 := by
      rw [← GlobalTheory.MemLoc.ActLaws.σDp_aDp, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.2]
      intro h0
      exact hθt ((Per.σC (g : GQ l)).injective (h0.trans (map_zero _).symm))
    refine GlobalTheory.T.hodgeTate_operator_of_galois_relations d N H.q H.p (Per.θD l (aDp l τ)) (Per.θD l (aDp l (Per.σA (g : GQ l) τ))) z (Per.θD l (aDp l w))
      _ (Y'.map ((Per.θD l).comp (aDp l))) _ (V₀.map (Per.θD l)) _ (((ρ g).map ((aDp l).comp (Per.zA l))).map (Per.θD l))
      ((Y.map (Per.σA (g : GQ l))).map ((Per.θD l).comp (aDp l))) ((H.V.map (Per.σDp (g : GQ l))).map (Per.θD l))
      hθt hb hzw ?_ ?_ ?_ ?_ ?_
    · rw [← Matrix.map_mul, hYY', mapSmul, Matrix.map_one _ (map_zero _) (map_one _), map_pow]; rfl
    · rw [show Y.map ((Per.θD l).comp (aDp l)) = (Y.map (aDp l)).map (Per.θD l) from (Matrix.map_map).symm,
        ← Matrix.map_mul, h1, mapSmul, map_pow]
    · have e := congrArg (fun M => M.map ((Per.θD l).comp (aDp l))) hG1
      simp only [mapSmul, Matrix.map_mul, map_pow] at e
      have hr : ((ρ g).map ((aDp l).comp (Per.zA l))).map (Per.θD l) = ((ρ g).map (Per.zA l)).map ((Per.θD l).comp (aDp l)) := by
        ext i j; simp
      rw [hr]
      simpa only [RingHom.comp_apply] using e
    · have e := congrArg (fun M => M.map (Per.θD l)) hG2
      simp only [mapSmul, Matrix.map_mul, map_pow] at e
      rw [← e, Matrix.diagonal_map (map_zero _)]
      simp [Function.comp_def]
    · have e := congrArg (fun M => (M.map (Per.σDp (g : GQ l))).map (Per.θD l)) h1
      simp only [mapSmul, Matrix.map_mul, map_pow] at e
      have e1 : ((Y.map (aDp l)).map (Per.σDp (g : GQ l))).map (Per.θD l) = (Y.map (Per.σA (g : GQ l))).map ((Per.θD l).comp (aDp l)) := by
        ext i j; simp [GlobalTheory.MemLoc.ActLaws.σDp_aDp]
      have e2 : (V₀.map (Per.σDp (g : GQ l))).map (Per.θD l) = V₀.map (Per.θD l) := by
        ext i j; simp only [Matrix.map_apply]; rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.2, h4]
      rw [e1, e2, GlobalTheory.MemLoc.ActLaws.σDp_aDp] at e
      exact e
  · obtain ⟨B', hBB'⟩ := hBu.exists_right_inv
    obtain ⟨Vu, hVu⟩ := H.unit
    have hcp : c.map C.o * c'.map C.o = 1 := by
      rw [← Matrix.map_mul, hcc', Matrix.map_one _ (map_zero _) (map_one _)]
    have hVV : H.V * (↑Vu⁻¹ : Matrix (Fin d) (Fin d) (Per.BdRp l)) = 1 := by rw [← hVu]; exact Vu.mul_inv
    have hV₀' : V₀ * ((↑u⁻¹ : Per.BdRp l) ^ N • ((↑Vu⁻¹ : Matrix (Fin d) (Fin d) (Per.BdRp l)) * Y.map (aDp l))) = 1 := by
      calc V₀ * ((↑u⁻¹ : Per.BdRp l) ^ N • ((↑Vu⁻¹ : Matrix (Fin d) (Fin d) (Per.BdRp l)) * Y.map (aDp l)))
          = ((↑u⁻¹ : Per.BdRp l) ^ N * (↑u⁻¹ : Per.BdRp l) ^ N) • (Y'.map (aDp l) * (H.V * (↑Vu⁻¹ : Matrix (Fin d) (Fin d) (Per.BdRp l))) * Y.map (aDp l)) := by
            rw [hV₀, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; simp only [Matrix.mul_assoc]
        _ = ((↑u⁻¹ : Per.BdRp l) ^ N * (↑u⁻¹ : Per.BdRp l) ^ N) • (Y'.map (aDp l) * Y.map (aDp l)) := by rw [hVV, Matrix.mul_one]
        _ = 1 := by
            rw [hY'Yd, smul_smul, ← hu, ← pow_add, ← two_mul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have hAA' : (F.A.map bk.ev).map (aDp l) * (F.A'.map bk.ev).map (aDp l) =
        aDp l (bk.ev bk.E) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l)) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, F.A_mul, mapSmul, mapSmul, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.map_one _ (map_zero _) (map_one _), map_pow, map_pow]
    obtain ⟨hne, htr⟩ := GlobalTheory.T.eisenstein_pow_dvd_of_bdRPlus_dvd l K bk
    obtain ⟨hdA, hdA'⟩ := GlobalTheory.T.pow_dvd_entries_of_mul_eq_diagonal_pow d N N₀ H.q H.p (aDp l (bk.ev bk.E)) _ _ B B' _ _ V₀ _ hne hBB' hcp hV₀' hAA' h2 hN₀ hp
    exact ⟨fun i j => htr _ _ (by simpa using hdA i j), fun i j => htr _ _ (by simpa using hdA' i j)⟩

end
