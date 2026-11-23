import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaAinfPeriodPowNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerQEqMapKerTheta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBetaLimitBdRPlusDeRhamFrameStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitBdRPlusMatrixOfCongrOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameLimitGaloisInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusGaloisRelationFrameAinfStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.InvBasis

variable {l : ℕ} [Fact l.Prime]

theorem pD_alg_pt : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.AinfP l), Formalism.Per.pD l a = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) a) :=
  GlobalTheory.RingIface.pD_eq_alg

theorem zD_alg_pt : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zD l z = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z))) :=
  GlobalTheory.RingIface.zD_eq_alg

theorem isUnit_gen_pt (l : ℕ) [Fact l.Prime] {a : Per.AinfP l} (h : Per.kerP l = Ideal.span {a}) : IsUnit (Per.pD l a) := GlobalTheory.RingIface.isUnit_of_generator l h

theorem padicInt_hom_ext_pt (f g : ℤ_[l] →+* Per.Ainf l) : f = g := by
  ext1 z
  haveI : IsHausdorff (Ideal.span {((l : ℕ) : Per.Ainf l)}) (Per.Ainf l) := inferInstance
  rw [← sub_eq_zero]
  refine IsHausdorff.haus this _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h := PadicInt.appr_spec n z
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * c := by rw [← hc]; ring
  refine ⟨f c - g c, ?_⟩
  conv_lhs => rw [hz]
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

theorem zD_eq_pt (z : ℤ_[l]) :
    algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (algebraMap ℤ_[l] (Ainf l) z)) = Per.zD l z := by
  have h : algebraMap ℤ_[l] (Ainf l) = Per.zA l := padicInt_hom_ext_pt _ _
  rw [h, zD_alg_pt l z, aDp, RingHom.comp_apply]

theorem matrix_map_smul {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S) (r : R) (M : Matrix (Fin d) (Fin d) R) :
    (r • M).map f = f r • M.map f := by
  ext i j; simp

theorem frob_basis_eq {K : FinExt l} {bk : BK K} {τ : Ainf l} (hτ : bk.IsPer τ) {N d : ℕ}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (hY : Y.map (inclW l) = inclW l τ ^ N • F.T) :
    Y.map WittVector.frobenius = Y * F.A.map bk.ev := by
  have hYij : ∀ i j, inclW l (Y i j) = inclW l τ ^ N * F.T i j := fun i j => by
    simpa using congrFun (congrFun hY i) j
  have hφij : ∀ i j, bk.evW bk.E ^ N * frobW l (F.T i j) = ∑ k, F.T i k * inclW l (bk.ev (F.A k j)) := fun i j => by
    simpa [Matrix.mul_apply, BK.evW] using congrFun (congrFun F.φ i) j
  refine Matrix.ext fun i j => ?_
  apply GlobalTheory.Prism.inclW_injective
  rw [Matrix.map_apply, ← frobW_inclW, hYij, map_mul, map_pow, frobW_inclW, hτ.1, Matrix.mul_apply, map_sum]
  simp_rw [map_mul, hYij]
  calc (inclW l (bk.ev bk.E) * inclW l τ) ^ N * frobW l (F.T i j)
      = inclW l τ ^ N * (bk.evW bk.E ^ N * frobW l (F.T i j)) := by simp only [BK.evW, RingHom.comp_apply]; ring
    _ = _ := by rw [hφij, Finset.mul_sum]; simp only [mul_assoc, Matrix.map_apply]

theorem isUnit_Etau {K : FinExt l} {bk : BK K} {τ : Ainf l} (hτ : bk.IsPer τ) :
    IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E * τ))) := by
  rw [map_mul, map_mul]
  refine IsUnit.mul ?_ ?_
  · have hk : Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)} := by
      rw [GlobalTheory.Per.kerQ_eq_map_ker_theta, ← bk.span_ev, Ideal.map_span, Set.image_singleton]
    have hu := isUnit_gen_pt l hk
    rw [pD_alg_pt] at hu
    rw [aDp, RingHom.comp_apply]
    exact hu
  · have h := GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ 1
    rw [pow_one] at h
    exact ((GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ h).map _

theorem exists_invariant_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∃ (B : Matrix (Fin d) (Fin d) (Per.BdRp l)) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit B ∧ IsUnit Q ∧ (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) ∧ (algebraMap (Per.BdRp l) (Per.BdR l)) (aDp l (bk.ev bk.E * τ)) ^ N • Q = ((Y * F.A.map bk.ev).map (aDp l) * B).map (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q := by
  intro l _ K bk τ hτ C N d ρ F Y hDR hY
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_beta_limit_bdRPlus_deRhamFrame l K bk N d ρ F hDR
  obtain ⟨k1, β1, hβ1, hB1⟩ := hB 1
  have hBu : IsUnit B := GlobalTheory.T.isUnit_bdRPlus_matrix_of_congr_one l K bk d k1 β1 B hβ1.1 hB1
  have hinv := GlobalTheory.T.breuilKisinLatticeFrame_limit_galois_invariant l K bk N d ρ F B hB
  have hφY := frob_basis_eq hτ F Y hY
  have hgal := GlobalTheory.T.frobenius_galois_relation_frame_ainf l K bk τ hτ N d ρ F Y hY
  obtain ⟨v, hv⟩ := isUnit_Etau hτ
  set ι : Per.BdRp l →+* Per.BdR l := algebraMap (Per.BdRp l) (Per.BdR l) with hι
  set j : Ainf l →+* Per.BdR l := ι.comp (aDp l) with hj
  set P : Matrix (Fin d) (Fin d) (Ainf l) := Y.map WittVector.frobenius with hP
  have hjv : j (bk.ev bk.E * τ) = v := hv.symm
  have hM : ((Y * F.A.map bk.ev).map (aDp l) * B).map ι = P.map j * B.map ι := by
    rw [Matrix.map_mul, ← hφY, Matrix.map_map]; rfl
  refine ⟨B, ((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ N • (((Y * F.A.map bk.ev).map (aDp l) * B).map ι), hBu, ?_,
    fun m => ?_, ?_, ?_⟩
  · obtain ⟨Y₀, Y₀', hY₀, hYY⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d ρ F.toPre
    have hY0 : Y₀ = Y := Matrix.ext fun i k => GlobalTheory.Prism.inclW_injective (by
      have := congrFun (congrFun (hY₀.trans hY.symm) i) k
      simpa using this)
    rw [hY0] at hYY
    have hPP : P * Y₀'.map WittVector.frobenius = (bk.ev bk.E * τ) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
      rw [hP, ← Matrix.map_mul, hYY, matrix_map_smul, Matrix.map_one _ (map_zero _) (map_one _), map_pow, hτ.1]
    have hPj : P.map j * (Y₀'.map WittVector.frobenius).map j = ((v : Per.BdR l) ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (Per.BdR l)) := by
      rw [← Matrix.map_mul, hPP, matrix_map_smul, Matrix.map_one _ (map_zero _) (map_one _), map_pow, hjv]
    have hPu : IsUnit (P.map j) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      refine Matrix.isUnit_det_of_right_inverse (B := (((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ (2 * N)) • (Y₀'.map WittVector.frobenius).map j) ?_
      rw [Matrix.mul_smul, hPj, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have hMu : IsUnit (P.map j * B.map ι) := hPu.mul (hBu.map (ι.mapMatrix (m := Fin d)))
    rw [hM, Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
    exact (((v⁻¹).isUnit.pow N).pow _).mul ((Matrix.isUnit_iff_isUnit_det _).1 hMu)
  · obtain ⟨k, β, -, h⟩ := hB m
    exact ⟨k, β, h⟩
  · rw [← hv, smul_smul, ← mul_pow, Units.mul_inv, one_pow, one_smul]
  · intro g
    have hσj : ∀ a : Ainf l, Per.σD (g : GQ l) (j a) = j (Per.σA (g : GQ l) a) := fun a => by
      simp only [hj, RingHom.comp_apply, hι, GlobalTheory.MemLoc.ActLaws.σD_alg, GlobalTheory.MemLoc.ActLaws.σDp_aDp]
    have hσι : ∀ b : Per.BdRp l, Per.σD (g : GQ l) (ι b) = ι (Per.σDp (g : GQ l) b) := fun b =>
      GlobalTheory.MemLoc.ActLaws.σD_alg _ b
    set c : Per.BdR l := ((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ N with hc
    set R : Matrix (Fin d) (Fin d) (Per.BdR l) := (ρ g).map (Per.zD l) with hR
    set S : Matrix (Fin d) (Fin d) (Per.BdR l) := (P.map (Per.σA (g : GQ l))).map j with hS
    set T' : Matrix (Fin d) (Fin d) (Per.BdR l) := (B.map (Per.σDp (g : GQ l))).map ι with hT'
    set Ej : Matrix (Fin d) (Fin d) (Per.BdR l) := ((F.ε g).map ((aDp l).comp WittVector.frobenius)).map ι with hEj
    have f1 : (v : Per.BdR l) ^ N • (R * S) = Per.σD (g : GQ l) (v : Per.BdR l) ^ N • (P.map j * Ej) := by
      have h1 := congrArg (fun M => M.map j) (hgal g)
      simp only [matrix_map_smul, Matrix.map_mul, map_pow] at h1
      rw [hjv, ← hσj, hjv] at h1
      have eR : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map j = R := Matrix.ext fun a b => zD_eq_pt (ρ g a b)
      have eE : ((F.ε g).map WittVector.frobenius).map j = Ej := Matrix.ext fun _ _ => rfl
      rw [eR, eE] at h1
      exact h1
    have f2 : Ej * T' = B.map ι := by
      have h2 := congrArg (fun M => M.map ι) (hinv g)
      simpa only [Matrix.map_mul] using h2
    have f3 : (c • (P.map j * B.map ι)).map (Per.σD (g : GQ l)) = Per.σD (g : GQ l) c • (S * T') := by
      rw [matrix_map_smul, Matrix.map_mul]
      congr 2
      · exact Matrix.ext fun a b => by simp only [Matrix.map_apply, hS, hσj]
      · exact Matrix.ext fun a b => by simp only [Matrix.map_apply, hT', hσι]
    have hw : Per.σD (g : GQ l) c * Per.σD (g : GQ l) (v : Per.BdR l) ^ N = 1 := by
      rw [hc, map_pow, ← mul_pow, ← map_mul, Units.inv_mul, map_one, one_pow]
    have key : (v : Per.BdR l) ^ N • (R * (Per.σD (g : GQ l) c • (S * T'))) = P.map j * B.map ι := by
      rw [Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul, f1,
        Matrix.smul_mul, smul_smul, Matrix.mul_assoc, f2, hw, one_smul]
    rw [hM, f3]
    calc R * (Per.σD (g : GQ l) c • (S * T')) = (c * (v : Per.BdR l) ^ N) • (R * (Per.σD (g : GQ l) c • (S * T'))) := by
          rw [hc, ← mul_pow, Units.inv_mul, one_pow, one_smul]
      _ = c • (P.map j * B.map ι) := by rw [mul_smul, key]

end GlobalTheory.BKLim.InvBasis

end
