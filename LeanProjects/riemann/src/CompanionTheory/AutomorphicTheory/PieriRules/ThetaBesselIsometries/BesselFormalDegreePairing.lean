import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFormalDegreeIdentityStatement
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselSubgroupParameterMeasurePreservingImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselCharacterUnipotentRadicalPropertiesImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.IsHaarOnIffGroupsUnitaryUnipotentImports
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

private theorem hsInner_add_left_theta_bessel_isometries {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A A' C : Wq →L[ℂ] Wp) :
    B.hsInner (A + A') C = B.hsInner A C + B.hsInner A' C := by
  unfold Formalism.FourierDecayAlt.B.hsInner
  rw [← inner_add_right]
  congr 1

private theorem hsInner_smul_lemma_2 {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A C : Wq →L[ℂ] Wp) :
    B.hsInner (c • A) C = c * B.hsInner A C := by
  unfold Formalism.FourierDecayAlt.B.hsInner
  rw [← inner_smul_right]
  congr 1

theorem besPhInt_bilin {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X X' : Wq →L[ℂ] Wp) :
    ∃ T : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wq) →L[ℂ] ℂ, ∀ P Q, T P Q = B.hsInner (P.comp (X.comp Q)) X' := by
  let f : (Wp →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wq) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun P Q => B.hsInner (P.comp (X.comp Q)) X')
      (fun P₁ P₂ Q => by rw [ContinuousLinearMap.add_comp, hsInner_add_left_theta_bessel_isometries])
      (fun c P Q => by rw [ContinuousLinearMap.smul_comp, hsInner_smul_lemma_2, smul_eq_mul])
      (fun P Q₁ Q₂ => by
        rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_add, hsInner_add_left_theta_bessel_isometries])
      (fun c P Q => by
        rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul, hsInner_smul_lemma_2,
          smul_eq_mul])
  let g : (Wp →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wq) →L[ℂ] ℂ :=
    (LinearMap.toContinuousLinearMap : ((Wq →L[ℂ] Wq) →ₗ[ℂ] ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ f
  exact ⟨LinearMap.toContinuousLinearMap g, fun P Q => rfl⟩

theorem besPhInt_rank {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X X' : Wq →L[ℂ] Wp)
    (a a' : Wp) (b b' : Wq) :
    B.hsInner (((innerSL ℂ a).smulRight a').comp (X.comp ((innerSL ℂ b').smulRight b))) X' =
      ⟪a, X b⟫_ℂ * star ⟪a', X' b'⟫_ℂ := by
  have key : ∀ i, ⟪X' (stdOrthonormalBasis ℂ Wq i),
      (((innerSL ℂ a).smulRight a').comp (X.comp ((innerSL ℂ b').smulRight b)))
        (stdOrthonormalBasis ℂ Wq i)⟫_ℂ =
      ⟪a, X b⟫_ℂ * (⟪b', stdOrthonormalBasis ℂ Wq i⟫_ℂ *
        ⟪stdOrthonormalBasis ℂ Wq i, (ContinuousLinearMap.adjoint X') a'⟫_ℂ) := by
    intro i
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      map_smul, inner_smul_right, ContinuousLinearMap.adjoint_inner_right, smul_eq_mul]
    ring
  unfold Formalism.FourierDecayAlt.B.hsInner Formalism.FourierDecayAlt.B.hsVec
  simp only [PiLp.inner_apply, PiLp.toLp_apply, key]
  rw [← Finset.mul_sum, OrthonormalBasis.sum_inner_mul_inner, ContinuousLinearMap.adjoint_inner_right]
  congr 1
  exact (inner_conj_symm (X' b') a').symm

theorem besPhInt_xi {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    B.xiTau D (1, 1) p = Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of p.1.2) *
      star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of p.2.2)) := by
  unfold Formalism.FourierDecayAlt.B.xiTau Formalism.FourierDecayAlt.B.lam Formalism.QuantumDeterminants.psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

private theorem continuous_ell_matrix_of {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) :
    Continuous (fun q : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.ell k r z (Matrix.of q)) := by
  unfold Formalism.QuantumDeterminants.ell
  refine continuous_finsetSum _ (fun a _ => ?_)
  by_cases h : (a : ℕ) + 1 < r
  · simp only [dif_pos h, Matrix.of_apply]
    fun_prop
  · simp only [dif_neg h, Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact continuous_finsetSum _ (fun j _ => by fun_prop)

theorem besPhInt_xi_cont {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) :
    Continuous (B.xiTau D (1, 1)) := by
  have h1 : Continuous (fun p : B.SS k r => Formalism.QuantumDeterminants.ell k r D.z (Matrix.of p.1.2)) :=
    (continuous_ell_matrix_of D.z).comp (continuous_snd.comp continuous_fst)
  have h2 : Continuous (fun p : B.SS k r => Formalism.QuantumDeterminants.ell k r D.z' (Matrix.of p.2.2)) :=
    (continuous_ell_matrix_of D.z').comp (continuous_snd.comp continuous_snd)
  unfold Formalism.FourierDecayAlt.B.xiTau Formalism.FourierDecayAlt.B.lam
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    ((continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h1))).sub
      (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h2))))))

private theorem isUnit_det_of_mem_UH_Hpk_of_inv_mem {k r : ℕ} (hk : 1 ≤ k)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hg' : g⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    IsUnit g.det := by
  by_contra hu
  rw [Matrix.nonsing_inv_apply_not_isUnit g hu] at hg'
  have h0 : Formalism.QuantumDeterminants.Hpk k r = 0 := by
    have h1 := hg'
    simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Matrix.conjTranspose_zero, Matrix.zero_mul] at h1
    exact h1.symm
  have hr : r < 2 * r + k + 1 := by omega
  have hk0 : k ≠ 0 := by omega
  have h2 := congrFun (congrFun h0 ⟨r, hr⟩) ⟨r, hr⟩
  simp [Formalism.QuantumDeterminants.Hpk, hk0] at h2

private theorem integrable_and_integral_prod_bilin_eq_apply_integrals {α β E F G : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    (T : E →L[ℂ] F →L[ℂ] G) {u : α → E} {v : β → F} (hu : Integrable u μ) (hv : Integrable v ν) :
    Integrable (fun p : α × β => T (u p.1) (v p.2)) (μ.prod ν) ∧
      ∫ p, T (u p.1) (v p.2) ∂(μ.prod ν) = T (∫ a, u a ∂μ) (∫ b, v b ∂ν) := by
  have hint : Integrable (fun p : α × β => T (u p.1) (v p.2)) (μ.prod ν) := by
    refine Integrable.mono' ((MeasureTheory.Integrable.mul_prod hu.norm hv.norm).const_mul ‖T‖) ?_ ?_
    · exact T.continuous₂.comp_aestronglyMeasurable₂ hu.aestronglyMeasurable.comp_fst
        hv.aestronglyMeasurable.comp_snd
    · exact Filter.Eventually.of_forall (fun p => by
        have h1 := T.le_opNorm₂ (u p.1) (v p.2)
        simpa [mul_assoc] using h1)
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  have h1 : ∀ a, ∫ b, T (u a) (v b) ∂ν = T (u a) (∫ b, v b ∂ν) :=
    fun a => (T (u a)).integral_comp_comm hv
  simp_rw [h1]
  have h2 := (T.flip (∫ b, v b ∂ν)).integral_comp_comm hu
  simpa using h2

theorem integral_xi_mul_Ph : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ x' ∈ R.TK, ∀ y' ∈ R.TK, ∀ X X' : Wq →L[ℂ] Wp, Integrable (B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X')) D.μSS ∧ ∫ p, B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p ∂D.μSS = ⟪l x, X (l' y)⟫_ℂ * star ⟪l x', X' (l' y')⟫_ℂ / (dd : ℂ) := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' dd hDG _ _ hl hl' hdd x hx y hy x' hx' y' hy' X X'
  classical
  have hrep := rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDG
  have hmul := hrep.1
  have hone := hrep.2.1
  have hunit := hrep.2.2.1
  have hTKsm := hrep.2.2.2.2.1
  have hWpi : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r D.z) D.μW :=
    ((_root_.GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW).2.2 D.z D.z_mem D.T_pos D.k_pos).2 D.haarW
  have hNpi : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) D.μN :=
    (_root_.GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μN).2.1.2 D.haarN
  have hW'pi : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r D.z') D.μW' :=
    ((_root_.GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW').2.2 D.z' D.z'_mem D.T'_pos D.k_pos).2 D.haarW'
  haveI : SigmaFinite D.μW := hWpi.1
  haveI : SigmaFinite D.μN := hNpi.1
  haveI : SigmaFinite D.μW' := hW'pi.1
  have h55 := _root_.GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos hWpi hNpi
  have h55' := _root_.GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos hW'pi hNpi
  have h54 := _root_.GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  have h54' := _root_.GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  obtain ⟨Φ, hΦ, hΦd⟩ : ∃ Φ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      MeasurePreserving Φ (D.μW.prod D.μN) (D.μW.prod D.μN) ∧
        ∀ q, Φ q = ((fun i j => (Matrix.of q.1)⁻¹ i j), (fun i j => (Matrix.of q.2)⁻¹ i j)) :=
    ⟨_, h55.2.2.2.2.1, fun q => rfl⟩
  obtain ⟨Ψ, hΨ, hΨd⟩ : ∃ Ψ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      MeasurePreserving Ψ (D.μW'.prod D.μN) (D.μW'.prod D.μN) ∧
        ∀ q, Ψ q = ((fun i j => Matrix.of q.1 i j),
          (fun i j => ((Matrix.of q.1)⁻¹ * Matrix.of q.2 * Matrix.of q.1) i j)) :=
    ⟨_, h55'.2.2.2.1, fun q => rfl⟩
  obtain ⟨U, hUd⟩ : ∃ U : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Wp →L[ℂ] Wp, ∀ q, U q =
      (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of q.2) *
        ⟪(R.σ (Matrix.of q.2 * Matrix.of q.1)) x, x'⟫_ℂ) • D.π (Matrix.of q.1) := ⟨_, fun q => rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Wq →L[ℂ] Wq, ∀ q, V q =
      (star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of q.2)) *
        ⟪y', (R.σ (Matrix.of q.2 * Matrix.of q.1)) y⟫_ℂ) • D.π' (Matrix.of q.1)⁻¹ := ⟨_, fun q => rfl⟩
  have hUeq : ∀ q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, Matrix.of q.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z →
      Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset k r →
      Formalism.FourierDecayAlt.ThreeDimData.beInt D.z Formalism.QuantumDeterminants.cStd D.π R.σ x' x (Φ q) = U q := by
    intro q hH hN
    obtain ⟨hNinv, hψinv⟩ := h54.2.2.1 _ hN
    have hHinv := (h54.2.2.2.2.1 _ hH _ hH).2.1
    have hHG := (h54.2.2.2.2.1 _ hH _ hH).2.2
    have hHinvG := (h54.2.2.2.2.1 _ hHinv _ hHinv).2.2
    have hNG := h54.2.2.2.2.2 _ hN
    have hNinvG := h54.2.2.2.2.2 _ hNinv
    have huH := isUnit_det_of_mem_UH_Hpk_of_inv_mem D.k_pos hH.1 hHinv.1
    have huN := isUnit_det_of_mem_UH_Hpk_of_inv_mem D.k_pos hN.1 hNinv.1
    have hin : ⟪x, (R.σ ((Matrix.of q.1)⁻¹ * (Matrix.of q.2)⁻¹)) x'⟫_ℂ =
        ⟪(R.σ (Matrix.of q.2 * Matrix.of q.1)) x, x'⟫_ℂ := by
      rw [hmul _ hNG _ hHG, hmul _ hHinvG _ hNinvG]
      calc ⟪x, (R.σ (Matrix.of q.1)⁻¹) ((R.σ (Matrix.of q.2)⁻¹) x')⟫_ℂ
          = ⟪(R.σ (Matrix.of q.1)) x,
              (R.σ (Matrix.of q.1)) ((R.σ (Matrix.of q.1)⁻¹) ((R.σ (Matrix.of q.2)⁻¹) x'))⟫_ℂ :=
            (hunit _ hHG _ _).symm
        _ = ⟪(R.σ (Matrix.of q.1)) x, (R.σ (Matrix.of q.2)⁻¹) x'⟫_ℂ := by
            rw [← hmul _ hHG _ hHinvG, Matrix.mul_nonsing_inv _ huH, hone]
        _ = ⟪(R.σ (Matrix.of q.2)) ((R.σ (Matrix.of q.1)) x),
              (R.σ (Matrix.of q.2)) ((R.σ (Matrix.of q.2)⁻¹) x')⟫_ℂ :=
            (hunit _ hNG _ _).symm
        _ = ⟪(R.σ (Matrix.of q.2)) ((R.σ (Matrix.of q.1)) x), x'⟫_ℂ := by
            rw [← hmul _ hNG _ hNinvG, Matrix.mul_nonsing_inv _ huN, hone]
    rw [hΦd, hUd]
    show (⟪x, (R.σ ((Matrix.of q.1)⁻¹ * (Matrix.of q.2)⁻¹)) x'⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of q.2)⁻¹)) • D.π ((Matrix.of q.1)⁻¹)⁻¹ = _
    rw [hψinv, star_star, Matrix.nonsing_inv_nonsing_inv _ huH, hin]
    congr 1
    ring
  have hVeq : ∀ q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, Matrix.of q.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z' →
      Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset k r →
      Formalism.FourierDecayAlt.ThreeDimData.beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y y' (Ψ q) = V q := by
    intro q hH hN
    have hHinv := (h54'.2.2.2.2.1 _ hH _ hH).2.1
    have huH := isUnit_det_of_mem_UH_Hpk_of_inv_mem D.k_pos hH.1 hHinv.1
    have hψc := (h54'.2.2.2.1 _ hH _ hN).2.2.2
    have hm : Matrix.of q.1 * ((Matrix.of q.1)⁻¹ * Matrix.of q.2 * Matrix.of q.1) =
        Matrix.of q.2 * Matrix.of q.1 := by
      rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ huH, one_mul]
    rw [hΨd, hVd]
    show (⟪y', (R.σ (Matrix.of q.1 * ((Matrix.of q.1)⁻¹ * Matrix.of q.2 * Matrix.of q.1))) y⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd ((Matrix.of q.1)⁻¹ * Matrix.of q.2 * Matrix.of q.1))) •
        D.π' (Matrix.of q.1)⁻¹ = _
    rw [hm, hψc]
    congr 1
    ring
  have hbe := hl.2 x' (hTKsm x' hx') x hx
  have hbe' := hl'.2 y (hTKsm y hy) y' hy'
  have hUi : Integrable U (D.μW.prod D.μN) ∧
      ∫ q, U q ∂(D.μW.prod D.μN) = (innerSL ℂ (l x)).smulRight (l x') := by
    have hcomp : (fun q => Formalism.FourierDecayAlt.ThreeDimData.beInt D.z Formalism.QuantumDeterminants.cStd D.π R.σ x' x (Φ q))
        =ᵐ[D.μW.prod D.μN] U :=
      h55.2.2.2.2.2.mono (fun q hq => hUeq q hq.1 hq.2)
    have hint1 : Integrable (fun q => Formalism.FourierDecayAlt.ThreeDimData.beInt D.z Formalism.QuantumDeterminants.cStd D.π R.σ x' x (Φ q))
        (D.μW.prod D.μN) :=
      (hΦ.integrable_comp hbe.1.aestronglyMeasurable).mpr hbe.1
    refine ⟨hint1.congr hcomp, ?_⟩
    rw [← integral_congr_ae hcomp, ← integral_map hΦ.measurable.aemeasurable
      (by rw [hΦ.map_eq]; exact hbe.1.aestronglyMeasurable), hΦ.map_eq]
    exact hbe.2
  have hVi : Integrable V (D.μW'.prod D.μN) ∧
      ∫ q, V q ∂(D.μW'.prod D.μN) = (innerSL ℂ (l' y')).smulRight (l' y) := by
    have hcomp : (fun q => Formalism.FourierDecayAlt.ThreeDimData.beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y y' (Ψ q))
        =ᵐ[D.μW'.prod D.μN] V :=
      h55'.2.2.2.2.2.mono (fun q hq => hVeq q hq.1 hq.2)
    have hint1 : Integrable (fun q => Formalism.FourierDecayAlt.ThreeDimData.beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y y' (Ψ q))
        (D.μW'.prod D.μN) :=
      (hΨ.integrable_comp hbe'.1.aestronglyMeasurable).mpr hbe'.1
    refine ⟨hint1.congr hcomp, ?_⟩
    rw [← integral_congr_ae hcomp, ← integral_map hΨ.measurable.aemeasurable
      (by rw [hΨ.map_eq]; exact hbe'.1.aestronglyMeasurable), hΨ.map_eq]
    exact hbe'.2
  have haeSS : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), D.inSS p := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := D.μW.prod D.μN)
      (ν := D.μW'.prod D.μN)).ae h55.2.2.2.2.2
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := D.μW.prod D.μN)
      (ν := D.μW'.prod D.μN)).ae h55'.2.2.2.2.2
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨hp1.1, hp1.2, hp2.1, hp2.2⟩
  obtain ⟨T, hT⟩ := besPhInt_bilin X X'
  have hFub := integrable_and_integral_prod_bilin_eq_apply_integrals T hUi.1 hVi.1
  have hpt : ∀ p : B.SS k r, D.inSS p →
      B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p =
        (1 / (dd : ℂ)) * T (U p.1) (V p.2) := by
    intro p hp
    rw [(Gp91.GlobalTheory.T.bessel_formal_degree_identity hH k r ε mu R Wp Wq D dd hDG hdd x y x' y' X X' p hp).2, besPhInt_xi, hT,
      hUd, hVd, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, hsInner_smul_lemma_2, hsInner_smul_lemma_2]
    simp only [Formalism.FourierDecayAlt.JF.sL, Formalism.FourierDecayAlt.JF.sR]
    ring
  have hae : (fun p => B.xiTau D (1, 1) p *
      B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p)
      =ᵐ[D.μSS] fun p => (1 / (dd : ℂ)) * T (U p.1) (V p.2) :=
    haeSS.mono (fun p hp => hpt p hp)
  have hF1 : Integrable (fun p => T (U p.1) (V p.2)) D.μSS := hFub.1
  have hF2 : ∫ p, T (U p.1) (V p.2) ∂D.μSS =
      T (∫ q, U q ∂(D.μW.prod D.μN)) (∫ q, V q ∂(D.μW'.prod D.μN)) := hFub.2
  have hint2 : Integrable (fun p => B.xiTau D (1, 1) p *
      B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p) D.μSS :=
    (hF1.const_mul (1 / (dd : ℂ))).congr hae.symm
  have hxi := besPhInt_xi_cont D
  have hnorm : ∀ p, ‖B.xiTau D (1, 1) p‖ = 1 := by
    intro p
    unfold Formalism.FourierDecayAlt.B.xiTau
    exact Complex.norm_exp_I_mul_ofReal _
  refine ⟨?_, ?_⟩
  · have hint3 : Integrable (fun p => star (B.xiTau D (1, 1) p) * (B.xiTau D (1, 1) p *
        B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p)) D.μSS :=
      hint2.congr' ((hxi.star.aestronglyMeasurable).mul hint2.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun p => by simp [hnorm]))
    refine hint3.congr (Filter.Eventually.of_forall (fun p => ?_))
    beta_reduce
    rw [← mul_assoc, Complex.star_def, Complex.conj_mul', hnorm]
    simp
  · rw [integral_congr_ae hae, integral_const_mul, hF2, hUi.2, hVi.2, hT,
      besPhInt_rank X X' (l x) (l x') (l' y) (l' y')]
    ring

end GlobalTheory
