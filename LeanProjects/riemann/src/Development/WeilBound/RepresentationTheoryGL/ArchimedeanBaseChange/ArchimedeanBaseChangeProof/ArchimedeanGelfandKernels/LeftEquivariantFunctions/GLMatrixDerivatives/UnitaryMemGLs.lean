import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeStructure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate NNReal ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.GLSubgroupConjTransposeClosure

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

local instance : SecondCountableTopology (Mat n) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
local instance : LocallyCompactSpace (Mat n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
local instance : SecondCountableTopology (G n) :=
  have : SecondCountableTopology (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology
local instance : LocallyCompactSpace (G n) := inferInstanceAs (LocallyCompactSpace (Mat n)ˣ)

theorem hOf_oPt : hOf (oPt n) = 1 := by
  have h := GlobalTheory.CompanionTheory.ConeHaar.hOf_coords (n := n) 1 isHermitian_one
  have e : oPt n = fun p => ((hb p * 1).trace).re := by funext p; simp [oPt, coords]
  rw [e]; exact h

theorem oPt_mem : oPt n ∈ cone n := by
  show (hOf (oPt n)).PosDef
  rw [hOf_oPt]; exact PosDef.one

def thE : G n ≃ₜ* G n where
  toFun y := (star y)⁻¹
  invFun y := (star y)⁻¹
  left_inv y := by simp [star_inv]
  right_inv y := by simp [star_inv]
  map_mul' x y := by simp [star_mul, _root_.mul_inv_rev]
  continuous_toFun := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · show Continuous fun y : G n => (((star y)⁻¹ : G n) : Mat n)
      have e : ∀ y : G n, (((star y)⁻¹ : G n) : Mat n) = star (((y⁻¹ : G n)) : Mat n) := fun y => by
        rw [← star_inv, Units.coe_star]
      simp only [e]; exact Units.continuous_coe_inv.star
    · show Continuous fun y : G n => ((((star y)⁻¹)⁻¹ : G n) : Mat n)
      simp only [inv_inv, Units.coe_star]; exact Units.continuous_val.star
  continuous_invFun := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · show Continuous fun y : G n => (((star y)⁻¹ : G n) : Mat n)
      have e : ∀ y : G n, (((star y)⁻¹ : G n) : Mat n) = star (((y⁻¹ : G n)) : Mat n) := fun y => by
        rw [← star_inv, Units.coe_star]
      simp only [e]; exact Units.continuous_coe_inv.star
    · show Continuous fun y : G n => ((((star y)⁻¹)⁻¹ : G n) : Mat n)
      simp only [inv_inv, Units.coe_star]; exact Units.continuous_val.star

theorem thE_val (y : G n) : ((thE y : G n) : Mat n) = (y : Mat n)ᴴ⁻¹ := by
  show (((star y)⁻¹ : G n) : Mat n) = _
  rw [Matrix.coe_units_inv]; rfl

theorem thE_thE : (thE (n := n)).trans thE = ContinuousMulEquiv.refl _ := by
  ext y; simp [thE, star_inv]

theorem map_thE [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] [μ.Regular] :
    μ.map thE = μ := by
  have h1 : mulEquivHaarChar (thE (n := n)) = 1 := by
    have h := mulEquivHaarChar_trans (φ := (thE (n := n))) (ψ := thE)
    rw [thE_thE, mulEquivHaarChar_refl] at h
    have hpos := mulEquivHaarChar_pos (thE (n := n))
    have h' : ((mulEquivHaarChar (thE (n := n)) : ℝ)) * (mulEquivHaarChar (thE (n := n)) : ℝ) = 1 := by
      exact_mod_cast h.symm
    have hp : (0 : ℝ) < mulEquivHaarChar (thE (n := n)) := by exact_mod_cast hpos
    have : (mulEquivHaarChar (thE (n := n)) : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  have := mulEquivHaarChar_smul_map μ (thE (n := n))
  rwa [h1, one_smul] at this

theorem mem_GLs_mul {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem inv_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n :=
  (Matrix.isUnit_nonsing_inv_det x (isUnit_iff_ne_zero.2 hx)).ne_zero

theorem cT_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : xᴴ ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_conjTranspose, star_ne_zero] at *
  exact hx

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by simp [GLs]

theorem unitary_mem_GLs (κ : Matrix.unitaryGroup (Fin n) ℂ) : κ.1 ∈ GLs n :=
  (Matrix.UnitaryGroup.det_isUnit κ).ne_zero

theorem hs_cT (y : Mat n) : GlobalTheory.CompanionTheory.LengthGL.hs yᴴ = GlobalTheory.CompanionTheory.LengthGL.hs y := by
  unfold GlobalTheory.CompanionTheory.LengthGL.hs
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

theorem lg_cT {y : Mat n} (hy : y ∈ GLs n) : lg yᴴ = lg y := by
  rw [GlobalTheory.CompanionTheory.LengthGL.lg_eq, GlobalTheory.CompanionTheory.LengthGL.lg_eq, hs_cT, ← Matrix.conjTranspose_nonsing_inv, hs_cT]

theorem lg_cT_inv {y : Mat n} (hy : y ∈ GLs n) : lg yᴴ⁻¹ = lg y := by
  rw [GlobalTheory.CompanionTheory.LengthGL.lg_inv (cT_mem_GLs hy), lg_cT hy]

theorem diag_unitary {z : Fin n → ℂ} (hz : ∀ a, ‖z a‖ = 1) : diagonal z ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext a
  simp only [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz a]
  simp

theorem lg_diag_mul {z : Fin n → ℂ} (hz : ∀ a, ‖z a‖ = 1) (x : Mat n) : lg (diagonal z * x) = lg x := by
  have h := GlobalTheory.CompanionTheory.LengthGL.lg_unitary x ⟨diagonal z, diag_unitary hz⟩ 1
  simpa using h

def trL {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (A : V →L[ℂ] V) :
    (V →L[ℂ] V) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℂ V) ∘ₗ (ContinuousLinearMap.coeLM ℂ) ∘ₗ (LinearMap.mulLeft ℂ A))

theorem trL_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (A B : V →L[ℂ] V) :
    trL A B = LinearMap.trace ℂ V ((A * B : V →L[ℂ] V) : V →ₗ[ℂ] V) := rfl

theorem end0 : End0 := by
  intro n lam E Fr ε ι S Γ T hCx _ _ μ _ σ c hσ hσ2 hform k val hkc hkeq hkΓ hksupp heig d z hd hz hz2
  obtain ⟨Rk, hRk⟩ := hksupp
  have hdG : d.val ∈ GLs n := GlobalTheory.CompanionTheory.LengthGL.mem_GLs_val d

  set F : Mat n → ℂ := fun y =>
    LinearMap.trace ℂ E.V ((Γ * S 0 * (k (d.val * yᴴ⁻¹) * Γ * T * Fr y⁻¹) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) with hFdef

  have hu0 : σ (oPt n) * (σ (oPt n))ᴴ = 1 := by rw [hσ2 _ oPt_mem, hOf_oPt]
  have hu0' : (σ (oPt n))ᴴ * σ (oPt n) = 1 := mul_eq_one_comm.mp hu0
  set U0 : Matrix.unitaryGroup (Fin n) ℂ := ⟨σ (oPt n), Matrix.mem_unitaryGroup_iff.2 hu0⟩ with hU0
  have hU0inv : (σ (oPt n))⁻¹ = (U0⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 := by
    rw [Matrix.inv_eq_left_inv hu0']; rfl

  have hpt : ∀ v ∈ cone n,
      LinearMap.trace ℂ E.V ((Γ * S 0 * Kc σ c Fr k Γ T d.val (oPt n, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
        F (σ v) * ((c : ℂ) * ((hOf v).det ^ n)⁻¹) := by
    intro v hv
    have hyG : σ v ∈ GLs n := GlobalTheory.CompanionTheory.ConeHaar.det_ne_of_gram (hσ2 v hv) hv
    have hmem : d.val * (σ v)ᴴ⁻¹ ∈ GLs n := mem_GLs_mul hdG (inv_mem_GLs (cT_mem_GLs hyG))
    have hk1 : k ((σ (oPt n))⁻¹ * d.val * (σ v)ᴴ⁻¹) = E.ρ U0⁻¹ * k (d.val * (σ v)ᴴ⁻¹) := by
      have h := hkeq _ hmem U0⁻¹ 1
      rw [map_one, mul_one] at h
      rw [← h, hU0inv, mul_assoc]; simp
    have hFr0 : Fr (σ (oPt n)) = E.ρ U0 := hCx.onK U0
    have hρ : E.ρ U0 * E.ρ U0⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hKf : Kf Fr k Γ T d.val (σ (oPt n)) (σ v) = k (d.val * (σ v)ᴴ⁻¹) * Γ * T * Fr (σ v)⁻¹ := by
      unfold Kf
      rw [hk1, hFr0, ← mul_assoc (E.ρ U0), hρ, one_mul]
    simp only [Kc]
    rw [hKf, mul_smul_comm, ContinuousLinearMap.coe_smul, map_smul, smul_eq_mul, mul_comm]

  have hcont_ci : ContinuousOn (fun y : Mat n => yᴴ⁻¹) (GLs n) := by
    have h1 : ContinuousOn (fun y : Mat n => y⁻¹) (GLs n) :=
      GlobalTheory.CompanionTheory.LengthGL.contDiffOn_inv.continuousOn
    have h2 : Continuous (fun y : Mat n => yᴴ) := continuous_id.matrix_conjTranspose
    exact h1.comp h2.continuousOn fun y hy => cT_mem_GLs hy
  have hcont_k : ContinuousOn (fun y : Mat n => k (d.val * yᴴ⁻¹)) (GLs n) :=
    hkc.comp (continuousOn_const.mul hcont_ci) fun y hy => mem_GLs_mul hdG (inv_mem_GLs (cT_mem_GLs hy))
  have hcont_Fr : ContinuousOn (fun y : Mat n => Fr y⁻¹) (GLs n) :=
    hCx.smooth.continuousOn.comp GlobalTheory.CompanionTheory.LengthGL.contDiffOn_inv.continuousOn fun y hy => inv_mem_GLs hy
  have hcont_B : ContinuousOn (fun y : Mat n => k (d.val * yᴴ⁻¹) * Γ * T * Fr y⁻¹) (GLs n) :=
    ((hcont_k.mul continuousOn_const).mul continuousOn_const).mul hcont_Fr
  have hFcont : ContinuousOn F (GLs n) := by
    have := (trL (Γ * S 0)).continuous.comp_continuousOn hcont_B
    exact this
  have hkz : ∀ y ∈ GLs n, Rk < lg y → k (d.val * yᴴ⁻¹) = 0 := by
    intro y hy hlt
    apply hRk _ (mem_GLs_mul hdG (inv_mem_GLs (cT_mem_GLs hy)))
    rw [hd, lg_diag_mul hz, lg_cT_inv hy]; exact hlt
  have hFsupp : ∃ R, ∀ y ∈ GLs n, R < lg y → F y = 0 :=
    ⟨Rk, fun y hy hlt => by simp only [hFdef, hkz y hy hlt, zero_mul, mul_zero, ContinuousLinearMap.coe_zero, map_zero]⟩
  have hFinv : ∀ y ∈ GLs n, ∀ κ : Matrix.unitaryGroup (Fin n) ℂ, F (y * κ.1) = F y := by
    intro y hy κ
    have hκ : κ.1 * star κ.1 = 1 := Matrix.mem_unitaryGroup_iff.1 κ.2
    have hκ' : star κ.1 * κ.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 κ.2
    have hci : (y * κ.1)ᴴ⁻¹ = yᴴ⁻¹ * κ.1 := by
      have hstar : (κ.1)ᴴ⁻¹ = κ.1 := by
        rw [← Matrix.star_eq_conjTranspose]; exact Matrix.inv_eq_right_inv hκ'
      rw [Matrix.conjTranspose_mul, Matrix.mul_inv_rev, hstar]
    have hinvκ : (y * κ.1)⁻¹ = (κ⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 * y⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hκ']; rfl
    have hmem : d.val * yᴴ⁻¹ ∈ GLs n := mem_GLs_mul hdG (inv_mem_GLs (cT_mem_GLs hy))
    have hk2 : k (d.val * (y * κ.1)ᴴ⁻¹) = k (d.val * yᴴ⁻¹) * E.ρ κ := by
      have h := hkeq _ hmem 1 κ
      rw [map_one, one_mul] at h
      rw [hci, ← h]; congr 1; simp [mul_assoc]
    have hFr2 : Fr (y * κ.1)⁻¹ = E.ρ κ⁻¹ * Fr y⁻¹ := by
      rw [hinvκ, hCx.mul _ (unitary_mem_GLs _) _ (inv_mem_GLs hy), hCx.onK]
    have hΓρ : Γ * E.ρ κ = E.ρ κ * Γ := by rw [← hCx.onK κ]; exact hCx.ΓFr _ (unitary_mem_GLs κ)
    have hTρ : T * E.ρ κ = E.ρ κ * T := hCx.TK κ
    have hρρ : E.ρ κ * E.ρ κ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hop : k (d.val * yᴴ⁻¹) * E.ρ κ * Γ * T * (E.ρ κ⁻¹ * Fr y⁻¹) = k (d.val * yᴴ⁻¹) * Γ * T * Fr y⁻¹ := by
      simp only [mul_assoc]
      rw [← mul_assoc (E.ρ κ) Γ, ← hΓρ, mul_assoc Γ (E.ρ κ), ← mul_assoc (E.ρ κ) T, ← hTρ, mul_assoc T (E.ρ κ),
        ← mul_assoc (E.ρ κ) (E.ρ κ⁻¹), hρρ, one_mul]
    simp only [hFdef]
    rw [hk2, hFr2, hop]

  have hcone : ∫ v in cone n,
      LinearMap.trace ℂ E.V ((Γ * S 0 * Kc σ c Fr k Γ T d.val (oPt n, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
        ∫ y : G n, F y.val ∂μ := by
    rw [setIntegral_congr_fun (GlobalTheory.CompanionTheory.ConeHaar.cone_open n).measurableSet hpt, hform F hFcont hFsupp hFinv,
      ← integral_const_mul]
    congr 1; funext v; ring
  rw [hcone]

  set B : G n → (E.V →L[ℂ] E.V) := fun y => k (d.val * (y.val)ᴴ⁻¹) * Γ * T * Fr (y.val)⁻¹ with hBdef
  have hBcont : Continuous B :=
    hcont_B.comp_continuous Units.continuous_val fun y => GlobalTheory.CompanionTheory.LengthGL.mem_GLs_val y
  have hBsupp : HasCompactSupport B :=
    HasCompactSupport.intro (GlobalTheory.CompanionTheory.LengthGL.isCompact_G (n := n) Rk) fun y hy => by
      simp only [Set.mem_setOf_eq, not_le] at hy
      simp only [hBdef, hkz _ (GlobalTheory.CompanionTheory.LengthGL.mem_GLs_val y) hy, zero_mul]
  have hBint : Integrable B μ := hBcont.integrable_of_hasCompactSupport hBsupp
  have hIF : ∫ y : G n, F y.val ∂μ = trL (Γ * S 0) (∫ y, B y ∂μ) := by
    rw [← (trL (Γ * S 0)).integral_comp_comm hBint]
    rfl

  have hkey : (∫ y, B y ∂μ) * S 0 = val (infOf lam) • (Fr d.val * T * S 0) := by
    refine ContinuousLinearMap.ext fun w => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.integral_apply hBint (S 0 w)]
    set v := Fr d.val (T (S 0 w)) with hv
    have hS0v : S 0 v = v := by
      rw [hv]
      have e1 : S 0 (Fr d.val (T (S 0 w))) = (S 0 * Fr d.val) (T (S 0 w)) := rfl
      rw [e1, hCx.sym_zero_comm_frame _ hdG, ContinuousLinearMap.mul_apply]
      have e2 : S 0 (T (S 0 w)) = (S 0 * T) (S 0 w) := rfl
      rw [e2, ← hCx.time_comm_sym_zero, ContinuousLinearMap.mul_apply]
      have e3 : S 0 (S 0 w) = (S 0 * S 0) w := rfl
      rw [e3, hCx.S0sq]
    set f : Mat n → E.V := fun x => Fr x⁻¹ (S 0 v) with hfdef
    set hh : G n → E.V := fun y' => k y'.val (Fr ((y'.val)⁻¹ * d.val) (T (S 0 w))) with hhdef
    have hBw : ∀ y : G n, B y (S 0 w) = hh (d * thE y) := by
      intro y
      have hyG := GlobalTheory.CompanionTheory.LengthGL.mem_GLs_val y
      have hcG : (y.val)ᴴ ∈ GLs n := cT_mem_GLs hyG
      have hθ : T (Fr (y.val)⁻¹ (S 0 w)) = Fr (y.val)ᴴ (T (S 0 w)) := by
        have h := hCx.S0θ _ hcG
        rw [Matrix.conjTranspose_conjTranspose] at h
        have := congrArg (fun A : E.V →L[ℂ] E.V => A w) h
        simpa [ContinuousLinearMap.mul_apply] using this
      have hΓ : Γ (Fr (y.val)ᴴ (T (S 0 w))) = Fr (y.val)ᴴ (T (S 0 w)) := by
        have h1 : Γ (Fr (y.val)ᴴ (T (S 0 w))) = Fr (y.val)ᴴ (Γ (T (S 0 w))) := by
          have := congrArg (fun A : E.V →L[ℂ] E.V => A (T (S 0 w))) (hCx.ΓFr _ hcG)
          simpa [ContinuousLinearMap.mul_apply] using this
        have h2 : Γ (T (S 0 w)) = T (Γ (S 0 w)) := by
          have := congrArg (fun A : E.V →L[ℂ] E.V => A (S 0 w)) hCx.ΓT
          simpa [ContinuousLinearMap.mul_apply] using this
        have h3 : Γ (S 0 w) = S 0 w := by
          have := congrArg (fun A : E.V →L[ℂ] E.V => A w) hCx.S0Γ
          simpa [ContinuousLinearMap.mul_apply] using this
        rw [h1, h2, h3]
      have hval : (d * thE y).val = d.val * (y.val)ᴴ⁻¹ := by rw [Units.val_mul, thE_val]
      have hinv : ((d * thE y).val)⁻¹ * d.val = (y.val)ᴴ := by
        rw [hval, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 hcG), mul_assoc,
          Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdG), mul_one]
      simp only [hBdef, hhdef, ContinuousLinearMap.mul_apply]
      rw [hθ, hΓ, hinv, hval]
    have hmp : MeasurePreserving (thE (n := n)) μ μ := ⟨thE.continuous.measurable, map_thE μ⟩
    have hI1 : ∫ y, B y (S 0 w) ∂μ = ∫ y, hh y ∂μ := by
      simp only [hBw]
      rw [hmp.integral_comp thE.toHomeomorph.measurableEmbedding (fun y => hh (d * y))]
      exact integral_mul_left_eq_self hh d
    have hfCE : f ∈ CE E := by
      refine ⟨?_, fun g hg κ => ?_⟩
      · have h1 : ContDiffOn ℝ ∞ (fun x : Mat n => Fr x⁻¹) (GLs n) :=
          hCx.smooth.comp GlobalTheory.CompanionTheory.LengthGL.contDiffOn_inv fun y hy => inv_mem_GLs hy
        exact ((ContinuousLinearMap.apply ℂ E.V (S 0 v)).restrictScalars ℝ).contDiff.comp_contDiffOn h1
      · have hκ' : star κ.1 * κ.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 κ.2
        have hinvκ : (g * κ.1)⁻¹ = (κ⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 * g⁻¹ := by
          rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hκ']; rfl
        simp only [hfdef]
        rw [hinvκ, hCx.mul _ (unitary_mem_GLs _) _ (inv_mem_GLs hg), hCx.onK, ContinuousLinearMap.mul_apply]
    have hact : act μ E k f 1 = val (infOf lam) • f 1 := heig (infOf lam) f hfCE (hCx.eig v) 1 one_mem_GLs
    have hI2 : ∫ y, hh y ∂μ = act μ E k f 1 := by
      unfold act
      congr 1; funext y
      have hyG := GlobalTheory.CompanionTheory.LengthGL.mem_GLs_val y
      simp only [hhdef, hfdef, one_mul, hS0v]
      rw [hCx.mul _ (inv_mem_GLs hyG) _ hdG, ContinuousLinearMap.mul_apply]
    have hf1 : f 1 = v := by simp only [hfdef, inv_one, hCx.one, ContinuousLinearMap.one_apply, hS0v]
    rw [hI1, hI2, hact, hf1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  rw [hIF, trL_apply, hCx.S0Γ, ContinuousLinearMap.coe_mul, LinearMap.trace_mul_comm, ← ContinuousLinearMap.coe_mul,
    hkey, ContinuousLinearMap.coe_smul, map_smul, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.coe_mul, LinearMap.trace_mul_comm, ← ContinuousLinearMap.coe_mul, ← mul_assoc, hd]
  exact hCx.char z hz hz2

end PositivityTheory.RgBcC.LfSt.GLSubgroupConjTransposeClosure
