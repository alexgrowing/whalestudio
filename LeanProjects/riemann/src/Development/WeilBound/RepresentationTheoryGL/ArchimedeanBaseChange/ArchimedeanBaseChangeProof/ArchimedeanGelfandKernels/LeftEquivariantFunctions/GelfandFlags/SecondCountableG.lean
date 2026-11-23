import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth

noncomputable section

open MeasureTheory Matrix Finset Topology
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.VC.NAvgH

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def sq (A : Mat n) : ℝ := ∑ a, ∑ b, ‖A a b‖ ^ 2

theorem sq_nonneg' (A : Mat n) : 0 ≤ sq A := by
  unfold sq; positivity

theorem sq_mul_le (A B : Mat n) : sq (A * B) ≤ sq A * sq B := by
  unfold sq
  have h1 : ∀ a b, ‖(A * B) a b‖ ^ 2 ≤ (∑ c, ‖A a c‖ ^ 2) * ∑ c, ‖B c b‖ ^ 2 := by
    intro a b
    rw [Matrix.mul_apply]
    calc ‖∑ c, A a c * B c b‖ ^ 2 ≤ (∑ c, ‖A a c‖ * ‖B c b‖) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans ?_
          simp only [norm_mul, le_refl]
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ a, ∑ b, ‖(A * B) a b‖ ^ 2 ≤ ∑ a, ∑ b, (∑ c, ‖A a c‖ ^ 2) * ∑ c, ‖B c b‖ ^ 2 := by
        gcongr with a _ b _
        exact h1 a b
    _ = (∑ a, ∑ c, ‖A a c‖ ^ 2) * ∑ c, ∑ b, ‖B c b‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.mul_sum, Finset.sum_comm]

theorem lg_eq (y : Mat n) : lg y = Real.log (1 + sq y + sq y⁻¹) := by
  simp only [lg, sq, Finset.sum_add_distrib, add_assoc]

theorem lg_mul_le (A B : Mat n) : lg (A * B) ≤ lg A + lg B := by
  rw [lg_eq, lg_eq, lg_eq, Matrix.mul_inv_rev]
  have hA := sq_nonneg' A; have hA' := sq_nonneg' A⁻¹; have hB := sq_nonneg' B; have hB' := sq_nonneg' B⁻¹
  have hxA : 0 < 1 + sq A + sq A⁻¹ := by linarith
  have hxB : 0 < 1 + sq B + sq B⁻¹ := by linarith
  have hxAB : 0 < 1 + sq (A * B) + sq (B⁻¹ * A⁻¹) := by
    have := sq_nonneg' (A * B); have := sq_nonneg' (B⁻¹ * A⁻¹); linarith
  rw [← Real.log_mul hxA.ne' hxB.ne']
  apply Real.log_le_log hxAB
  have e1 := sq_mul_le A B
  have e2 := sq_mul_le B⁻¹ A⁻¹
  nlinarith [mul_nonneg hA hB, mul_nonneg hA' hB', mul_nonneg hA hB', mul_nonneg hA' hB]

theorem lg_inv (A : Mat n) (hA : A ∈ GLs n) : lg A⁻¹ = lg A := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  rw [lg_eq, lg_eq, Matrix.nonsing_inv_nonsing_inv A hA', add_right_comm]

theorem isOpen_GLs : IsOpen (GLs n) := by
  show IsOpen {g : Mat n | det g ≠ 0}
  exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem continuousAt_lg (x : Mat n) (hx : x ∈ GLs n) : ContinuousAt lg x := by
  have hinv : ContinuousAt (fun y : Mat n => y⁻¹) x := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hx
  have hsq : Continuous (sq : Mat n → ℝ) := by
    unfold sq
    refine continuous_finset_sum _ (fun a _ => continuous_finset_sum _ (fun b _ => ?_))
    exact (((continuous_apply b).comp (continuous_apply a)).norm).pow 2
  have hpos : 0 < 1 + sq x + sq x⁻¹ := by linarith [sq_nonneg' x, sq_nonneg' x⁻¹]
  rw [show (lg : Mat n → ℝ) = fun y => Real.log (1 + sq y + sq y⁻¹) from funext lg_eq]
  exact ((continuousAt_const.add hsq.continuousAt).add (hsq.continuousAt.comp hinv)).log hpos.ne'

theorem mem_GLsG (y : G n) : y.val ∈ GLs n := by
  show det y.val ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

theorem mem_GLs_mul {A B : Mat n} (hA : A ∈ GLs n) (hB : B ∈ GLs n) : A * B ∈ GLs n := by
  show (A * B).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hA hB

def lmulL : Mat n →L[ℝ] Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => LinearMap.toContinuousLinearMap
        { toFun := fun x => M * x
          map_add' := fun x y => Matrix.mul_add M x y
          map_smul' := fun c x => Matrix.mul_smul M c x }
      map_add' := fun M M' => by ext x : 1; simp [Matrix.add_mul]
      map_smul' := fun c M => by ext x : 1; simp [Matrix.smul_mul] }

theorem secondCountable_G : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end PositivityTheory.RgBcC.VC.NAvgH

namespace PositivityTheory.RgBcC.VC

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC.NAvgH
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nAvg_of (hIS : IntSmooth) (hLg : LgCpt) (hNU : NilUni) : NAvg := by
  intro n _ _ E W₁ W₂ hW N hN ν _ φ hφ hφR
  obtain ⟨R, hR⟩ := hφR
  obtain ⟨hNc, hinv⟩ := hNU n W₁ W₂ hW N hN
  haveI := hinv ν
  haveI : SecondCountableTopology (G n) := secondCountable_G
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨hφs, hφk⟩ := hφ
  have hφc : ContinuousOn φ (GLs n) := hφs.continuousOn
  have hmem : ∀ u : N, ∀ x ∈ GLs n, ((u : G n) : Mat n) * x ∈ GLs n :=
    fun u x hx => mem_GLs_mul (mem_GLsG _) hx
  have hlgu : ∀ u x : Mat n, x ∈ GLs n → lg u ≤ lg (u * x) + lg x := by
    intro u x hx
    have h := lg_mul_le (u * x) x⁻¹
    rwa [Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.mpr hx), lg_inv x hx] at h
  have cpt : ∀ c : ℝ, IsCompact {u : N | lg ((u : G n) : Mat n) ≤ c} := fun c =>
    hNc.isClosedEmbedding_subtypeVal.isCompact_preimage (hLg n c)
  have hsupp : ∀ x₀ ∈ GLs n, ∃ U ∈ 𝓝 x₀, ∃ K : Set N, IsCompact K ∧
      ∀ u ∉ K, ∀ x ∈ U, φ (((u : G n) : Mat n) * x) = 0 := by
    intro x₀ hx₀
    refine ⟨GLs n ∩ lg ⁻¹' Set.Iio (lg x₀ + 1),
      Filter.inter_mem (isOpen_GLs.mem_nhds hx₀)
        ((continuousAt_lg x₀ hx₀).preimage_mem_nhds (Iio_mem_nhds (by linarith))),
      _, cpt (R + lg x₀ + 1), ?_⟩
    intro u hu x hx
    have hu' : ¬ lg ((u : G n) : Mat n) ≤ R + lg x₀ + 1 := hu
    have h1 := hlgu ((u : G n) : Mat n) x hx.1
    have h2 : lg x < lg x₀ + 1 := hx.2
    exact hR _ (hmem u x hx.1) (by linarith [lt_of_not_ge hu'])
  have hint : ∀ x ∈ GLs n, Integrable (fun u : N => φ (((u : G n) : Mat n) * x)) ν := by
    intro x hx
    obtain ⟨U, hU, K, hK, hKz⟩ := hsupp x hx
    have hc : Continuous (fun u : N => φ (((u : G n) : Mat n) * x)) :=
      hφc.comp_continuous (by fun_prop) (fun u => hmem u x hx)
    exact hc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK (fun u hu => hKz u hu x (mem_of_mem_nhds hU)))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hmaps : ∀ U : Mat n, U ∈ GLs n → Set.MapsTo (lmulL U) (GLs n) (GLs n) :=
      fun U hU x hx => mem_GLs_mul hU hx
    have hle : ∀ m : ℕ, ((m : ℕ∞ω) ≤ ∞) := fun m => by exact_mod_cast le_top
    have hD : ∀ m : ℕ, ContinuousOn (iteratedFDeriv ℝ m φ) (GLs n) := fun m =>
      (hφs.continuousOn_iteratedFDerivWithin (hle m) isOpen_GLs.uniqueDiffOn).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen m isOpen_GLs hx).symm)
    have hform : ∀ (m : ℕ) (U : Mat n), U ∈ GLs n → ∀ x ∈ GLs n,
        iteratedFDeriv ℝ m (φ ∘ ⇑(lmulL U)) x =
          (iteratedFDeriv ℝ m φ (lmulL U x)).compContinuousLinearMap (fun _ => lmulL U) := by
      intro m U hU x hx
      have hopen : IsOpen (⇑(lmulL U) ⁻¹' GLs n) := isOpen_GLs.preimage (lmulL U).continuous
      have hgx : lmulL U x ∈ GLs n := hmaps U hU hx
      have hx' : x ∈ ⇑(lmulL U) ⁻¹' GLs n := hgx
      have h1 := (lmulL U).iteratedFDerivWithin_comp_right hφs isOpen_GLs.uniqueDiffOn
        hopen.uniqueDiffOn hgx (hle m)
      have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := φ ∘ ⇑(lmulL U)) m hopen hx'
      have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := φ) m isOpen_GLs hgx
      rw [← e1, ← e2]
      exact h1
    have hUc : Continuous (fun p : N × Mat n => ((p.1 : G n) : Mat n)) := by fun_prop
    have hUx : Continuous (fun p : N × Mat n => ((p.1 : G n) : Mat n) * p.2) := by fun_prop
    have key := hIS n N ν E.V (fun u => φ ∘ ⇑(lmulL ((u : G n) : Mat n)))
      (fun u => hφs.comp (lmulL ((u : G n) : Mat n)).contDiff.contDiffOn (hmaps _ (mem_GLsG _)))
      (fun m => by
        let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
          (fun _ : Fin m => Mat n) (fun _ : Fin m => Mat n) E.V
        have hC : Continuous (fun p : N × Mat n => C (fun _ => lmulL ((p.1 : G n) : Mat n))) :=
          C.cont.comp (continuous_pi fun _ => lmulL.continuous.comp hUc)
        have hDp : ContinuousOn
            (fun p : N × Mat n => iteratedFDeriv ℝ m φ (lmulL ((p.1 : G n) : Mat n) p.2))
            (Set.univ ×ˢ GLs n) :=
          (hD m).comp hUx.continuousOn (fun p hp => hmem p.1 p.2 hp.2)
        refine (hC.continuousOn.clm_apply hDp).congr (fun p hp => ?_)
        exact (hform m _ (mem_GLsG _) p.2 hp.2).trans rfl)
      hsupp
    exact key
  · intro g hg k
    have e : ∀ u : N, φ (((u : G n) : Mat n) * (g * ↑k)) = E.ρ k⁻¹ (φ (((u : G n) : Mat n) * g)) := by
      intro u
      rw [← Matrix.mul_assoc]
      exact hφk _ (hmem u g hg) k
    show ∫ u : N, φ (((u : G n) : Mat n) * (g * ↑k)) ∂ν = E.ρ k⁻¹ (∫ u : N, φ (((u : G n) : Mat n) * g) ∂ν)
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact ContinuousLinearMap.integral_comp_comm _ (hint g hg)
  · intro u₀ hu₀ x hx
    have hu₁ : u₀ ∈ N := by
      rw [← SetLike.mem_coe, hN]
      exact hu₀
    set u₁ : N := ⟨u₀, hu₁⟩ with hu₁def
    have key : ∀ f : N → E.V, ∫ u, f (u * u₁) ∂ν = ∫ u, f u ∂ν := by
      intro f
      rw [← integral_inv_eq_self (fun u => f (u * u₁)) ν]
      have hre : ∀ u : N, f (u⁻¹ * u₁) = (fun v => f v⁻¹) (u₁⁻¹ * u) := fun u => by
        simp [_root_.mul_inv_rev]
      simp_rw [hre]
      rw [integral_mul_left_eq_self (fun v => f v⁻¹) u₁⁻¹, integral_inv_eq_self f ν]
    show ∫ u : N, φ (((u : G n) : Mat n) * ((u₀ : Mat n) * x)) ∂ν = ∫ u : N, φ (((u : G n) : Mat n) * x) ∂ν
    rw [← key (fun u => φ (((u : G n) : Mat n) * x))]
    congr 1
    ext u
    simp [hu₁def, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]

end PositivityTheory.RgBcC.VC
