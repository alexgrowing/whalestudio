import Development.WeilBound.ThetaLifts.LatticeBasics.SliceSeminorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsEqAdelicCharMul
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumStarAndSchAStar

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Automorphic.GJMatrix GroundTheory.Global

attribute [local instance 100000] measurableSpace_adeleRing

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
  {Φ : (κ ⊕ κ → AF F) → ℂ}

theorem sl_int (h : Φ ∈ schA F (κ ⊕ κ)) (a) : Integrable (sl a Φ) (adeleMeasurePi F) :=
  integrable_of_mem_schwartzBruhatPi ((sl_mem h).1 a)

variable (F κ) in

def lD : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ := (LinearMap.exists_extend
  ({ toFun Φ := adelicFourierPi F (sl 0 Φ.1) 0
     map_add' Φ Ψ := congrFun (adelicFourierPi_add (sl_int Φ.2 0) (sl_int Ψ.2 0)) 0
     map_smul' c Φ := congrFun (adelicFourierPi_smul c (sl 0 Φ.1)) 0 } : schA F (κ ⊕ κ) →ₗ[ℂ] ℂ)).choose

theorem lD_apply (h : Φ ∈ schA F (κ ⊕ κ)) : lD F κ Φ = adelicFourierPi F (sl 0 Φ) 0 :=
  LinearMap.congr_fun (LinearMap.exists_extend _).choose_spec (⟨Φ, h⟩ : schA F (κ ⊕ κ))

theorem lD_int (h : Φ ∈ schA F (κ ⊕ κ)) : lD F κ Φ = ∫ u, Φ (Sum.elim u u) ∂adeleMeasurePi F := by
  rw [lD_apply h]; simp [adelicFourierPi, sl]

theorem lD_adm : lD F κ ∈ (adeleClass F).adm (κ ⊕ κ) := fun g hg => by
  refine ⟨finiteFourierPi F (fun u => g (Sum.elim (u + finPartPi (K := F) 0) u)) (finPartPi 0) •
    ((BoundedContinuousFunction.evalCLM ℂ (infPartPi 0)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).comp
      ((mixedFourierPiSchwartz F).comp (slice (infPartPi (K := F) 0))), fun f => ?_⟩
  rw [lD_apply (Submodule.subset_span ⟨f, g, hg, rfl⟩), show pureA F f g = schwartzBruhatTensorPi f g from rfl,
    sl_tensor, adelicFourierPi_schwartzBruhatTensorPi]
  exact mul_comm _ _

theorem std_eq (h : IsStd ψ) : ∃ ξ : F, ξ ≠ 0 ∧ ∀ x, ψ x = (adelicChar F (algebraMap F (AF F) ξ * x) : ℂ) := by
  obtain ⟨ξ, e⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ h.1 h.2.1
  obtain ⟨x, hx⟩ := GlobalTheory.StdCharFromIsStd.exists_ne_one h
  exact ⟨ξ, fun h0 => hx (by simp [e, h0]), e⟩

theorem elim_dot (a a' b b' : κ → AF F) : Sum.elim a a' ⬝ᵥ Sum.elim b b' = a ⬝ᵥ b + a' ⬝ᵥ b' := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem lD_schr (h : IsStd ψ) {ξ : F} (e : ∀ x, ψ x = (adelicChar F (algebraMap F (AF F) ξ * x) : ℂ))
    (hΦ : Φ ∈ schA F (κ ⊕ κ)) (a a' b b' : κ → AF F) :
    lD F κ (schr ψ (Sum.elim a a', Sum.elim b b') Φ) = ψ (⅟(2 : AF F) * (a ⬝ᵥ b + a' ⬝ᵥ b') - a' ⬝ᵥ (b + b')) *
      adelicFourierPi F (sl (a - a') Φ) (algebraMap F (AF F) ξ • (b + b')) := by
  rw [lD_int (GlobalTheory.HeisSchA.schr_mem_schA ψ h _ Φ hΦ), adelicFourierPi, ← integral_const_mul, eq_comm,
    ← integral_add_right_eq_self _ a', eq_comm]
  refine integral_congr_ae (.of_forall fun u => ?_)
  have : ∑ i, (u + a') i * (algebraMap F (AF F) ξ • (b + b')) i = algebraMap F (AF F) ξ * ((u + a') ⬝ᵥ (b + b')) := by
    rw [← smul_eq_mul, ← dotProduct_smul]; rfl
  simp only [schr, sl]
  rw [this, ← e, mul_left_comm, ← AddChar.map_add_eq_mul, mul_comm]
  congr 2
  · funext i; cases i <;> simp
  · simp only [elim_dot, add_dotProduct, dotProduct_add]; ring

theorem lD_kill (h : IsStd ψ) (hΦ : Φ ∈ schA F (κ ⊕ κ)) (a b : κ → AF F) :
    lD F κ (schr ψ (Sum.elim a a, Sum.elim b (-b)) Φ) = lD F κ Φ := by
  obtain ⟨ξ, -, e⟩ := std_eq h
  rw [lD_schr h e hΦ, lD_apply hΦ]; simp

theorem lD_inj (h : IsStd ψ) (hΦ : Φ ∈ schA F (κ ⊕ κ))
    (h0 : ∀ a b, lD F κ (schr ψ (Sum.elim a 0, Sum.elim b 0) Φ) = 0) : Φ = 0 := by
  obtain ⟨ξ, hξ, e⟩ := std_eq h
  have k : ∀ a, adelicFourierPi F (sl a Φ) = 0 := fun a => funext fun b => by
    have := h0 a (algebraMap F (AF F) ξ⁻¹ • b)
    rw [lD_schr h e hΦ, sub_zero, add_zero, smul_smul, ← map_mul, mul_inv_cancel₀ hξ, map_one, one_smul] at this
    exact (mul_eq_zero.1 this).resolve_left (by rw [e]; exact Circle.coe_ne_zero _)
  funext z
  have := congrFun (adelicFourierPi_adelicFourierPi ((sl_mem hΦ).1 (z ∘ .inl - z ∘ .inr))) (-(z ∘ .inr))
  rw [k, adelicFourierPi_zero] at this
  simpa [sl] using this.symm

theorem lD_theta (h : IsStd ψ) (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    HasSum (fun p : (κ → F) × (κ → F) => lD F κ (schr ψ (Sum.elim (rt p.1) (-rt p.1), Sum.elim (rt p.2) (rt p.2)) Φ))
      (thetaSum F Φ) := by
  obtain ⟨ξ, hξ, e⟩ := std_eq h
  have h2 : ξ * 2 ≠ 0 := mul_ne_zero hξ two_ne_zero
  convert ((Equiv.smulRight (β := κ → F) (two_ne_zero (α := F))).prodCongr (Equiv.smulRight (β := κ → F) h2)).hasSum_iff.2
    (hasSum_sl hΦ) using 2 with p
  have : ⅟(2 : AF F) * (rt p.1 ⬝ᵥ rt p.2 + -rt p.1 ⬝ᵥ rt p.2) - -rt p.1 ⬝ᵥ (rt p.2 + rt p.2) =
      algebraMap F (AF F) (p.1 ⬝ᵥ (p.2 + p.2)) := by
    simp [dotProduct]
  rw [lD_schr h e hΦ, this, h.2.1, one_mul]
  congr 2 <;> funext i <;> simp [rt, map_ofNat] <;> ring

theorem star_mem {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) : star φ ∈ schA F κ :=
  (GlobalTheory.CompanionTheory.ThetaReal.thetaSum_star_and_schA_star F κ φ).2 h

theorem box_mem {φ φ' : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) (h' : φ' ∈ schA F κ) : boxFun φ (star φ') ∈ schA F (κ ⊕ κ) :=
  GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ h _ (star_mem h')

theorem theta_box {φ φ' : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) (h' : φ' ∈ schA F κ) :
    thetaSum F (boxFun φ (star φ')) = thetaSum F φ * star (thetaSum F φ') := by
  rw [show star (thetaSum F φ') = _ from (GlobalTheory.CompanionTheory.ThetaReal.thetaSum_star_and_schA_star F κ φ').1.symm, thetaSum, thetaSum,
    thetaSum, tsum_mul_tsum_of_summable_norm (summable_norm_of_mem_schA F h) (summable_norm_of_mem_schA F (star_mem h')),
    ← (Equiv.sumArrowEquivProdArrow κ κ F).tsum_eq]
  rfl

theorem borel_eq : (MeasurableSpace.pi : MeasurableSpace (κ → AF F)) = borel _ := BorelSpace.measurable_eq

theorem lD_haar (ν : @Measure (κ → AF F) (borel _)) (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, lD F κ (boxFun φ (star φ')) = c * ∫ u, φ u * star (φ' u) ∂ν := by
  revert ν
  rw [← borel_eq]
  intro ν hν
  refine ⟨Measure.addHaarScalarFactor (adeleMeasurePi F) ν, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,
    fun φ h φ' h' => ?_⟩
  rw [lD_int (box_mem h h')]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (adeleMeasurePi F) ν, integral_smul_nnreal_measure]
  rfl

theorem lD_sq {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) :
    lD F κ (boxFun φ (star φ)) = (∫⁻ x, ‖φ x‖ₑ ^ 2 ∂adeleMeasurePi F).toReal := by
  rw [lD_int (box_mem h h)]
  have : ∀ u, boxFun φ (star φ) (Sum.elim u u) = ((‖φ u‖ ^ 2 : ℝ) : ℂ) := fun u => by
    simp [boxFun, Complex.mul_conj']
  simp only [this]
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ => sq_nonneg _)
    ((continuous_of_mem_schwartzBruhatPi h).norm.pow 2).aestronglyMeasurable]
  simp [ENNReal.ofReal_pow, ofReal_norm_eq_enorm]

theorem lD_unit {G : Type} [Group G] {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} (hu : IsUnitaryOn (adeleClass F) om)
    (hp : ∀ g, ∀ φ ∈ schA F κ, om g φ ∈ schA F κ) (g : G) {φ φ' : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) (h' : φ' ∈ schA F κ) :
    lD F κ (boxFun (om g φ) (star (om g φ'))) = lD F κ (boxFun φ (star φ')) := by
  have k : ∀ φ ∈ schA F κ, lD F κ (boxFun (om g φ) (star (om g φ))) = lD F κ (boxFun φ (star φ)) := fun φ h => by
    unfold IsUnitaryOn at hu
    rw [← borel_eq] at hu
    rw [lD_sq h, lD_sq (hp g φ h), hu _ inferInstance g φ h]
  have k1 := k _ (add_mem h h')
  have k2 := k _ (add_mem h (Submodule.smul_mem _ Complex.I h'))
  simp only [map_add, map_smul, star_add, star_smul, GlobalTheory.SchwartzBox.boxFun_add_left, GlobalTheory.SchwartzBox.boxFun_add_right,
    GlobalTheory.SchwartzBox.boxFun_smul_left, GlobalTheory.SchwartzBox.boxFun_smul_right, k φ h, k φ' h', smul_eq_mul,
    Complex.star_def, Complex.conj_I] at k1 k2
  linear_combination (1 / 2) * k1 + (Complex.I / 2) * k2 + (1 / 2 * (lD F κ (boxFun (om g φ) (star (om g φ'))) -
    lD F κ (boxFun φ (star φ')) - lD F κ (boxFun (om g φ') (star (om g φ))) + lD F κ (boxFun φ' (star φ)))) * Complex.I_mul_I

end GlobalTheory.ThK.Dbl

end
