import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SetIntegralPowEqZeroOfPosFreqEuclidean
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemThetaDomainIffIsSiegelAddTranspose
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMulDotProductLeOfIsCompactThetaDomain
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.DifferentiableOnThetaProdOfNormal

noncomputable section

open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real

namespace GlobalTheory.CanTh

section Operators

variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem hasSum_polyDeriv_of_locally_normal {ι : Type*} {F : ι → W → ℂ} {U : Set W} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ v : ι → ℝ, Summable v ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ v i)
    (P : MvPolynomial σ ℂ) (u : σ → W) {x : W} (hx : x ∈ U) :
    HasSum (fun i => I2.polyDeriv P u (F i) x) (I2.polyDeriv P u (fun w => ∑' i, F i w) x) := by
  unfold I2.polyDeriv
  refine hasSum_sum fun m _ => HasSum.mul_left _ ?_
  exact (SCV.hasSum_iteratedFDeriv_of_locally_normal hU hF hle _ hx).mapL
    (ContinuousMultilinearMap.apply ℂ (fun _ => W) ℂ _)

omit [FiniteDimensional ℂ W] in

theorem polyDeriv_congr_of_eventuallyEq (P : MvPolynomial σ ℂ) (u : σ → W) {F G : W → ℂ} {x : W}
    (h : F =ᶠ[𝓝 x] G) : I2.polyDeriv P u F x = I2.polyDeriv P u G x := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [(h.iteratedFDeriv ℂ _).eq_of_nhds]

theorem polyDeriv_const_mul (P : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} {U : Set W}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (c : ℂ) {x : W} (hx : x ∈ U) :
    I2.polyDeriv P u (fun w => c * F w) x = c * I2.polyDeriv P u F x := by
  unfold I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : (fun w => c * F w) = c • F := rfl
  rw [e, iteratedFDeriv_const_smul_apply
    (SCV.contDiffAt_of_differentiableOn hF (hU.mem_nhds hx) _)]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]

theorem iteratedFDeriv_snd {F : B × W → ℂ} {U : Set (B × W)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {s : B} {x : W} (hx : (s, x) ∈ U) (k : ℕ) (v : Fin k → W) :
    iteratedFDeriv ℂ k (fun w => F (s, w)) x v =
      iteratedFDeriv ℂ k F (s, x) (fun j => (0, v j)) := by
  set L : W →L[ℂ] B × W := ContinuousLinearMap.inr ℂ B W with hL
  set c : B × W := (s, 0) with hc
  set t : Set (B × W) := (fun w => c + w) ⁻¹' U with ht
  have hto : IsOpen t := hU.preimage (by fun_prop)
  have hto' : IsOpen (L ⁻¹' t) := hto.preimage L.continuous
  have hg : DifferentiableOn ℂ (fun w => F (c + w)) t :=
    hF.comp (by fun_prop) fun w hw => hw
  have h0 : L x ∈ t := by simpa [ht, hc, hL] using hx
  have key := L.iteratedFDerivWithin_comp_right (SCV.contDiffOn_nat hto k hg) hto.uniqueDiffOn
    hto'.uniqueDiffOn h0 le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hto' (show x ∈ L ⁻¹' t from h0),
    iteratedFDerivWithin_of_isOpen k hto h0, iteratedFDeriv_comp_add_left] at key
  have e : (fun w => F (s, w)) = (fun w => F (c + w)) ∘ L := by
    ext w
    simp [hL, hc]
  rw [e, key]
  simp [hL, hc]

theorem differentiableOn_polyDeriv_snd {F : B × W → ℂ} {U : Set (B × W)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (P : MvPolynomial σ ℂ) (u : σ → W) :
    DifferentiableOn ℂ (fun p : B × W => I2.polyDeriv P u (fun w => F (p.1, w)) p.2) U := by
  unfold I2.polyDeriv
  refine DifferentiableOn.fun_sum fun m _ => DifferentiableOn.const_mul ?_ _
  refine DifferentiableOn.congr ?_ fun p hp => iteratedFDeriv_snd hU hF (s := p.1) (x := p.2) hp _ _
  exact (ContinuousMultilinearMap.apply ℂ (fun _ => B × W) ℂ _).differentiable.comp_differentiableOn
    (SCV.differentiableOn_iteratedFDeriv hU hF _)

theorem differentiableOn_polyDeriv_param {F : B × W → ℂ} {V : Set B} (hV : IsOpen V)
    (hF : DifferentiableOn ℂ F (V ×ˢ Set.univ)) (P : MvPolynomial σ ℂ) (u : σ → W) (x : W) :
    DifferentiableOn ℂ (fun s : B => I2.polyDeriv P u (fun w => F (s, w)) x) V :=
  (differentiableOn_polyDeriv_snd (hV.prod isOpen_univ) hF P u).comp (f := fun s => (s, x))
    (by fun_prop) fun _ hs => ⟨hs, trivial⟩

end Operators

variable {g : ℕ}

def thTerm (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (ζ : Fin g → ℂ) (m : Fin g → ℤ) : ℂ :=
  cexp (π * I * (((fun i => (m i : ℂ)) + fun i => (a i : ℂ)) ⬝ᵥ
      τ *ᵥ ((fun i => (m i : ℂ)) + fun i => (a i : ℂ))) +
    2 * π * I * (((fun i => (m i : ℂ)) + fun i => (a i : ℂ)) ⬝ᵥ (ζ + fun i => (b i : ℂ))))

theorem thetaChar_eq_tsum (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (ζ : Fin g → ℂ) :
    thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) ζ = ∑' m, thTerm τ a b ζ m := rfl

theorem thTerm_eq_thetaTerm (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (ζ : Fin g → ℂ)
    (m : Fin g → ℤ) : thTerm τ a b ζ m = thetaTerm a b ζ τ m := by
  unfold thTerm thetaTerm eC
  congr 1
  have e1 : ((fun i => (m i : ℂ)) + fun i => (a i : ℂ)) = shiftVec a m := rfl
  have e2 : (fun i => (b i : ℂ)) = ofRealVec b := rfl
  rw [e1, e2]
  ring

theorem thetaChar_eq_theta (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (ζ : Fin g → ℂ) :
    thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) ζ = theta a b ζ τ := by
  rw [thetaChar_eq_tsum]
  exact tsum_congr fun m => thTerm_eq_thetaTerm τ a b ζ m

theorem thTerm_add_matrix (τ S : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (ζ : Fin g → ℂ)
    (m : Fin g → ℤ) :
    thTerm (τ + S) a b ζ m = cexp (π * I * (((fun i => (m i : ℂ)) + fun i => (a i : ℂ)) ⬝ᵥ
      S *ᵥ ((fun i => (m i : ℂ)) + fun i => (a i : ℂ)))) * thTerm τ a b ζ m := by
  unfold thTerm
  rw [← Complex.exp_add, add_mulVec, dotProduct_add]
  congr 1
  ring

theorem thTerm_add_var (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (ζ w : Fin g → ℂ)
    (m : Fin g → ℤ) :
    thTerm τ a b (ζ + w) m =
      cexp (2 * π * I * (((fun i => (m i : ℂ)) + fun i => (a i : ℂ)) ⬝ᵥ w)) * thTerm τ a b ζ m := by
  unfold thTerm
  rw [← Complex.exp_add]
  congr 1
  simp only [dotProduct_add]
  ring

theorem mem_thetaDomain {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef) :
    τ ∈ ThetaDomain (Fin g) := hp.add hp.transpose

theorem summable_norm_thTerm {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ ThetaDomain (Fin g))
    (a b : Fin g → ℝ) (ζ : Fin g → ℂ) : Summable fun m => ‖thTerm τ a b ζ m‖ := by
  simp only [thTerm_eq_thetaTerm]
  exact thetaSummable_holds (Fin g) a b ζ τ hτ

theorem hasSum_thTerm {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ ThetaDomain (Fin g))
    (a b : Fin g → ℝ) (ζ : Fin g → ℂ) :
    HasSum (thTerm τ a b ζ) (thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) ζ) :=
  (summable_norm_thTerm hτ a b ζ).of_norm.hasSum

theorem hasSum_prod_thTerm {κ : Type*} [Fintype κ] {τ : κ → Matrix (Fin g) (Fin g) ℂ}
    (hτ : ∀ k, τ k ∈ ThetaDomain (Fin g)) (a b : κ → Fin g → ℝ) (ζ : κ → Fin g → ℂ) :
    HasSum (fun m : κ → Fin g → ℤ => ∏ k, thTerm (τ k) (a k) (b k) (ζ k) (m k))
      (∏ k, thetaChar (τ k) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ)) (ζ k)) := by
  simpa using hasSum_multilinear_tuples (J := fun _ : κ => Fin g → ℤ)
    (ContinuousMultilinearMap.mkPiAlgebra ℂ κ ℂ) (x := fun k => thTerm (τ k) (a k) (b k) (ζ k))
    (fun k => summable_norm_thTerm (hτ k) _ _ _) fun k => hasSum_thTerm (hτ k) _ _ _

section Continuous

variable {W : Type*} [TopologicalSpace W] [LocallyCompactSpace W]

theorem thTerm_locally_normal {U : Set W} (hU : IsOpen U) {T : W → Matrix (Fin g) (Fin g) ℂ}
    {Z : W → Fin g → ℂ} (hT : ∀ i j, ContinuousOn (fun w => T w i j) U) (hZ : ContinuousOn Z U)
    (hdom : ∀ w ∈ U, T w ∈ ThetaDomain (Fin g)) (a b : Fin g → ℝ) {x : W} (hx : x ∈ U) :
    ∃ t ∈ 𝓝 x, ∃ v : (Fin g → ℤ) → ℝ, Summable v ∧
      ∀ m, ∀ w ∈ t, ‖thTerm (T w) a b (Z w) m‖ ≤ v m := by
  obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx)
  have hc : ContinuousOn (fun w => ((Z w, fun i j => T w i j) :
      (Fin g → ℂ) × (Fin g → Fin g → ℂ))) K :=
    (hZ.prodMk (continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hT i j)).mono hKU
  obtain ⟨v, hv, h⟩ := thetaMTest_holds (Fin g) a _ (hK.image_of_continuousOn hc) (by
    rintro _ ⟨w, hw, rfl⟩
    exact hdom w (hKU hw))
  refine ⟨K, hKx, v, hv, fun m w hw => ?_⟩
  rw [thTerm_eq_thetaTerm]
  exact h b _ ⟨w, hw, rfl⟩ m

theorem mul_prod_thTerm_locally_normal {κ : Type*} [Fintype κ] {U : Set W} (hU : IsOpen U)
    {G : W → ℂ} {T : κ → W → Matrix (Fin g) (Fin g) ℂ} {Z : κ → W → Fin g → ℂ}
    (hG : ContinuousOn G U) (hT : ∀ k i j, ContinuousOn (fun w => T k w i j) U)
    (hZ : ∀ k, ContinuousOn (Z k) U) (hdom : ∀ k, ∀ w ∈ U, T k w ∈ ThetaDomain (Fin g))
    (a b : κ → Fin g → ℝ) {x : W} (hx : x ∈ U) :
    ∃ t ∈ 𝓝 x, ∃ v : (κ → Fin g → ℤ) → ℝ, Summable v ∧
      ∀ m, ∀ w ∈ t, ‖G w * ∏ k, thTerm (T k w) (a k) (b k) (Z k w) (m k)‖ ≤ v m := by
  choose t ht v hv h using fun k =>
    thTerm_locally_normal hU (hT k) (hZ k) (hdom k) (a k) (b k) hx
  have h0 : ∀ k m, 0 ≤ v k m := fun k m =>
    (norm_nonneg _).trans (h k m x (mem_of_mem_nhds (ht k)))
  have hG' : ∀ᶠ w in 𝓝 x, ‖G w‖ < ‖G x‖ + 1 :=
    (hG.continuousAt (hU.mem_nhds hx)).norm.eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨{w | ‖G w‖ < ‖G x‖ + 1} ∩ ⋂ k, t k, inter_mem hG' (iInter_mem.2 ht),
    fun m => (‖G x‖ + 1) * ∏ k, v k (m k),
    (summable_prod_tuples (J := fun _ : κ => Fin g → ℤ) h0 hv).mul_left _, fun m w hw => ?_⟩
  rw [norm_mul, norm_prod]
  exact mul_le_mul (le_of_lt hw.1) (Finset.prod_le_prod (fun k _ => norm_nonneg _)
    fun k _ => h k _ w (Set.mem_iInter.1 hw.2 k))
    (Finset.prod_nonneg fun k _ => norm_nonneg _) (by positivity)

end Continuous

section Holomorphic

variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem differentiableOn_prod_fun {κ : Type*} (s : Finset κ) {F : κ → W → ℂ} {U : Set W}
    (hF : ∀ k ∈ s, DifferentiableOn ℂ (F k) U) :
    DifferentiableOn ℂ (fun w => ∏ k ∈ s, F k w) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert k s hk ih =>
    simp only [Finset.prod_insert hk]
    exact (hF k (Finset.mem_insert_self _ _)).mul
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem differentiableOn_thTerm {U : Set W} {T : W → Matrix (Fin g) (Fin g) ℂ}
    {Z : W → Fin g → ℂ} (hT : ∀ i j, DifferentiableOn ℂ (fun w => T w i j) U)
    (hZ : DifferentiableOn ℂ Z U) (a b : Fin g → ℝ) (m : Fin g → ℤ) :
    DifferentiableOn ℂ (fun w => thTerm (T w) a b (Z w) m) U := by
  simp only [thTerm_eq_thetaTerm]
  exact (differentiable_thetaTerm_prod a b m).comp_differentiableOn
    (f := fun w => (Z w, fun i j => T w i j))
    (hZ.prodMk (differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => hT i j))

theorem differentiableOn_thetaChar {U : Set W} {T : W → Matrix (Fin g) (Fin g) ℂ}
    {Z : W → Fin g → ℂ} (hT : ∀ i j, DifferentiableOn ℂ (fun w => T w i j) U)
    (hZ : DifferentiableOn ℂ Z U) (hdom : ∀ w ∈ U, T w ∈ ThetaDomain (Fin g))
    (a b : Fin g → ℝ) :
    DifferentiableOn ℂ
      (fun w => thetaChar (T w) (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) (Z w)) U := by
  simp only [thetaChar_eq_theta]
  exact (thetaHolo_of_domainOpen_of_mTest siegelSubDomain_and_domainOpen.2 thetaMTest_holds
    (Fin g) a b).comp (f := fun w => (Z w, fun i j => T w i j))
    (hZ.prodMk (differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => hT i j)) hdom

theorem differentiable_thetaChar {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ ThetaDomain (Fin g))
    (a b : Fin g → ℝ) :
    Differentiable ℂ (thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ))) :=
  differentiableOn_univ.1 (differentiableOn_thetaChar (T := fun _ => τ) (Z := id)
    (fun _ _ => differentiableOn_const _) differentiableOn_id (fun _ _ => hτ) a b)

variable [FiniteDimensional ℂ W] {κ : Type*} [Fintype κ]

theorem hasSum_polyDeriv_mul_prod {U : Set W} (hU : IsOpen U)
    {G : W → ℂ} {T : κ → W → Matrix (Fin g) (Fin g) ℂ} {Z : κ → W → Fin g → ℂ}
    (hG : DifferentiableOn ℂ G U) (hT : ∀ k i j, DifferentiableOn ℂ (fun w => T k w i j) U)
    (hZ : ∀ k, DifferentiableOn ℂ (Z k) U) (hdom : ∀ k, ∀ w ∈ U, T k w ∈ ThetaDomain (Fin g))
    (a b : κ → Fin g → ℝ) (P : MvPolynomial σ ℂ) (u : σ → W) {x : W} (hx : x ∈ U) :
    HasSum (fun m : κ → Fin g → ℤ =>
        I2.polyDeriv P u (fun w => G w * ∏ k, thTerm (T k w) (a k) (b k) (Z k w) (m k)) x)
      (I2.polyDeriv P u (fun w => G w *
        ∏ k, thetaChar (T k w) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ)) (Z k w)) x) := by
  have : ProperSpace W := FiniteDimensional.proper ℂ W
  have h := hasSum_polyDeriv_of_locally_normal hU
    (F := fun (m : κ → Fin g → ℤ) w => G w * ∏ k, thTerm (T k w) (a k) (b k) (Z k w) (m k))
    (fun m => hG.mul (differentiableOn_prod_fun _ fun k _ =>
      differentiableOn_thTerm (hT k) (hZ k) _ _ _))
    (fun y hy => mul_prod_thTerm_locally_normal hU hG.continuousOn
      (fun k i j => (hT k i j).continuousOn) (fun k => (hZ k).continuousOn) hdom a b hy) P u hx
  rwa [polyDeriv_congr_of_eventuallyEq P u (G := fun w => G w *
    ∏ k, thetaChar (T k w) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ)) (Z k w))] at h
  filter_upwards [hU.mem_nhds hx] with w hw
  exact ((hasSum_prod_thTerm (fun k => hdom k w hw) a b fun k => Z k w).mul_left _).tsum_eq

theorem hasSum_polyDeriv_mul_prod_const {G : W → ℂ} {τ : κ → Matrix (Fin g) (Fin g) ℂ}
    {Z : κ → W → Fin g → ℂ} (hG : Differentiable ℂ G) (hZ : ∀ k, Differentiable ℂ (Z k))
    (hτ : ∀ k, τ k ∈ ThetaDomain (Fin g)) (a b : κ → Fin g → ℝ) (P : MvPolynomial σ ℂ)
    (u : σ → W) (x : W) :
    HasSum (fun m : κ → Fin g → ℤ =>
        I2.polyDeriv P u (fun w => G w * ∏ k, thTerm (τ k) (a k) (b k) (Z k w) (m k)) x)
      (I2.polyDeriv P u (fun w => G w *
        ∏ k, thetaChar (τ k) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ)) (Z k w)) x) ∧
    Summable fun m : κ → Fin g → ℤ =>
      ‖I2.polyDeriv P u (fun w => G w * ∏ k, thTerm (τ k) (a k) (b k) (Z k w) (m k)) x‖ :=
  have h := hasSum_polyDeriv_mul_prod (T := fun k _ => τ k) isOpen_univ hG.differentiableOn
    (fun _ _ _ => differentiableOn_const _) (fun k => (hZ k).differentiableOn)
    (fun k _ _ => hτ k) a b P u (Set.mem_univ x)
  ⟨h, summable_norm_iff.2 h.summable⟩

theorem hasSum_polyDeriv_mul_prod_add_matrix {G : W → ℂ} {τ S : κ → Matrix (Fin g) (Fin g) ℂ}
    {Z : κ → W → Fin g → ℂ} (hG : Differentiable ℂ G) (hZ : ∀ k, Differentiable ℂ (Z k))
    (hτ : ∀ k, τ k + S k ∈ ThetaDomain (Fin g)) (a b : κ → Fin g → ℝ) (P : MvPolynomial σ ℂ)
    (u : σ → W) (x : W) :
    HasSum (fun m : κ → Fin g → ℤ =>
        I2.polyDeriv P u (fun w => G w * ∏ k, thTerm (τ k) (a k) (b k) (Z k w) (m k)) x *
          cexp (π * I * ∑ k, ((fun i => (m k i : ℂ)) + fun i => (a k i : ℂ)) ⬝ᵥ
            S k *ᵥ ((fun i => (m k i : ℂ)) + fun i => (a k i : ℂ))))
      (I2.polyDeriv P u (fun w => G w *
        ∏ k, thetaChar (τ k + S k) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ)) (Z k w)) x) := by
  convert (hasSum_polyDeriv_mul_prod_const hG hZ hτ a b P u x).1 using 2 with m
  rw [mul_comm, ← polyDeriv_const_mul P u isOpen_univ _ _ (Set.mem_univ x)]
  · congr 1
    funext w
    simp only [thTerm_add_matrix, Finset.prod_mul_distrib, Finset.mul_sum, Complex.exp_sum]
    ring
  · exact hG.differentiableOn.mul (differentiableOn_prod_fun _ fun k _ =>
      differentiableOn_thTerm (T := fun _ => τ k) (fun _ _ => differentiableOn_const _)
        (hZ k).differentiableOn _ _ _)

end Holomorphic

def imInv (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)

def canTh (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (ζ : Fin g → ℂ) : ℂ :=
  cexp (π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ)) * thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) ζ

def canMult (a b : Fin g → ℝ) (m n : Fin g → ℤ) : ℂ :=
  cexp (π * I * ((m ⬝ᵥ n : ℤ) : ℂ) + 2 * π * I *
    (((a ⬝ᵥ fun i => (m i : ℝ) : ℝ) : ℂ) - ((b ⬝ᵥ fun i => (n i : ℝ) : ℝ) : ℂ)))

def translConst (b a' b' : Fin g → ℝ) : ℂ :=
  cexp (-(π * I * ((a' ⬝ᵥ b' : ℝ) : ℂ)) - 2 * π * I * ((a' ⬝ᵥ b : ℝ) : ℂ))

theorem norm_translConst (b a' b' : Fin g → ℝ) : ‖translConst b a' b'‖ = 1 := by
  rw [translConst, Complex.norm_exp]
  simp

variable {τ : Matrix (Fin g) (Fin g) ℂ}

theorem imInv_mul (hp : (τ.map Complex.im).PosDef) :
    imInv τ * (τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) = 1 := by
  change (τ.map Complex.im)⁻¹.map ofRealHom * (τ.map Complex.im).map ofRealHom = 1
  rw [← Matrix.map_mul, nonsing_inv_mul _ hp.det_pos.ne'.isUnit,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem imInv_eq_inv_map (hp : (τ.map Complex.im).PosDef) :
    imInv τ = ((τ.map Complex.im).map fun x : ℝ => (x : ℂ))⁻¹ :=
  (inv_eq_left_inv (imInv_mul hp)).symm

theorem isSymm_imInv (hs : τ.IsSymm) : (imInv τ).IsSymm :=
  (hs.map Complex.im).inv.map _

theorem dot_imInv_eq_hermForm_add (hp : (τ.map Complex.im).PosDef) (u v : Fin g → ℝ)
    (ζ : Fin g → ℂ) :
    ζ ⬝ᵥ imInv τ *ᵥ ((fun i => (v i : ℂ)) + τ *ᵥ fun i => (u i : ℂ)) =
      hermForm (imInv τ) ζ ((fun i => (v i : ℂ)) + τ *ᵥ fun i => (u i : ℂ)) +
        2 * I * (ζ ⬝ᵥ fun i => (u i : ℂ)) := by
  have e : ((fun i => (v i : ℂ)) + τ *ᵥ fun i => (u i : ℂ)) =
      star ((fun i => (v i : ℂ)) + τ *ᵥ fun i => (u i : ℂ)) +
        (2 * I) • ((τ.map Complex.im).map fun x : ℝ => (x : ℂ)) *ᵥ fun i => (u i : ℂ) := by
    funext i
    apply Complex.ext
    · simp [mulVec, dotProduct]
    · simp [mulVec, dotProduct]
      ring
  conv_lhs => rw [e]
  rw [mulVec_add, dotProduct_add, mulVec_smul, mulVec_mulVec, imInv_mul hp, one_mulVec,
    dotProduct_smul, smul_eq_mul, hermForm]

theorem differentiable_canTh (hp : (τ.map Complex.im).PosDef) (a b : Fin g → ℝ) :
    Differentiable ℂ (canTh τ a b) := by
  refine Differentiable.mul ?_ (differentiable_thetaChar (mem_thetaDomain hp) a b)
  simp only [dotProduct, mulVec]
  fun_prop

theorem thetaChar_ne_zero (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (a b : Fin g → ℝ) :
    thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) ≠ 0 := by
  have h := theta_ne_zero (τ := τ) ⟨hs, hp⟩ a b
  simp only [← thetaChar_eq_theta] at h
  exact h

theorem canTh_ne_zero (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (a b : Fin g → ℝ) :
    canTh τ a b ≠ 0 := by
  obtain ⟨z, hz⟩ := Function.ne_iff.1 (thetaChar_ne_zero hs hp a b)
  exact Function.ne_iff.2 ⟨z, mul_ne_zero (Complex.exp_ne_zero _) hz⟩

theorem canTh_translate (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (a b a' b' : Fin g → ℝ)
    {y : Fin g → ℂ} (hy : y = (fun i => (b' i : ℂ)) + τ *ᵥ fun i => (a' i : ℂ)) (ζ : Fin g → ℂ) :
    cexp (-(π * hermForm (imInv τ) ζ y) - π / 2 * hermForm (imInv τ) y y) * canTh τ a b (ζ + y) =
      translConst b a' b' * canTh τ (a + a') (b + b') ζ := by
  have h1 := dot_imInv_eq_hermForm_add hp a' b' ζ
  have h2 := dot_imInv_eq_hermForm_add hp a' b' y
  rw [← hy] at h1 h2
  have h3 := dot_mulVec_symm (isSymm_imInv hs) ζ y
  have h4 := thetaRealTransl_holds (Fin g) a b a' b' ζ τ hs
  have e : ζ + τ *ᵥ ofRealVec a' + ofRealVec b' = ζ + y := by
    rw [hy, add_assoc, add_comm (τ *ᵥ _)]
    rfl
  have h5 : (y ⬝ᵥ fun i => (a' i : ℂ)) =
      ((a' ⬝ᵥ b' : ℝ) : ℂ) + ofRealVec a' ⬝ᵥ τ *ᵥ ofRealVec a' := by
    rw [hy, add_dotProduct, dotProduct_comm (τ *ᵥ _)]
    congr 1
    simp [dotProduct, mul_comm]
  have h6 : ofRealVec a' ⬝ᵥ (ζ + ofRealVec b + ofRealVec b') =
      (ζ ⬝ᵥ fun i => (a' i : ℂ)) + ((a' ⬝ᵥ b : ℝ) : ℂ) + ((a' ⬝ᵥ b' : ℝ) : ℂ) := by
    simp [dotProduct, ofRealVec, mul_add, Finset.sum_add_distrib, mul_comm]
  rw [e, h6] at h4
  rw [canTh, canTh, thetaChar_eq_theta, thetaChar_eq_theta, h4, translConst, eC]
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, h3, h1, h2, h5]
  ring

theorem canTh_add_int (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (n m : Fin g → ℤ)
    (ζ : Fin g → ℂ) :
    canTh τ (a + fun i => (n i : ℝ)) (b + fun i => (m i : ℝ)) ζ =
      cexp (2 * π * I * ((a ⬝ᵥ fun i => (m i : ℝ) : ℝ) : ℂ)) * canTh τ a b ζ := by
  have e : ofRealVec a ⬝ᵥ ofIntVec m = ((a ⬝ᵥ fun i => (m i : ℝ) : ℝ) : ℂ) := by
    simp [dotProduct, ofRealVec, ofIntVec]
  rw [canTh, canTh, thetaChar_eq_theta, thetaChar_eq_theta, thetaIntChar_holds, e, eC]
  ring

theorem canTh_add_period (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (a b : Fin g → ℝ)
    (m n : Fin g → ℤ) {l : Fin g → ℂ} (hl : l = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ))
    (ζ : Fin g → ℂ) :
    canTh τ a b (ζ + l) = canMult a b m n *
      cexp (π * hermForm (imInv τ) ζ l + π / 2 * hermForm (imInv τ) l l) * canTh τ a b ζ := by
  have h := canTh_translate hs hp a b (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) (y := l)
    (by simpa using hl) ζ
  rw [canTh_add_int] at h
  have e : translConst b (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) *
      cexp (2 * π * I * ((a ⬝ᵥ fun i => (m i : ℝ) : ℝ) : ℂ)) = canMult a b m n := by
    rw [translConst, canMult, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-(m ⬝ᵥ n), ?_⟩
    have e1 : (((fun i => (n i : ℝ)) ⬝ᵥ fun i => (m i : ℝ) : ℝ) : ℂ) = ((m ⬝ᵥ n : ℤ) : ℂ) := by
      simp [dotProduct, mul_comm]
    rw [e1, dotProduct_comm _ b, Int.cast_neg]
    ring
  rw [← mul_assoc, e] at h
  rw [mul_right_comm, ← h, mul_right_comm, ← Complex.exp_add]
  simp

theorem im_hermForm_imInv (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    (u v u' v' : Fin g → ℝ) :
    (hermForm (imInv τ) ((fun i => (v i : ℂ)) + τ *ᵥ fun i => (u i : ℂ))
      ((fun i => (v' i : ℂ)) + τ *ᵥ fun i => (u' i : ℂ))).im = u ⬝ᵥ v' - v ⬝ᵥ u' := by
  set y := (fun i => (v i : ℂ)) + τ *ᵥ fun i => (u i : ℂ) with hy
  set y' := (fun i => (v' i : ℂ)) + τ *ᵥ fun i => (u' i : ℂ) with hy'
  have h1 := dot_imInv_eq_hermForm_add hp u' v' y
  have h2 := dot_imInv_eq_hermForm_add hp u v y'
  rw [← hy'] at h1
  rw [← hy] at h2
  have h3 := dot_mulVec_symm (isSymm_imInv hs) y y'
  have h4 : hermForm (imInv τ) y' y = starRingEnd ℂ (hermForm (imInv τ) y y') := by
    rw [hermForm, dot_mulVec_symm (isSymm_imInv hs)]
    simp [hermForm, dotProduct, mulVec, imInv]
  have h5 : (y ⬝ᵥ fun i => (u' i : ℂ)) - (y' ⬝ᵥ fun i => (u i : ℂ)) =
      ((v ⬝ᵥ u' - u ⬝ᵥ v' : ℝ) : ℂ) := by
    rw [hy, hy', add_dotProduct, add_dotProduct, dotProduct_comm (τ *ᵥ _), dotProduct_comm (τ *ᵥ _),
      dot_mulVec_symm hs]
    simp [dotProduct, mul_comm]
  have h6 : hermForm (imInv τ) y y' - starRingEnd ℂ (hermForm (imInv τ) y y') =
      2 * I * ((u ⬝ᵥ v' - v ⬝ᵥ u' : ℝ) : ℂ) := by
    rw [← h4]
    push_cast at h5 ⊢
    linear_combination h2 - h1 - h3 - 2 * I * h5
  have h7 := congrArg Complex.im h6
  simp only [sub_im, conj_im, mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat,
    im_ofNat] at h7
  linarith

end GlobalTheory.CanTh
