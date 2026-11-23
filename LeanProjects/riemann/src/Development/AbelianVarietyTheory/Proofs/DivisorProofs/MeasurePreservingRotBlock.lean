import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAbsProdLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGaussAbsSupportFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousProd

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights MeasureTheory GlobalTheory.ChowHt

namespace GlobalTheory.FormHtLower

def rotAlong {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} {t : ℂ} (hu : ‖u‖ = 1) (ht : ‖t‖ = 1) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := (((t • rotCL u t⁻¹ : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)
      norm_map' := fun x => by
        change ‖t • rotCL u t⁻¹ x‖ = ‖x‖
        rw [norm_smul, ht, one_mul, norm_rotCL hu (by rw [norm_inv, ht, inv_one])] } rfl

theorem rotAlong_apply {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} {t : ℂ} (hu : ‖u‖ = 1) (ht : ‖t‖ = 1)
    (x : EuclideanSpace ℂ (Fin n)) : rotAlong hu ht x = x + ((t - 1) * inner ℂ u x) • u := by
  have h0 : t ≠ 0 := fun h => by simp [h] at ht
  change t • rotCL u t⁻¹ x = _
  rw [rotCL_apply, smul_add, smul_smul, smul_smul, mul_inv_cancel₀ h0, one_smul, sub_mul, one_mul, sub_smul]
  abel

def rotBlock {B n : ℕ} (b : Fin B) {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ) (z : BlockSphere B n) :
    BlockSphere B n :=
  fun i => (if i = b then sphereMap (rotAlong hu (norm_circPt θ)) else id) (z i)

theorem measurePreserving_rotBlock {B n : ℕ} (b : Fin B) {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ) :
    MeasurePreserving (rotBlock b hu θ) (blockSphereProb B n) (blockSphereProb B n) :=
  measurePreserving_pi _ _ fun i => by
    split_ifs
    exacts [measurePreserving_sphereMap _, MeasurePreserving.id _]

theorem coe_rotBlock {B n : ℕ} (b : Fin B) {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ) (z : BlockSphere B n)
    (i : Fin B) : (rotBlock b hu θ z i : EuclideanSpace ℂ (Fin n)) =
      z i + (if i = b then (circPt θ - 1) * inner ℂ u (z b : EuclideanSpace ℂ (Fin n)) else 0) • u := by
  unfold rotBlock
  split_ifs with h
  · subst h; exact rotAlong_apply hu (norm_circPt θ) _
  · simp

theorem continuous_rotBlock {B n : ℕ} (b : Fin B) {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) :
    Continuous fun p : ℝ × BlockSphere B n => rotBlock b hu p.1 p.2 := by
  refine continuous_pi fun i => continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_rotBlock]
  have hc : ∀ j, Continuous fun p : ℝ × BlockSphere B n => (p.2 j : EuclideanSpace ℂ (Fin n)) := fun j =>
    continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd)
  have hθ : Continuous fun p : ℝ × BlockSphere B n => circPt p.1 := by
    unfold circPt; fun_prop
  split_ifs
  exacts [(hc i).add (((hθ.sub continuous_const).mul (continuous_const.inner (hc b))).smul continuous_const),
    (hc i).add continuous_const]

theorem mean_lead_le {B N : ℕ} (b : Fin B) {u : EuclideanSpace ℂ (Fin N)} (hu : ‖u‖ = 1) {a a' : Fin B → ℕ}
    {F L : MvPolynomial (Fin B × Fin N) ℂ} (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) (hL0 : L ≠ 0)
    (hL : IsMultiHomogeneous a' L) (m : ℕ) {r : ℝ} (hr : 0 < r)
    (h : ∀ z : Fin B × Fin N → ℂ, ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ p.coeff m = eval z L ∧
      ∀ t, p.eval t = eval (fun q => z q + t * (if q.1 = b then (r : ℂ) * u q.2 else 0)) F) :
    blockSphereMean B N L - m * (Real.log r + (harmonic (N - 1) : ℝ) / 2) ≤ blockSphereMean B N F := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hn : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hu0 (Subsingleton.elim _ _))
  have : IsProbabilityMeasure (sphereProb N) := isProbabilityMeasure_sphereProb hn
  have : IsProbabilityMeasure (blockSphereProb B N) := by
    unfold blockSphereProb; infer_instance
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ
  set G : BlockSphere B N → ℝ := fun z => Real.log ‖eval (blockPoint z) F‖ with hG
  have hGi : Integrable G (blockSphereProb B N) := Closed.sphereLogIntegrable B N a F hF0 hF
  have hskew : MeasurePreserving (fun q : ℝ × BlockSphere B N => (q.1, rotBlock b hu q.1 q.2))
      (μ.prod (blockSphereProb B N)) (μ.prod (blockSphereProb B N)) :=
    (MeasurePreserving.id _).skew_product (continuous_rotBlock b hu).measurable
      (Filter.Eventually.of_forall fun θ => (measurePreserving_rotBlock b hu θ).map_eq)
  have hH : Integrable (Function.uncurry fun θ z => G (rotBlock b hu θ z)) (μ.prod (blockSphereProb B N)) := by
    have h1 : Integrable (G ∘ Prod.snd) (μ.prod (blockSphereProb B N)) :=
      (measurePreserving_snd.integrable_comp hGi.aestronglyMeasurable).mpr hGi
    exact (hskew.integrable_comp h1.aestronglyMeasurable).mpr h1
  have hinner : ∀ θ, ∫ z, G (rotBlock b hu θ z) ∂(blockSphereProb B N) = blockSphereMean B N F := by
    intro θ
    have hmp := measurePreserving_rotBlock (B := B) b hu θ
    rw [← integral_map hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hGi.aestronglyMeasurable), hmp.map_eq]
    rfl
  have hmean : blockSphereMean B N F = ∫ z, (∫ θ, G (rotBlock b hu θ z) ∂μ) ∂(blockSphereProb B N) := by
    rw [← integral_integral_swap hH]
    simp [hinner]

  set w : UnitSphereC N → ℂ := fun z => inner ℂ u (z : EuclideanSpace ℂ (Fin N)) with hw
  set c : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (fun i => star (WithLp.ofLp u i)) with hc
  have hcw : ∀ z : UnitSphereC N, ∑ i, WithLp.ofLp c i * spherePoint z i = w z := by
    intro z
    simp [hc, hw, spherePoint, PiLp.inner_apply, RCLike.inner_apply, RCLike.star_def, mul_comm]
  have hcn : ‖c‖ = 1 := by
    rw [← hu]; simp [hc, EuclideanSpace.norm_eq]
  have hc0 : c ≠ 0 := fun h => by simp [h] at hcn
  obtain ⟨hwint, hwval⟩ := Closed.sphereLinLog N c hc0
  simp only [hcw, hcn, Real.log_one, zero_sub] at hwint hwval
  have hev : MeasurePreserving (fun z : BlockSphere B N => z b) (blockSphereProb B N) (sphereProb N) :=
    measurePreserving_eval (fun _ : Fin B => sphereProb N) b
  have hwint' : Integrable (fun z : BlockSphere B N => Real.log ‖w (z b)‖) (blockSphereProb B N) :=
    (hev.integrable_comp hwint.aestronglyMeasurable).mpr hwint
  have hwval' : ∫ z, Real.log ‖w (z b)‖ ∂(blockSphereProb B N) = -((harmonic (N - 1) : ℝ) / 2) := by
    rw [← hwval, ← hev.map_eq, integral_map hev.measurable.aemeasurable
      (by rw [hev.map_eq]; exact hwint.aestronglyMeasurable)]
  have hae : ∀ᵐ z ∂(blockSphereProb B N), w (z b) ≠ 0 :=
    hev.quasiMeasurePreserving.ae (measure_eq_zero_iff_ae_notMem.mp (sphereProb_inner_eq_zero hu0))
  have hLi := Closed.sphereLogIntegrable B N a' L hL0 hL
  have hsub : Integrable (fun z : BlockSphere B N => m * (Real.log ‖w (z b)‖ - Real.log r)) (blockSphereProb B N) :=
    (hwint'.sub (integrable_const _)).const_mul _
  have hlow : ∫ z, (Real.log ‖eval (blockPoint z) L‖ + m * (Real.log ‖w (z b)‖ - Real.log r)) ∂(blockSphereProb B N) =
      blockSphereMean B N L - m * (Real.log r + (harmonic (N - 1) : ℝ) / 2) := by
    rw [integral_add hLi hsub, integral_const_mul,
      integral_sub hwint' (integrable_const _), hwval']
    simp only [integral_const, probReal_univ, one_smul, blockSphereMean]
    ring
  rw [hmean, ← hlow]
  refine integral_mono_ae (hLi.add hsub) hH.integral_prod_right ?_
  filter_upwards [hae, ae_blockSphere_eval_ne_zero B N a' L hL0 hL] with z hz hzL
  obtain ⟨p, hp, hpm, hpe⟩ := h (blockPoint z)
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  set κ : ℂ := w (z b) / r with hκ
  have hκ0 : κ ≠ 0 := div_ne_zero hz hr0
  have hdeg : p.natDegree = m := le_antisymm hp (Polynomial.le_natDegree_of_ne_zero (hpm ▸ hzL))
  have hq : ∀ θ, G (rotBlock b hu θ z) =
      Real.log ‖(p.comp (Polynomial.C κ * Polynomial.X + Polynomial.C (-κ))).eval (circPt θ)‖ := fun θ => by
    rw [Polynomial.eval_comp, hpe]
    simp only [hG]
    refine congrArg (fun x => Real.log ‖eval x F‖) (funext fun q => ?_)
    simp only [blockPoint, spherePoint, coe_rotBlock, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · simp only [hκ, hw]; field_simp; ring
    · simp
  simp only [hq]
  rw [hμ, integral_log_circ]
  refine le_trans (le_of_eq ?_) (log_norm_leadingCoeff_le _)
  rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_linear hκ0]; exact one_ne_zero),
    Polynomial.leadingCoeff_linear hκ0, Polynomial.leadingCoeff, hdeg, hpm, norm_mul, norm_pow,
    Real.log_mul (norm_ne_zero_iff.2 hzL) (pow_ne_zero _ (norm_ne_zero_iff.2 hκ0)), Real.log_pow, hκ, norm_div,
    Real.log_div (norm_ne_zero_iff.2 hz) (norm_ne_zero_iff.2 hr0), Complex.norm_real, Real.norm_of_nonneg hr.le]

section Alg

variable {R : Type} [CommRing R] {ι : Type}

def shift (d : ι → R) (f : MvPolynomial ι R) : MvPolynomial (Option ι) R :=
  aeval (fun p => X (some p) + C (d p) * X none) f

def along (d : ι → R) (f : MvPolynomial ι R) : Polynomial (MvPolynomial ι R) := optionEquivLeft R ι (shift d f)

theorem along_C (d : ι → R) (c : R) : along d (C c) = Polynomial.C (C c) := by simp [along, shift]

theorem along_add (d : ι → R) (f g : MvPolynomial ι R) : along d (f + g) = along d f + along d g := by
  simp [along, shift]

theorem along_mul (d : ι → R) (f g : MvPolynomial ι R) : along d (f * g) = along d f * along d g := by
  simp [along, shift]

theorem along_X (d : ι → R) (p : ι) :
    along d (X p) = Polynomial.C (X p) + Polynomial.C (C (d p)) * Polynomial.X := by simp [along, shift]

theorem along_sum (d : ι → R) {κ : Type} (s : Finset κ) (f : κ → MvPolynomial ι R) :
    along d (∑ k ∈ s, f k) = ∑ k ∈ s, along d (f k) := by simp [along, shift]

theorem eval_along {S : Type} [CommRing S] (φ : R →+* S) (d : ι → R) (z : ι → S) (t : S) (f : MvPolynomial ι R) :
    ((along d f).map (eval₂Hom φ z)).eval t = eval₂Hom φ (fun p => z p + t * φ (d p)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [along_C]
  | add p q hp hq => rw [along_add, Polynomial.map_add, Polynomial.eval_add, hp, hq, map_add]
  | mul_X p i hp =>
    rw [along_mul, Polynomial.map_mul, Polynomial.eval_mul, hp, map_mul, along_X]
    congr 1
    simp [mul_comm t]

theorem along_ne_zero (d : ι → R) {f : MvPolynomial ι R} (hf : f ≠ 0) : along d f ≠ 0 := fun h => hf (by
  have := eval_along (C : R →+* MvPolynomial ι R) d X 0 f
  rw [h] at this
  simpa using this.symm)

variable {B N n : ℕ}

def inBlock (b : Fin B) (u : Fin N → R) : Fin B × Fin N → R := fun q => if q.1 = b then u q.2 else 0

theorem linSubst_coeff_along (w : Matrix (Fin N) (Fin n) R) (b : Fin B) (k : Fin n)
    (f : MvPolynomial (Fin B × Fin N) R) (j : ℕ) :
    linSubst w ((along (inBlock b (w.col k)) f).coeff j) =
      (along (inBlock b (Pi.single k 1)) (linSubst w f)).coeff j := by
  let ψ : MvPolynomial (Fin B × Fin N) R →+* MvPolynomial (Fin B × Fin n) R :=
    (aeval (fun p : Fin B × Fin N => ∑ k, C (w p.2 k) * X (p.1, k)) :
      MvPolynomial (Fin B × Fin N) R →ₐ[R] MvPolynomial (Fin B × Fin n) R).toRingHom
  have hψ : ∀ g, ψ g = linSubst w g := fun _ => rfl
  have key : (along (inBlock b (w.col k)) f).map ψ = along (inBlock b (Pi.single k 1)) (ψ f) := by
    induction f using MvPolynomial.induction_on with
    | C a => simp [along_C, ψ]
    | add p q hp hq => rw [along_add, Polynomial.map_add, hp, hq, map_add, along_add]
    | mul_X p i hp =>
      rw [along_mul, Polynomial.map_mul, hp, map_mul, along_mul, along_X]
      congr 1
      have e1 : ψ (X i) = ∑ k, C (w i.2 k) * X (i.1, k) := by simp [ψ]
      have e2 : ∀ c, ψ (C c) = C c := fun c => by simp [ψ]
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X, e1, e2,
        along_sum]
      simp only [along_mul, along_C, along_X, mul_add, Finset.sum_add_distrib, map_sum, map_mul, ← mul_assoc,
        ← Finset.sum_mul]
      congr 2
      by_cases h : i.1 = b <;> simp [inBlock, h, Pi.single_apply, apply_ite]
  rw [← hψ, ← hψ, ← key, Polynomial.coeff_map]

end Alg

theorem homog_coeff_along {K : Type} [Field K] {B N : ℕ} (b : Fin B) (u : Fin N → K) {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) K} (hf : IsMultiHomogeneous a f) (j : ℕ)
    (h0 : (along (inBlock b u) f).coeff j ≠ 0) :
    ∃ a' : Fin B → ℕ, IsMultiHomogeneous a' ((along (inBlock b u) f).coeff j) ∧ ∑ i, a' i + j = ∑ i, a i := by
  let wt : Option (Fin B × Fin N) → Fin B → ℕ := fun o => o.elim (Pi.single b 1) GlobalTheory.Chow.blockWeight
  have hs : IsWeightedHomogeneous wt (shift (inBlock b u) f) a := by
    rw [isMultiHomogeneous_iff_block] at hf
    rw [f.as_sum, shift, map_sum]
    refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
    rw [aeval_monomial, algebraMap_eq]
    refine IsWeightedHomogeneous.C_mul ?_ _
    rw [← hf (mem_support_iff.1 hs), Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
    refine IsWeightedHomogeneous.prod _ _ _ fun p _ => IsWeightedHomogeneous.pow ?_ _
    refine (isWeightedHomogeneous_X K wt (some p)).add ?_
    by_cases h : p.1 = b
    · have : wt (some p) = wt none := by simp [wt, GlobalTheory.Chow.blockWeight, h]
      rw [this]
      exact (isWeightedHomogeneous_X K wt none).C_mul _
    · simp only [inBlock, if_neg h, map_zero, zero_mul]
      exact isWeightedHomogeneous_zero _ _ _
  have key : ∀ s ∈ ((along (inBlock b u) f).coeff j).support, ∀ i,
      ∑ l, s (i, l) + (Pi.single b j : Fin B → ℕ) i = a i := fun s hs' i => by
    have h1 := congrFun (hs (mem_support_iff.1 ((mem_support_coeff_optionEquivLeft K).1 hs'))) i
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_option, ← GlobalTheory.Chow.weight_blockWeight,
      Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at *
    rw [← h1]
    simp [wt, Pi.single_apply, add_comm]
  obtain ⟨s₀, hs₀⟩ := support_nonempty.2 h0
  refine ⟨fun i => a i - (Pi.single b j : Fin B → ℕ) i, fun s hs' i => ?_, ?_⟩
  · have := key s hs' i
    beta_reduce
    omega
  · have : j = ∑ i, (Pi.single b j : Fin B → ℕ) i := by simp
    conv_lhs => rw [this, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := key s₀ hs₀ i
    simp only [Finset.sum_pi_single', Finset.mem_univ, if_true]
    omega

theorem gaussAbs_coeff_along_le {K ι : Type} [Field K] [NumberField K] (v : FinitePlace K) {d : ι → K}
    (hd : ∀ p, v (d p) ≤ 1) (f : MvPolynomial ι K) (j : ℕ) : gaussAbs v ((along d f).coeff j) ≤ gaussAbs v f := by
  classical
  refine gauss_abs_le_of_coeff_le v _ (GlobalTheory.GaussSubst.gaussAbs_nonneg v f) fun s => ?_
  rw [along, optionEquivLeft_coeff_coeff]
  refine (coeff_le_gauss_abs v _ _).trans (GlobalTheory.GaussSubst.gaussAbs_aeval_le K v _ _ _ _ fun p => ?_)
  refine gauss_abs_le_of_coeff_le v _ zero_le_one fun m => ?_
  rw [coeff_add, coeff_C_mul]
  refine (FinitePlace.add_le v _ _).trans (max_le ?_ ?_)
  · rw [coeff_X']; split_ifs <;> simp
  · rw [coeff_X']; split_ifs <;> simp [hd p]

theorem eq_C_of_natDegree_along {K : Type} [Field K] [Infinite K] {B N n : ℕ} {w : Matrix (Fin N) (Fin n) K}
    (hw : Submodule.span K (Set.range w.col) = ⊤) {f : MvPolynomial (Fin B × Fin N) K}
    (h : ∀ b k, (along (inBlock b (w.col k)) f).natDegree = 0) : f = C (eval 0 f) := by
  let T : Submodule K (Fin B × Fin N → K) :=
    { carrier := {d | ∀ (t : K) z, eval (z + t • d) f = eval z f}
      add_mem' := fun {x y} hx hy t z => by rw [smul_add, ← add_assoc, hy, hx]
      zero_mem' := fun t z => by simp
      smul_mem' := fun c x hx t z => by rw [smul_smul, hx] }
  have h1 : ∀ b k, inBlock b (w.col k) ∈ T := fun b k t z => by
    have e := fun t => eval_along (RingHom.id K) (inBlock b (w.col k)) z t f
    rw [Polynomial.eq_C_of_natDegree_eq_zero (h b k)] at e
    have e1 := e t
    have e2 := e 0
    simp only [Polynomial.map_C, Polynomial.eval_C, zero_mul, add_zero] at e1 e2
    exact e1.symm.trans e2
  have h2 : ∀ b (u : Fin N → K), inBlock b u ∈ T := fun b u => by
    have hu : u ∈ Submodule.span K (Set.range w.col) := hw ▸ trivial
    induction hu using Submodule.span_induction with
    | mem _ h => obtain ⟨k, rfl⟩ := h; exact h1 b k
    | zero => convert T.zero_mem; funext q; simp [inBlock]
    | add x y _ _ hx hy => convert T.add_mem hx hy; funext q; by_cases h : q.1 = b <;> simp [inBlock, h]
    | smul c x _ hx => convert T.smul_mem c hx; funext q; by_cases h : q.1 = b <;> simp [inBlock, h]
  refine MvPolynomial.funext fun z => ?_
  have h3 : z ∈ T := by
    have : z = ∑ b, inBlock b fun j => z (b, j) := by
      funext q; simp [inBlock, Finset.sum_apply]
    rw [this]
    exact T.sum_mem fun b _ => h2 b _
  simpa using h3 1 0

theorem eval_linSubst_map {K : Type} [Field K] {B N : ℕ} (σ : K →+* ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (g : MvPolynomial (Fin B × Fin N) K) (z : Fin B × Fin N → ℂ) :
    eval z (linSubst A (MvPolynomial.map σ g)) = eval₂Hom σ (fun q => A.mulVec (fun i => z (q.1, i)) q.2) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [linSubst]
  | add p q hp hq => simp only [linSubst, map_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p i hp =>
    simp only [linSubst, map_mul] at hp ⊢
    rw [hp]
    simp [Matrix.mulVec, dotProduct]

theorem mean_leadingCoeff_le {K : Type} [Field K] {B N : ℕ} (σ : K →+* ℂ) {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0)
    (b : Fin B) {x : Fin N → K} (hx : x ≠ 0) {Λ : ℝ} (hΛ : frameNorm A (fun j => σ (x j)) ≤ Λ) {a a' : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) K} (hf0 : f ≠ 0) (hf : IsMultiHomogeneous a f)
    (hL : IsMultiHomogeneous a' (along (inBlock b x) f).leadingCoeff) :
    blockSphereMean B N (linSubst A (MvPolynomial.map σ (along (inBlock b x) f).leadingCoeff)) -
      (along (inBlock b x) f).natDegree * (Real.log Λ + (harmonic (N - 1) : ℝ) / 2) ≤
      blockSphereMean B N (linSubst A (MvPolynomial.map σ f)) := by
  have hne : ∀ {h : MvPolynomial (Fin B × Fin N) K}, h ≠ 0 → linSubst A (MvPolynomial.map σ h) ≠ 0 := fun {h} hh =>
    GlobalTheory.HeightUnique.linSubst_ne_zero (A.mul_nonsing_inv hA.isUnit) fun h0 =>
      hh (MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero]))
  set y : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (A⁻¹.mulVec fun j => σ (x j)) with hy
  have hAy : A.mulVec y.ofLp = fun j => σ (x j) := by
    rw [hy, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, A.mul_nonsing_inv hA.isUnit, Matrix.one_mulVec]
  have hy0 : y ≠ 0 := fun h => hx (funext fun j => by
    rw [h] at hAy
    simpa using (congrFun hAy j).symm)
  have hn : ‖y‖ = frameNorm A fun j => σ (x j) := by rw [frameNorm, EuclideanSpace.norm_eq]
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hr' : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have key := mean_lead_le b (u := ((‖y‖ : ℝ) : ℂ)⁻¹ • y)
    (by rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hr.ne'])
    (hne hf0) (GlobalTheory.HeightUnique.linSubst_homog _ (isMultiHomogeneous_map_ring a f hf σ))
    (hne (Polynomial.leadingCoeff_ne_zero.2 (along_ne_zero (inBlock b x) hf0)))
    (GlobalTheory.HeightUnique.linSubst_homog _ (isMultiHomogeneous_map_ring a' _ hL σ)) (along (inBlock b x) f).natDegree hr fun z => by
      refine ⟨(along (inBlock b x) f).map (eval₂Hom σ fun q => A.mulVec (fun i => z (q.1, i)) q.2),
        Polynomial.natDegree_map_le, by rw [Polynomial.coeff_map, eval_linSubst_map]; rfl, fun t => ?_⟩
      rw [eval_along, eval_linSubst_map]
      refine congrArg (fun x => eval₂Hom σ x f) (funext fun q => ?_)
      by_cases h : q.1 = b
      · have e : (fun i => z (q.1, i) + t * (if (q.1, i).1 = b then ((‖y‖ : ℝ) : ℂ) *
            (((‖y‖ : ℝ) : ℂ)⁻¹ • y).ofLp (q.1, i).2 else 0)) = (fun i => z (q.1, i)) + t • y.ofLp := by
          funext i
          simp [h, mul_inv_cancel_left₀ hr']
        rw [e, Matrix.mulVec_add, Matrix.mulVec_smul, hAy]
        simp [inBlock, h]
      · simp [inBlock, h]
  have h2 : Real.log ‖y‖ ≤ Real.log Λ := Real.log_le_log hr (hn ▸ hΛ)
  have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) (along (inBlock b x) f).natDegree)
  linarith

theorem formHeight_zero_ge {K : Type} [Field K] [NumberField K] {B N n : ℕ} (hN : 0 < N) {w : Matrix (Fin N) (Fin n) K}
    (hw : Submodule.span K (Set.range w.col) = ⊤) {A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0)
    {Λ : ℝ} (hΛ : ∀ k σ, frameNorm (A σ) (fun j => σ (w j k)) ≤ Λ) (e : ℕ) :
    ∀ (a : Fin B → ℕ) (f : MvPolynomial (Fin B × Fin N) K), f ≠ 0 → IsMultiHomogeneous a f → ∑ i, a i = e →
      -(e * (Real.log Λ + (harmonic (N - 1) : ℝ) / 2)) ≤ formHeight 0 w A f := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro a f hf0 hf he
  have h1 : IsMultiHomogeneous (0 : Fin B → ℕ) (1 : MvPolynomial (Fin B × Fin N) K) :=
    isMultiHomogeneous_iff_block.2 (isWeightedHomogeneous_one _ _)
  by_cases h : ∀ b k, (along (inBlock b (w.col k)) f).natDegree = 0
  · have hC := eq_C_of_natDegree_along hw h
    have hc : eval 0 f ≠ 0 := fun h0 => hf0 (by rw [hC, h0, map_zero])
    have ha : ∀ i, a i = 0 := fun i => by
      rw [← hf 0 (by rw [hC, mem_support_iff, coeff_zero_C]; exact hc) i]; simp
    have := GlobalTheory.HeightUnique.formHeight_C_mul hN 0 hw hA one_ne_zero h1 hc
    rw [mul_one, ← hC, GlobalTheory.ZeroCycleHt.formHeight_one] at this
    rw [this, ← he]
    simp [ha]
  push Not at h
  obtain ⟨b, k, hm⟩ := h
  have hP := along_ne_zero (inBlock b (w.col k)) hf0
  have hL0 := Polynomial.leadingCoeff_ne_zero.2 hP
  obtain ⟨a', ha', hs⟩ := homog_coeff_along b (w.col k) hf _ hL0
  have hx : w.col k ≠ 0 := fun h0 => hm (by
    have : along (inBlock b (w.col k)) f = Polynomial.C f := by
      rw [h0]
      clear hm hP hL0 ha' hs hf hf0
      induction f using MvPolynomial.induction_on with
      | C a => exact along_C _ _
      | add p q hp hq => rw [along_add, hp, hq, map_add]
      | mul_X p i hp => rw [along_mul, hp, along_X]; simp [inBlock]
    rw [this, Polynomial.natDegree_C])
  have hih := ih (∑ i, a' i) (by omega) a' _ hL0 ha' rfl
  have harch := fun σ => mean_leadingCoeff_le σ (hA σ) b hx (hΛ k σ) hf0 hf ha'
  obtain ⟨P, hP'⟩ := GlobalTheory.HeightUnique.exists_right_inv hw
  have hfin := (GlobalTheory.HSFinPart.finPart_props K _ _).2.1 _ _ (GlobalTheory.HeightUnique.linSubst_ne_zero hP' hf0)
    (GlobalTheory.HeightUnique.linSubst_ne_zero hP' hL0) fun v => by
      rw [Polynomial.leadingCoeff, linSubst_coeff_along]
      refine gaussAbs_coeff_along_le v (fun p => ?_) _ _
      simp only [inBlock, Pi.single_apply]
      split_ifs <;> simp
  have hd : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
  have hsum := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => harch σ
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul] at hsum
  rw [GlobalTheory.HSChoice.finPart, GlobalTheory.HSChoice.finPart, div_le_div_iff_of_pos_right hd] at hfin
  simp only [formHeight, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero, le_div_iff₀ hd] at hih ⊢
  rw [← he, ← hs, Nat.cast_add]
  simp only [Polynomial.leadingCoeff] at hfin hsum hih
  linarith

theorem formHeight_ge {K : Type} [Field K] [NumberField K] {B N n δ : ℕ} (hN : 0 < N) {w : Matrix (Fin N) (Fin n) K}
    (hw : Submodule.span K (Set.range w.col) = ⊤) {A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0)
    {Λ : ℝ} (hΛ : ∀ k σ, frameNorm (A σ) (fun j => σ (w j k)) ≤ Λ) {f : MvPolynomial (Fin B × Fin N) K} (hf0 : f ≠ 0)
    (hf : IsMultiHomogeneous (fun _ => δ) f) : -(B * δ * Real.log Λ) ≤ formHeight δ w A f := by
  have h := formHeight_zero_ge hN hw hA hΛ (B * δ) _ f hf0 hf (by simp)
  have hd : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
  simp only [formHeight, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero, le_div_iff₀ hd, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul, Nat.cast_mul] at h ⊢
  linarith

end GlobalTheory.FormHtLower
