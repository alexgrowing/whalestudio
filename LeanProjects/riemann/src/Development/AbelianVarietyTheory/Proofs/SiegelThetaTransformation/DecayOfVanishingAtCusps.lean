import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.StarInvMulVecDotProductMulVecInvMulVec
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NormDetDenomLeRankOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFourierExpansionHolomorphicTubeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsIntegralBasisHermitianMatricesDualStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TracePairingGeDetImPowHermitianHalfSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableExpNegTraceTotallyPositiveHermitianStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Decay

open MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {N : ℕ}

def pr (T : Matrix (Fin N) (Fin N) E) (Z : CM Ψ N N) : ℂ := ∑ τ : Ψ, (T.map τ.1 * Z τ).trace

def cube (m : ℕ) : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ : Fin m => Set.Ico (0 : ℝ) 1)

theorem volume_cube (m : ℕ) : volume (cube m) = 1 := by
  simp [cube, volume_pi_pi]

theorem herm_map {T : Matrix (Fin N) (Fin N) E} (h : ccT T = T) (τ : E →+* ℂ) :
    (T.map τ).IsHermitian := by
  rw [Matrix.IsHermitian, ← Base.ccT_map, h]

theorem trace_im {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace.im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  have := Matrix.trace_conjTranspose (A * B)
  rw [conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm] at this
  exact this.symm

theorem imH_of_herm {X : Matrix (Fin N) (Fin N) ℂ} (h : X.IsHermitian) : imH X = 0 := by
  rw [imH, h.eq, sub_self, smul_zero]

theorem imH_xy {X Y : Matrix (Fin N) (Fin N) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    imH (X + I • Y) = Y := by
  rw [imH_add_I_smul _ _ hY, imH_of_herm hX, zero_add]

theorem re_herm (Z : Matrix (Fin N) (Fin N) ℂ) : (Z - I • imH Z).IsHermitian := by
  have : Z - I • imH Z = (2 : ℂ)⁻¹ • (Z + Zᴴ) := by
    ext a b
    simp only [imH, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    field_simp
    ring
  rw [this, Matrix.IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose,
    add_comm]
  simp

theorem trace_mul_im {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (Z : Matrix (Fin N) (Fin N) ℂ) : (A * Z).trace.im = (A * imH Z).trace.re := by
  have h : A * Z = A * (Z - I • imH Z) + I • (A * imH Z) := by
    rw [← Matrix.mul_smul, ← Matrix.mul_add, sub_add_cancel]
  conv_lhs => rw [h]
  rw [trace_add, trace_smul, add_im, trace_im hA (re_herm Z)]
  simp

theorem pr_im {T : Matrix (Fin N) (Fin N) E} (h : ccT T = T) (Z : CM Ψ N N) :
    (pr T Z).im = ∑ τ : Ψ, (T.map τ.1 * imH (Z τ)).trace.re := by
  rw [pr, im_sum]
  exact Finset.sum_congr rfl fun τ _ => trace_mul_im (herm_map h _) _

theorem norm_e (w : ℂ) : ‖cexp (2 * π * I * w)‖ = Real.exp (-(2 * π * w.im)) := by
  rw [Complex.norm_exp]; simp

theorem norm_e' (w : ℂ) : ‖cexp (-(2 * π * I * w))‖ = Real.exp (2 * π * w.im) := by
  rw [Complex.norm_exp]; simp

theorem posDef_of_ge {Y : Matrix (Fin N) (Fin N) ℂ} {η : ℝ} (hη : 0 < η)
    (h : (Y - (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) : Y.PosDef := by
  have h1 : ((η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hη)
  simpa using h1.add_posSemidef h

def IsCoef {m : ℕ} (X : (Fin m → ℝ) → CM Ψ N N) (f : CM Ψ N N → ℂ) (T : Matrix (Fin N) (Fin N) E)
    (a : ℂ) : Prop :=
  ∀ Y : CM Ψ N N, (∀ τ, (Y τ).PosDef) → a = ∫ x in cube m,
    f (fun τ => X x τ + I • Y τ) * cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y τ)))

section coef
variable {m : ℕ} {X : (Fin m → ℝ) → CM Ψ N N} {f : CM Ψ N N → ℂ} {T : Matrix (Fin N) (Fin N) E}
  {a : ℂ} {η B : ℝ}

theorem norm_integrand_le (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T) (hη : 0 < η)
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) {Y : CM Ψ N N}
    (hY : ∀ τ, (Y τ - (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) (x : Fin m → ℝ) :
    ‖f (fun τ => X x τ + I • Y τ) * cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y τ)))‖ ≤
      B * Real.exp (2 * π * ∑ τ : Ψ, (T.map τ.1 * Y τ).trace.re) := by
  have hi : ∀ τ, imH (X x τ + I • Y τ) = Y τ := fun τ =>
    imH_xy (hX x τ) (posDef_of_ge hη (hY τ)).1
  rw [norm_mul, norm_e', pr_im hT]
  simp only [hi]
  gcongr
  exact hB _ fun τ => by simpa only [hi] using hY τ

theorem coef_bound (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T) (hη : 0 < η)
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) (ha : IsCoef X f T a) {Y : CM Ψ N N}
    (hY : ∀ τ, (Y τ - (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) :
    ‖a‖ ≤ B * Real.exp (2 * π * ∑ τ : Ψ, (T.map τ.1 * Y τ).trace.re) := by
  rw [ha Y fun τ => posDef_of_ge hη (hY τ)]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cube m)
    (by rw [volume_cube]; exact ENNReal.one_lt_top)
    (fun x _ => norm_integrand_le hX hT hη hB hY x)
  simpa [Measure.real, volume_cube] using this

theorem trace_vecMulVec (A : Matrix (Fin N) (Fin N) ℂ) (u : Fin N → ℂ) :
    (A * vecMulVec u (star u)).trace = star u ⬝ᵥ A *ᵥ u := by
  simp only [Matrix.trace, diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem coef_psd (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T) (hη : 0 < η)
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) (ha : IsCoef X f T a) (h0 : a ≠ 0) (τ : Ψ) :
    (T.map τ.1).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨herm_map hT _, fun u => ?_⟩
  rw [Complex.le_def]
  refine ⟨?_, (ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.quad_im (herm_map hT _) u).symm⟩
  by_contra hneg
  simp only [zero_re, not_le] at hneg
  set q := (star u ⬝ᵥ T.map τ.1 *ᵥ u).re with hq
  set c := ∑ σ : Ψ, (T.map σ.1 * ((η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))).trace.re with hc
  have key : ∀ t : ℝ, 0 ≤ t → ‖a‖ ≤ B * Real.exp (2 * π * (c + q * t)) := by
    intro t ht
    have := coef_bound hX hT hη hB ha (Y := fun σ => (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) +
      if σ = τ then (t : ℂ) • vecMulVec u (star u) else 0) (fun σ => by
        rw [add_sub_cancel_left]
        split_ifs
        · exact (posSemidef_vecMulVec_self_star u).smul (by exact_mod_cast ht)
        · exact PosSemidef.zero)
    convert this using 4
    simp only [Matrix.mul_add, trace_add, add_re, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single τ]
    · rw [if_pos rfl, Matrix.mul_smul, trace_smul, trace_vecMulVec, smul_eq_mul, re_ofReal_mul,
        mul_comm]
    · intro σ _ h; simp [h]
    · simp
  have lim : Tendsto (fun t : ℝ => B * Real.exp (2 * π * (c + q * t))) atTop (𝓝 (B * 0)) := by
    refine Tendsto.const_mul _ (Real.tendsto_exp_atBot.comp ?_)
    exact Tendsto.const_mul_atBot (by positivity)
      (tendsto_atBot_add_const_left _ _ (tendsto_id.const_mul_atTop_of_neg hneg))
  have := ge_of_tendsto lim ((eventually_ge_atTop 0).mono key)
  exact h0 (norm_le_zero_iff.1 (by simpa using this))

theorem coef_sing (hXc : Continuous X) (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T)
    (hη : 0 < η)
    (hf : DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N})
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) (ha : IsCoef X f T a) {v : Fin N → E}
    (hv : ∀ Z ∈ Hn Ψ N, Tendsto (fun t : ℝ => f (pushZ Ψ Z v t)) atTop (𝓝 0))
    (hTv : T *ᵥ v = 0) : a = 0 := by
  set P : CM Ψ N N := fun τ => vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a)) with hP
  set Y : ℝ → CM Ψ N N := fun t τ => (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) + (t : ℂ) • P τ
    with hYdef
  have hY : ∀ t, 0 ≤ t → ∀ τ, (Y t τ - (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef := by
    intro t ht τ
    simp only [hYdef, add_sub_cancel_left]
    exact (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht)
  have hTP : ∀ τ : Ψ, (T.map τ.1 * P τ).trace = 0 := by
    intro τ
    rw [hP, trace_vecMulVec]
    have : T.map τ.1 *ᵥ (fun a => τ.1 (v a)) = 0 := by
      ext i
      have := congrArg τ.1 (congrFun hTv i)
      simpa [mulVec, dotProduct] using this
    rw [this, dotProduct_zero]
  have hpush : ∀ x t, (fun τ => X x τ + I • Y t τ) = pushZ Ψ (fun τ => X x τ + I • Y 0 τ) v t := by
    intro x t
    funext τ
    simp only [hYdef, pushZ, hP, smul_add, smul_smul, ofReal_zero, mul_zero, zero_smul, add_zero,
      add_assoc]
    rfl
  have hpr : ∀ x t, pr T (fun τ => X x τ + I • Y t τ) = pr T (fun τ => X x τ + I • Y 0 τ) := by
    intro x t
    simp [pr, hYdef, Matrix.mul_add, hTP]
  have htr : ∀ t, ∑ τ : Ψ, (T.map τ.1 * Y t τ).trace.re = ∑ τ : Ψ, (T.map τ.1 * Y 0 τ).trace.re := by
    intro t
    simp [hYdef, Matrix.mul_add, hTP]
  have hH : ∀ t, 0 ≤ t → ∀ x, (fun τ => X x τ + I • Y t τ) ∈ Hn Ψ N := fun t ht x τ => by
    have := posDef_of_ge hη (hY t ht τ)
    simpa only [imH_xy (hX x τ) this.1] using this
  haveI : IsFiniteMeasure (volume.restrict (cube m)) :=
    isFiniteMeasure_restrict.2 (by rw [volume_cube]; exact ENNReal.one_ne_top)
  have lim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (cube m))
    (l := atTop) (F := fun (t : ℝ) x => f (fun τ => X x τ + I • Y t τ) *
      cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y t τ)))) (f := fun _ => 0)
    (fun _ => B * Real.exp (2 * π * ∑ τ : Ψ, (T.map τ.1 * Y 0 τ).trace.re))
    ((eventually_ge_atTop 0).mono fun t ht => by
      have hc : Continuous fun x => (fun τ => X x τ + I • Y t τ : CM Ψ N N) :=
        hXc.add continuous_const
      refine (Continuous.mul (hf.continuousOn.comp_continuous hc (hH t ht)) ?_).aestronglyMeasurable
      refine Complex.continuous_exp.comp (Continuous.neg (continuous_const.mul ?_))
      exact continuous_finset_sum _ fun τ _ =>
        (continuous_const.matrix_mul ((continuous_apply τ).comp hc)).matrix_trace)
    ((eventually_ge_atTop 0).mono fun t ht => ae_of_all _ fun x => by
      rw [← htr t]; exact norm_integrand_le hX hT hη hB (hY t ht) x)
    (integrable_const _)
    (ae_of_all _ fun x => by
      have := (hv _ (hH 0 le_rfl x)).mul_const
        (cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y 0 τ))))
      rw [zero_mul] at this
      exact this.congr fun t => by rw [hpr x t, hpush x t])
  rw [integral_zero] at lim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) lim
  exact (eventually_ge_atTop 0).mono fun t ht => ha _ fun τ => posDef_of_ge hη (hY t ht τ)

theorem coef_posDef (hXc : Continuous X) (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T)
    (hη : 0 < η)
    (hf : DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N})
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) (ha : IsCoef X f T a)
    (hv : ∀ v : Fin N → E, v ≠ 0 → ∀ Z ∈ Hn Ψ N,
      Tendsto (fun t : ℝ => f (pushZ Ψ Z v t)) atTop (𝓝 0))
    (h0 : a ≠ 0) (τ : Ψ) : (T.map τ.1).PosDef := by
  refine (coef_psd hX hT hη hB ha h0 τ).posDef_iff_det_ne_zero.2 fun h => h0 ?_
  have : T.det = 0 := by
    have e := τ.1.map_det T
    rw [RingHom.mapMatrix_apply, h] at e
    exact (map_eq_zero _).1 e
  obtain ⟨v, hv0, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 this
  exact coef_sing hXc hX hT hη hf hB ha (hv v hv0) hTv

end coef

theorem exists_fourier (hΨ : IsType Ψ) (N R : ℕ) (hR : 0 < R) :
    ∃ (m c : ℕ) (T : (Fin m → ℤ) → Matrix (Fin N) (Fin N) E) (X : (Fin m → ℝ) → CM Ψ N N),
      0 < c ∧ Function.Injective T ∧ (∀ ν, ccT (T ν) = T ν ∧ Den c (T ν)) ∧ Continuous X ∧
      (∀ x τ, (X x τ).IsHermitian) ∧ ∀ f : CM Ψ N N → ℂ,
        DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} →
        (∀ y : Matrix (Fin N) (Fin N) E, IntM y → ccT y = y → ∀ Z ∈ Hn Ψ N,
          f (fun τ => Z τ + ((R : E) • y).map τ.1) = f Z) →
        ∃ a : (Fin m → ℤ) → ℂ, (∀ ν, IsCoef X f (T ν) (a ν)) ∧
          ∀ Z ∈ Hn Ψ N, HasSum (fun ν => a ν * cexp (2 * π * I * pr (T ν) Z)) (f Z) := by
  obtain ⟨m, β, T, c, hc, h1, hd, hZ⟩ := GlobalTheory.T.exists_integral_basis_hermitian_matrices_dual E Ψ hΨ N R hR
  choose hβ hT hD y hy hyc hβy using h1
  set Φ : (Fin m → ℂ) → CM Ψ N N := fun z τ => ∑ j, z j • (β j).map τ.1 with hΦ
  set co : CM Ψ N N → Fin m → ℂ := fun Z j => pr (T j) Z with hco
  have hΦco : ∀ Z, Φ (co Z) = Z := fun Z => (hZ Z).symm
  have hcoΦ : ∀ z, co (Φ z) = z := by
    intro z
    funext i
    simp only [hco, hΦ, pr, Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ τ : Ψ, z j * ((T i).map τ.1 * (β j).map τ.1).trace =
        z j * if i = j then 1 else 0 := by
      intro j
      rw [← hd i j, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Matrix.map_mul, AddMonoidHom.map_trace]
    simp only [this]
    simp
  set TT : (Fin m → ℤ) → Matrix (Fin N) (Fin N) E := fun ν => ∑ i, (ν i : E) • T i with hTT
  have hpr : ∀ ν Z, pr (TT ν) Z = ∑ i, (ν i : ℂ) * co Z i := by
    intro ν Z
    have : ∀ τ : Ψ, (TT ν).map τ.1 = ∑ i, (ν i : ℂ) • (T i).map τ.1 := by
      intro τ; ext a b; simp [hTT, Matrix.sum_apply]
    simp only [pr, this, hco, Matrix.sum_mul, Matrix.smul_mul, trace_sum, trace_smul, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_comm
  have hherm : ∀ (x : Fin m → ℝ) τ, (Φ (fun i => (x i : ℂ)) τ).IsHermitian := by
    intro x τ
    simp only [hΦ, Matrix.IsHermitian, conjTranspose_sum, conjTranspose_smul,
      (herm_map (hβ _) _).eq, star_def, conj_ofReal]
  have hadd : ∀ z w, Φ (z + w) = fun τ => Φ z τ + Φ w τ := by
    intro z w; funext τ; simp [hΦ, add_smul, Finset.sum_add_distrib]
  have hxy : ∀ x y : Fin m → ℝ, Φ (fun i => (x i : ℂ) + I * y i) =
      fun τ => Φ (fun i => (x i : ℂ)) τ + I • Φ (fun i => (y i : ℂ)) τ := by
    intro x y; funext τ
    simp only [hΦ, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  have him : ∀ z τ, imH (Φ z τ) = Φ (fun i => ((z i).im : ℂ)) τ := by
    intro z τ
    have : z = fun i => ((z i).re : ℂ) + I * (z i).im := by
      funext i; rw [mul_comm, re_add_im]
    conv_lhs => rw [this, hxy]
    exact imH_xy (hherm _ τ) (hherm _ τ)
  have hΦd : Differentiable ℂ (fun (z : Fin m → ℂ) (τ : Ψ) (a b : Fin N) => Φ z τ a b) := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    simp only [hΦ, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have hXc : Continuous fun x : Fin m → ℝ => Φ (fun i => (x i : ℂ)) :=
    hΦd.continuous.comp (continuous_pi fun i => continuous_ofReal.comp (continuous_apply i))
  have hint : ∀ k : ℤ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := k)
  have hccT : ∀ (S : Fin m → Matrix (Fin N) (Fin N) E) (ν : Fin m → ℤ), (∀ i, ccT (S i) = S i) →
      ccT (∑ i, (ν i : E) • S i) = ∑ i, (ν i : E) • S i := by
    intro S ν hS
    ext a b
    have : ∀ i, cc (S i b a) = S i a b := fun i => congrFun (congrFun (hS i) a) b
    simp only [cc] at this
    simp [ccT, cc, Matrix.sum_apply, this]
  have hIntM : ∀ (S : Fin m → Matrix (Fin N) (Fin N) E) (ν : Fin m → ℤ), (∀ i, IntM (S i)) →
      IntM (∑ i, (ν i : E) • S i) := by
    intro S ν hS a b
    rw [Matrix.sum_apply]
    exact IsIntegral.sum _ fun i _ => (hint _).mul (hS i a b)
  refine ⟨m, c, TT, fun x => Φ (fun i => (x i : ℂ)), hc, ?_, fun ν => ⟨hccT T ν hT, ?_⟩, hXc,
    hherm, fun f hf hper => ?_⟩
  · intro ν μ h
    funext j
    have h1 := hpr ν (Φ (Pi.single j 1))
    rw [h, hpr, hcoΦ] at h1
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h1
    exact_mod_cast h1.symm
  · have := hIntM (fun i => (c : E) • T i) ν hD
    simpa only [Den, hTT, Finset.smul_sum, smul_comm (c : E)] using this
  set Ω : Set (Fin m → ℝ) := {y | ∀ τ, (Φ (fun i => (y i : ℂ)) τ).PosDef} with hΩ
  have hmem : ∀ z : Fin m → ℂ, (fun i => (z i).im) ∈ Ω ↔ Φ z ∈ Hn Ψ N := by
    intro z; simp only [hΩ, Hn, Set.mem_setOf_eq, him]
  have hopen : IsOpen Ω := by
    refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
    exact Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
      (fun x : Fin m → ℝ => Φ (fun i => (x i : ℂ)) τ)
      (fun a b => (((continuous_apply τ).comp hXc).matrix_elem a b)) (fun x => hherm x τ) x0 (hx0 τ)
  have hconv : Convex ℝ Ω := by
    intro x hx y hy s t hs ht hst τ
    have e : Φ (fun i => (((s • x + t • y) i : ℝ) : ℂ)) τ =
        (s : ℂ) • Φ (fun i => (x i : ℂ)) τ + (t : ℂ) • Φ (fun i => (y i : ℂ)) τ := by
      simp only [hΦ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofReal_add, ofReal_mul, add_smul,
        Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    rw [e]
    rcases hs.eq_or_lt with h0 | h0
    · have : t = 1 := by linarith
      subst this h0
      simpa using hy τ
    · exact ((hx τ).smul (by exact_mod_cast h0)).add_posSemidef
        ((hy τ).posSemidef.smul (by exact_mod_cast ht))
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.exists_fourier_expansion_holomorphic_tube (Fin m) Ω (fun z => f (Φ z)) hopen hconv
    (hf.comp hΦd.differentiableOn fun z hz => (hmem z).1 hz) (by
      intro z hz k
      have := hper _ (hIntM y k hy) (hccT y k hyc) _ ((hmem z).1 hz)
      rw [← this]
      change f (Φ _) = _
      rw [hadd]
      congr 1
      funext τ
      congr 1
      ext a b
      simp only [hΦ, hβy, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        map_mul, map_sum, map_natCast, map_intCast, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
  refine ⟨a, fun ν Y hY => ?_, fun Z hZ' => ?_⟩
  · have hre : (fun i => (((co Y i).re : ℝ) : ℂ)) = co Y := by
      funext i
      refine Complex.ext (by simp) ?_
      simp [hco, pr_im (hT i), imH_of_herm (hY _).1]
    have hYe : Φ (fun i => (((co Y i).re : ℝ) : ℂ)) = Y := by rw [hre, hΦco]
    rw [ha2 (fun i => (co Y i).re) (fun τ => by rw [hYe]; exact hY τ) ν]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have e := hxy x (fun i => (co Y i).re)
    rw [hYe] at e
    simp only []
    rw [← e, hpr, hcoΦ]
  · have := ha1 (co Z) ((hmem _).2 (by rwa [hΦco]))
    simpa only [hΦco, hpr] using this

theorem rpow_mul_exp_le {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) :
    ∃ C : ℝ, ∀ u : ℝ, 0 < u → u ^ p * Real.exp (-(b * u)) ≤ C := by
  refine ⟨Real.exp (-(p * Real.log (b / (p + 1)))), fun u hu => ?_⟩
  have hε : 0 < b / (p + 1) := by positivity
  rw [Real.rpow_def_of_pos hu, ← Real.exp_add, Real.exp_le_exp]
  have h1 := Real.log_le_sub_one_of_pos (mul_pos hε hu)
  rw [Real.log_mul hε.ne' hu.ne'] at h1
  have h2 : p * (b / (p + 1) * u) ≤ b * u := by
    rw [← mul_assoc]
    gcongr
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hp]

theorem card_pos (hΨ : IsType Ψ) : 0 < Ψ.card := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  rw [Finset.card_pos]
  by_cases h : τ ∈ Ψ
  · exact ⟨τ, h⟩
  · exact ⟨_, not_not.1 (mt (hΨ τ).2 h)⟩

end

end GlobalTheory.SW.Decay

open GlobalTheory.SW.Decay in

theorem GlobalTheory.SW.decay_of_vanishing_at_cusps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N R : ℕ) (δ s : ℝ), 0 < N → 0 < R → 0 < δ → 0 ≤ s → ∃ C : ℝ, ∀ (f : CM Ψ N N → ℂ) (B : ℝ), DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} → (∀ y : Matrix (Fin N) (Fin N) E, IntM y → ccT y = y → ∀ Z ∈ Hn Ψ N, f (fun τ => Z τ + ((R : E) • y).map τ.1) = f Z) → (∀ Z ∈ HnGe Ψ N (δ / 4), ‖f Z‖ ≤ B) → (∀ v : Fin N → E, v ≠ 0 → ∀ Z ∈ Hn Ψ N, Tendsto (fun t : ℝ => f (pushZ Ψ Z v t)) atTop (𝓝 0)) → ∀ Z ∈ HnGe Ψ N δ, ‖f Z‖ * detIm Z ^ s ≤ C * B := by
  intro E _ _ _ Ψ hΨ N R δ s hN hR hδ hs
  obtain ⟨m, c, T, X, hc, hinj, hT, hXc, hX, hF⟩ := exists_fourier hΨ N R hR
  obtain ⟨k, hk, hk'⟩ := GlobalTheory.T.trace_pairing_ge_detIm_pow_hermitianHalfSpace E Ψ hΨ N c hN hc
  have hsum := GlobalTheory.T.summable_exp_neg_trace_totallyPositive_hermitian E Ψ hΨ N c (π * δ / 2) hc (by positivity)
  set S : Set (Fin m → ℤ) := {ν | ∀ τ : Ψ, ((T ν).map τ.1).PosSemidef} with hS
  have hsum' : Summable fun ν : S =>
      Real.exp (-(π * δ / 2 * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re)) := by
    have hi : Function.Injective fun ν : S => (⟨T ν.1, (hT _).1, (hT _).2, ν.2⟩ :
        {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧
          ∀ τ : Ψ, (T.map τ.1).PosSemidef}) :=
      fun ν μ h => Subtype.ext (hinj (Subtype.mk.inj h))
    have := hsum.comp_injective hi
    simpa only [Function.comp_def] using this
  set σ := ∑' ν : S, Real.exp (-(π * δ / 2 * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re)) with hσ
  have hσ0 : 0 ≤ σ := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hd : (0 : ℝ) < ((Ψ.card * N : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (card_pos hΨ) hN
  set d : ℝ := ((Ψ.card * N : ℕ) : ℝ)
  obtain ⟨C, hC⟩ := rpow_mul_exp_le (b := π * k) (p := d * s) (by positivity) (by positivity)
  refine ⟨C * σ, fun f B hf hper hB hv Z hZ => ?_⟩
  obtain ⟨a, ha, hfa⟩ := hF f hf hper
  have hη : 0 < δ / 4 := by positivity
  have hZ' : Z ∈ Hn Ψ N := fun τ => posDef_of_ge hδ (hZ τ)
  have hB0 : 0 ≤ B := by
    refine (norm_nonneg _).trans (hB (fun _ => 0 + I • (((δ / 4 : ℝ) : ℂ) • 1)) fun τ => ?_)
    rw [imH_xy isHermitian_zero (posDef_of_ge hη (by simpa using PosSemidef.zero)).1]
    simpa using PosSemidef.zero
  have hD : 0 < detIm Z :=
    Finset.prod_pos fun τ _ => (ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA.det_re_pos_im (hZ' τ)).1
  set u := detIm Z ^ (1 / d) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hD _
  have hus : detIm Z ^ s = u ^ (d * s) := by
    rw [hu, ← Real.rpow_mul hD.le]; congr 1; field_simp
  have h1 : HasSum (fun ν : S => a ν.1 * cexp (2 * π * I * pr (T ν.1) Z)) (f Z) := by
    have hsupp : Function.support (fun ν => a ν * cexp (2 * π * I * pr (T ν) Z)) ⊆ S :=
      fun ν hν τ => coef_psd hX (hT ν).1 hη hB (ha ν) (left_ne_zero_of_mul hν) τ
    have := (hasSum_subtype_iff_of_support_subset hsupp).2 (hfa Z hZ')
    simpa only [Function.comp_def] using this
  have h2 : ‖f Z‖ ≤ B * Real.exp (-(π * k * u)) * σ := by
    refine h1.norm_le_of_bounded (hsum'.hasSum.mul_left _) fun ν => ?_
    by_cases h0 : a ν.1 = 0
    · rw [h0, zero_mul, norm_zero]; positivity
    have hpd := coef_posDef hXc hX (hT ν.1).1 hη hf hB (ha ν.1) hv h0
    have b1 := coef_bound hX (hT ν.1).1 hη hB (ha ν.1)
      (Y := fun _ => ((δ / 4 : ℝ) : ℂ) • 1) (fun _ => by simpa using PosSemidef.zero)
    have b2 := hk' _ (hT ν.1).1 (hT ν.1).2 hpd Z hZ'
    have tr : ∀ η : ℝ, ∑ τ : Ψ, ((T ν.1).map τ.1 * ((η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))).trace.re
        = η * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re := by
      intro η
      simp only [Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul, re_ofReal_mul,
        Finset.mul_sum]
    have b3 : δ * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re ≤
        ∑ τ : Ψ, ((T ν.1).map τ.1 * imH (Z τ)).trace.re := by
      rw [← tr]
      refine Finset.sum_le_sum fun τ _ => ?_
      have := GlobalTheory.re_trace_mul_nonneg_of_posSemidef (ν.2 τ) (hZ τ)
      rw [Matrix.mul_sub, trace_sub, map_sub, sub_nonneg] at this
      exact this
    rw [tr] at b1
    rw [norm_mul, norm_e, pr_im (hT ν.1).1]
    refine (mul_le_mul_of_nonneg_right b1 (Real.exp_pos _).le).trans ?_
    rw [mul_assoc B, mul_assoc B, ← Real.exp_add, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB0
    replace b2 : k * u ≤ _ := b2
    generalize ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re = p at b3 ⊢
    generalize ∑ τ : Ψ, ((T ν.1).map τ.1 * imH (Z τ)).trace.re = q at b2 b3 ⊢
    have := add_le_add (mul_le_mul_of_nonneg_left b2 Real.pi_pos.le)
      (mul_le_mul_of_nonneg_left b3 Real.pi_pos.le)
    linarith
  calc ‖f Z‖ * detIm Z ^ s ≤ B * Real.exp (-(π * k * u)) * σ * u ^ (d * s) := by
        rw [hus]; gcongr
    _ = u ^ (d * s) * Real.exp (-(π * k * u)) * σ * B := by ring
    _ ≤ C * σ * B := by gcongr; exact hC u hu0
