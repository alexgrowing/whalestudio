import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKTypeOfMap

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology

namespace GlobalTheory.LowTypeRestriction

open Formalism.MainNotions.S GlobalTheory.GardingVec

def distOne {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) : ℝ := (trace ((x - 1)ᴴ * (x - 1))).re

theorem distOne_eq {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) :
    distOne x = ∑ j, ∑ i, ‖(x - 1) i j‖ ^ 2 := by
  simp only [distOne, trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem distOne_conj {n : ℕ} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ unitaryGroup (Fin n) ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) : distOne (kᴴ * x * k) = distOne x := by
  have h1 : kᴴ * k = 1 := (mem_unitaryGroup_iff').1 hk
  have h2 : k * kᴴ = 1 := (mem_unitaryGroup_iff).1 hk
  have e : kᴴ * x * k - 1 = kᴴ * (x - 1) * k := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  unfold distOne
  rw [e]
  have e2 : (kᴴ * (x - 1) * k)ᴴ * (kᴴ * (x - 1) * k) = kᴴ * ((x - 1)ᴴ * (x - 1)) * k := by
    calc (kᴴ * (x - 1) * k)ᴴ * (kᴴ * (x - 1) * k) = kᴴ * ((x - 1)ᴴ * (k * kᴴ) * (x - 1)) * k := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one]
  rw [e2, trace_mul_cycle, h2, Matrix.one_mul]

theorem dist_le_of_distOne {n : ℕ} {x : Matrix (Fin n) (Fin n) ℂ} {δ : ℝ} (hδ : 0 ≤ δ) (h : distOne x ≤ δ ^ 2) :
    (x : Fin n → Fin n → ℂ) ∈ Metric.closedBall (α := Fin n → Fin n → ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) δ := by
  refine (Metric.mem_closedBall (α := Fin n → Fin n → ℂ)).2 ((dist_pi_le_iff hδ).2 fun i => (dist_pi_le_iff hδ).2 fun j => ?_)
  rw [dist_eq_norm]
  have h1 : ‖(x - 1) i j‖ ^ 2 ≤ δ ^ 2 := by
    refine le_trans ?_ h
    rw [distOne_eq]
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => ∑ i, ‖(x - 1) i j‖ ^ 2)
      (fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.mem_univ j))
    exact Finset.single_le_sum (f := fun i => ‖(x - 1) i j‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
  exact abs_le_of_sq_le_sq' h1 hδ |>.2

theorem exists_sublevel {n : ℕ} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C ∧ C ⊆ U ∧ ∀ x, distOne x ≤ δ → x ∈ C := by
  obtain ⟨δ, hδ, hs⟩ := (Metric.nhds_basis_closedBall (α := Fin n → Fin n → ℂ)
    (x := (1 : Matrix (Fin n) (Fin n) ℂ))).mem_iff.1 hU
  exact ⟨δ ^ 2, by positivity, Metric.closedBall (α := Fin n → Fin n → ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) δ,
    isCompact_closedBall (α := Fin n → Fin n → ℂ) _ _, hs, fun x hx => dist_le_of_distOne hδ.le hx⟩

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_distOne {n : ℕ} : ContDiff ℝ ∞ (distOne (n := n)) := by
  have h : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ => x - 1 := contDiff_id.sub contDiff_const
  have h2 := (contDiff_conjTranspose.comp h).mul h
  exact Complex.reCLM.contDiff.comp
    ((LinearMap.toContinuousLinearMap (traceLinearMap (Fin n) ℝ ℂ)).contDiff.comp h2)

theorem exists_bump {n : ℕ} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ φ : Matrix (Fin n) (Fin n) ℂ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ (∀ x, φ x ≠ 0 → x ∈ U) ∧
      (∀ x, 0 ≤ φ x) ∧ φ 1 = 1 ∧ ∀ k ∈ unitaryGroup (Fin n) ℂ, ∀ x, φ (kᴴ * x * k) = φ x := by
  obtain ⟨δ, hδ, C, hC, hCU, hx⟩ := exists_sublevel hU
  let b : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hb : ∀ x, b (distOne x) ≠ 0 → x ∈ C := fun x h => by
    have : distOne x ∈ Function.support b := h
    rw [b.support_eq, mem_ball_zero_iff] at this
    exact hx x ((le_abs_self _).trans (le_of_lt this))
  refine ⟨fun x => b (distOne x), b.contDiff.comp contDiff_distOne, HasCompactSupport.intro hC fun x h => ?_,
    fun x h => hCU (hb x h), fun x => b.nonneg, ?_, fun k hk x => by simp only [distOne_conj hk]⟩
  · by_contra h'; exact h (hb x h')
  · refine b.one_of_mem_closedBall ?_
    have : distOne (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [distOne]
    rw [this]; exact Metric.mem_closedBall_self b.rIn_pos.le

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {φ : Matrix (Fin n) (Fin n) ℂ → ℝ}

theorem integrable_garding (hσ : IsURepOn (UJset ε) σ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) (w : H) :
    Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • σ (umat g) w) (Formalism.REAL.muG ε) := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w := (hσ.2.2 w).comp_continuous hu fun g => g.2
  have hψc : HasCompactSupport fun g : Formalism.REAL.UJ ε => φ (umat g) := hφc.comp_isClosedEmbedding hemb
  exact ((hφ.comp hu).smul hb).integrable_of_hasCompactSupport hψc.smul_right

def garding (hσ : IsURepOn (UJset ε) σ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) : H →ₗ[ℂ] H where
  toFun w := ∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂(Formalism.REAL.muG ε)
  map_add' w w' := by
    rw [← integral_add (integrable_garding hσ hφ hφc w) (integrable_garding hσ hφ hφc w')]
    simp only [map_add, smul_add]
  map_smul' c w := by
    rw [RingHom.id_apply, ← integral_smul]
    simp only [map_smul, smul_comm c]

theorem garding_apply (hσ : IsURepOn (UJset ε) σ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) (w : H) :
    garding hσ hφ hφc w = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂(Formalism.REAL.muG ε) := rfl

theorem garding_ne_zero [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : φ 1 = 1) {w : H} (hw : w ≠ 0)
    (hs : ∀ g ∈ UJset ε, φ g ≠ 0 → ‖σ g w - w‖ < ‖w‖ / 2) : garding hσ hφ hφc w ≠ 0 := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hint := integrable_garding hσ hφ hφc w
  rw [garding_apply]
  set μ := Formalism.REAL.muG ε
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := hemb.continuous
  have hψ : Continuous fun g : Formalism.REAL.UJ ε => φ (umat g) := hφ.comp hu
  have hψc : HasCompactSupport fun g : Formalism.REAL.UJ ε => φ (umat g) := hφc.comp_isClosedEmbedding hemb
  have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) μ := hψ.integrable_of_hasCompactSupport hψc
  have hpos : 0 < ∫ g : Formalism.REAL.UJ ε, φ (umat g) ∂μ :=
    hψ.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hψc (fun g => hφ0 _)
      (by show φ 1 ≠ 0; rw [hφ1]; exact one_ne_zero)
  intro h0
  have e1 : ∫ g : Formalism.REAL.UJ ε, (φ (umat g) • σ (umat g) w - φ (umat g) • w) ∂μ
      = -((∫ g : Formalism.REAL.UJ ε, φ (umat g) ∂μ) • w) := by
    rw [integral_sub hint (hψi.smul_const w), h0, integral_smul_const, zero_sub]
  have e2 : ‖∫ g : Formalism.REAL.UJ ε, (φ (umat g) • σ (umat g) w - φ (umat g) • w) ∂μ‖
      ≤ ∫ g : Formalism.REAL.UJ ε, φ (umat g) * (‖w‖ / 2) ∂μ := by
    refine norm_integral_le_of_norm_le (hψi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ0 _)]
    by_cases hg : φ (umat g) = 0
    · simp [hg]
    · exact mul_le_mul_of_nonneg_left (le_of_lt (hs _ g.2 hg)) (hφ0 _)
  rw [e1, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le, integral_mul_const] at e2
  nlinarith [mul_pos hpos hwpos]

theorem garding_translate [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (w : H) {x y : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ UJset ε) (hyx : y * x = 1) :
    σ x (garding hσ hφ hφc w)
      = ∫ g : Formalism.REAL.UJ ε, φ (y * umat g) • σ (umat g) w ∂(Formalism.REAL.muG ε) := by
  obtain ⟨-, hrange⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  obtain ⟨z, hz⟩ : x ∈ Set.range (fun g : Formalism.REAL.UJ ε => umat g) := by
    rw [show Set.range (fun g : Formalism.REAL.UJ ε => umat g) = _ from hrange]; exact hx
  have hz' : umat z = x := hz
  rw [garding_apply, ← ContinuousLinearMap.integral_comp_comm _ (integrable_garding hσ hφ hφc w),
    ← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => φ (y * umat g) • σ (umat g) w) z]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have e : umat (z * g) = x * umat g := by rw [← hz']; rfl
  simp only [e]
  rw [← Matrix.mul_assoc, hyx, Matrix.one_mul, hσ.1.2 _ hx _ g.2, ContinuousLinearMap.map_smul_of_tower]
  rfl

theorem kset_subset {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : g ∈ UJset ε := by
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  have h1 : gᴴ * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem garding_comm [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hinv : ∀ k ∈ unitaryGroup (Fin n) ℂ, ∀ x, φ (kᴴ * x * k) = φ x)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) (w : H) :
    σ k (garding hσ hφ hφc w) = garding hσ hφ hφc (σ k w) := by
  have h1 : kᴴ * k = 1 := (mem_unitaryGroup_iff').1 hk.1
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  obtain ⟨-, hrange⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  obtain ⟨z, hz⟩ : k ∈ Set.range (fun g : Formalism.REAL.UJ ε => umat g) := by
    rw [show Set.range (fun g : Formalism.REAL.UJ ε => umat g) = _ from hrange]; exact kset_subset hk
  have hz' : umat z = k := hz
  rw [garding_translate hσ hφ hφc w (kset_subset hk) h1, garding_apply,
    ← integral_mul_right_eq_self (fun g : Formalism.REAL.UJ ε => φ (kᴴ * umat g) • σ (umat g) w) z]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have e : umat (g * z) = umat g * k := by rw [← hz']; rfl
  simp only [e]
  rw [← Matrix.mul_assoc, hinv k hk.1, hσ.1.2 _ g.2 _ (kset_subset hk)]
  rfl

theorem contDiff_garding [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (w : H) (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ) (hx : ContDiff ℝ ∞ x)
    (hxG : ∀ t, x t ∈ UJset ε) : ContDiff ℝ ∞ fun t => σ (x t) (garding hσ hφ.continuous hφc w) := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w := (hσ.2.2 w).comp_continuous hu fun g => g.2
  let y : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun t => Formalism.REAL.Jm ε * (x t)ᴴ * Formalism.REAL.Jm ε
  have hy : ContDiff ℝ ∞ y := (contDiff_const.mul (contDiff_conjTranspose.comp hx)).mul contDiff_const
  have hyx : ∀ t, y t * x t = 1 := fun t => by
    have h : (x t)ᴴ * Formalism.REAL.Jm ε * x t = Formalism.REAL.Jm ε := hxG t
    calc y t * x t = Formalism.REAL.Jm ε * ((x t)ᴴ * Formalism.REAL.Jm ε * x t) := by simp only [y, Matrix.mul_assoc]
      _ = 1 := by rw [h, Formalism.REAL.Jm_mul_self]
  have hxy : ∀ t, x t * y t = 1 := fun t => mul_eq_one_comm.1 (hyx t)
  have hform := fun t => garding_translate hσ hφ.continuous hφc w (hxG t) (hyx t)
  simp only [hform]
  set μ := Formalism.REAL.muG ε
  refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
  have hC : IsCompact (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1) (tsupport φ)) :=
    ((isCompact_closedBall t₀ 1).image hx.continuous).mul hφc
  have hK := hemb.isCompact_preimage hC
  have hs : ContDiff ℝ ∞ fun t => ∫ g in (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹'
      (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1) (tsupport φ)),
      φ (y t * umat g) • σ (umat g) w ∂μ :=
    contDiff_infty.2 fun m => contDiff_setIntegral_nat μ hK (hu.prodMk hb) m
      (fun z : (Fin k → ℝ) × (Matrix (Fin n) (Fin n) ℂ × H) => φ (y z.1 * z.2.1) • z.2.2)
      ((hφ.comp ((hy.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd))).smul
        (contDiff_snd.comp contDiff_snd))
  refine hs.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [Metric.closedBall_mem_nhds t₀ one_pos] with t ht
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
  by_contra hne
  refine hg ⟨x t, ⟨t, ht, rfl⟩, y t * umat g, subset_tsupport _ fun h => hne (by rw [h, zero_smul]), ?_⟩
  show x t * (y t * umat g) = umat g
  rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]

theorem isKTypeOf_map {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hS : IsKTypeOf ε σ Λ S) (L : H →ₗ[ℂ] H)
    (hL : ∀ k ∈ Formalism.REAL.Kset ε, ∀ w, σ k (L w) = L (σ k w)) {v : H} (hv : v ∈ S) (hLv : L v ≠ 0) :
    IsKTypeOf ε σ Λ (S.map L) := by
  first
  | exact @_root_.GlobalTheory.KTypeUnderMaps.isKTypeOf_map
  | exact _root_.GlobalTheory.KTypeUnderMaps.isKTypeOf_map
  | (apply _root_.GlobalTheory.KTypeUnderMaps.isKTypeOf_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.KTypeUnderMaps.isKTypeOf_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.KTypeUnderMaps.isKTypeOf_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.KTypeUnderMaps.isKTypeOf_map ..)

theorem exists_smoothVec_lowKSub {lam : Fin n → ℝ} (hσ : IsDS ε lam σ) {P G : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) :
    ∃ v ∈ lowKSub ε lam σ, v ≠ 0 ∧
      Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v := by
  obtain ⟨_, -, hU, -, -, ⟨S, hS⟩, -⟩ := hσ
  obtain ⟨w, hwS, hw, -⟩ := hS.2.2.2.1
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := (1 : Formalism.REAL.UJ ε).2
  have hnb : {g | ‖σ g w - w‖ < ‖w‖ / 2} ∈ 𝓝[UJset ε] (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := (hU.2.2 w 1 hone) (Metric.ball_mem_nhds _ (half_pos hwpos))
    simpa [hU.1.1, Set.preimage, dist_eq_norm] using h
  obtain ⟨U, hUn, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnb
  obtain ⟨φ, hφ, hφc, hφU, hφ0, hφ1, hinv⟩ := exists_bump hUn
  have hne := garding_ne_zero hU hφ.continuous hφc hφ0 hφ1 hw fun g hg h0 => hUs ⟨hφU g h0, hg⟩
  have hT := isKTypeOf_map hS (garding hU hφ.continuous hφc)
    (fun k hk w => garding_comm hU hφ.continuous hφc hinv hk w) hwS hne
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  refine ⟨_, (le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) hT) ⟨w, hwS, rfl⟩, hne,
    fun k Xs hX => contDiff_garding hU hφ hφc w k _
      ((contDiff_const.mul (contDiff_expProd Xs)).mul contDiff_const) fun t => ?_⟩
  refine conj_mem hP h (list_prod_mem _ fun g hg => ?_)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
  exact exp_mem hG (hX i) _

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
  Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lowT_ne_bot {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    lowT M τ ≠ ⊥ := by
  obtain ⟨v, hv, h0, hs⟩ := exists_smoothVec_lowKSub (M.ds τ) (M.fr_unit τ) (M.fr_gram τ)
  exact (Submodule.ne_bot_iff _).2 ⟨⟨v, Submodule.subset_span hs⟩, hv, fun h => h0 (congrArg Subtype.val h)⟩

end GlobalTheory.LowTypeRestriction

end
