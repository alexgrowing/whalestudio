import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsOmNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsOmNVbInt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNPolyPencil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology PtsPencil

namespace OmNPoly

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sum_sq_pos {z : (Σ k, ι k) → ℂ} {k : K} (hz : ∃ i, z ⟨k, i⟩ ≠ 0) :
    0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := hz
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
    (Finset.single_le_sum (fun i _ => sq_nonneg ‖z ⟨k, i⟩‖) (Finset.mem_univ i))

theorem log_refNorm (a : K → ℤ) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (refNorm a z) = ∑ k, (a k : ℝ) / 2 * Real.log (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
  unfold refNorm
  rw [Real.log_prod fun k _ => (Real.rpow_pos_of_pos (sum_sq_pos (hz k)) _).ne']
  exact Finset.sum_congr rfl fun k _ => Real.log_rpow (sum_sq_pos (hz k)) _

theorem log_refNorm_lin (m a : K → ℤ) (q p : ℕ) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (refNorm ((q : ℤ) • m + (p : ℤ) • a) z) =
      q * Real.log (refNorm m z) + p * Real.log (refNorm a z) := by
  rw [log_refNorm _ hz, log_refNorm _ hz, log_refNorm _ hz, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem log_hermOfFun (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((hermOfFun ι a F).h z) =
      Real.log (refNorm a z) + Real.log (F (orbitRep z) / refNorm a (orbitRep z)) := by
  show Real.log (refNorm a z * Real.exp (Real.log (F (orbitRep z) / refNorm a (orbitRep z)))) = _
  rw [Real.log_mul (refNorm_pos a hz).ne' (Real.exp_pos _).ne', Real.log_exp]

theorem orbitRep_ne {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, orbitRep z ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, _, hzc⟩ := exists_eq_smul_orbitRep z
  intro k
  obtain ⟨i, hi⟩ := hz k
  refine ⟨i, fun h0 => hi ?_⟩
  rw [hzc]
  simp [torusSmul, h0]

theorem orbitRep_orbitRep (z : (Σ k, ι k) → ℂ) : orbitRep (orbitRep z) = orbitRep z := by
  unfold orbitRep
  rw [Quotient.out_eq]

theorem hermOfFun_h_orbitRep (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, orbitRep z ⟨k, i⟩ ≠ 0) (hF : 0 < F (orbitRep z)) :
    (hermOfFun ι a F).h (orbitRep z) = F (orbitRep z) := by
  show refNorm a (orbitRep z) * Real.exp (Real.log (F (orbitRep (orbitRep z)) /
    refNorm a (orbitRep (orbitRep z)))) = _
  rw [orbitRep_orbitRep, Real.exp_log (div_pos hF (refNorm_pos a hz))]
  field_simp [(refNorm_pos a hz).ne']

theorem rescale_inv_pow_mul (x c s : ℝ) (n i : ℕ) (hx : x ≠ 0) (hi : i ≤ n) :
    (x ^ n)⁻¹ * (c * 1 ^ i * x ^ (n - i) * s) = c * (1 / x) ^ i * 1 ^ (n - i) * s := by
  rw [pow_sub₀ _ hx hi, one_div, inv_pow, one_pow, one_pow,
    show (x ^ n)⁻¹ * (c * 1 * (x ^ n * (x ^ i)⁻¹) * s) = ((x ^ n)⁻¹ * x ^ n) * (c * (x ^ i)⁻¹ * s) by ring,
    inv_mul_cancel₀ (pow_ne_zero n hx)]
  ring

theorem rescale_mul_div_pow (x c s : ℝ) (n i : ℕ) (hx : x ≠ 0) (hi : i ≤ n) :
    c * 1 ^ i * x ^ (n - i) * s / x ^ n = c * s * (1 / x) ^ i := by
  rw [div_eq_inv_mul, rescale_inv_pow_mul x c s n i hx hi, one_pow]
  ring

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

omit [DecidableEq Ψ] in
theorem vertFactor_nonneg (p : ℕ) (z : (Σ k, ι k) → ℂ) : 0 ≤ D.vertFactor p z := by
  unfold ComponentData.vertFactor
  split_ifs
  · positivity
  · exact zero_le_one

theorem log_NbarQ_affine (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    ∃ U V : ℝ, (∀ q : ℕ, 1 ≤ q → Real.log ((X.NbarQ B 1 q t).h z) = q * U + V) ∧
      Real.log ((muReg X.H X.S B t).h z) = U := by
  have hz' := hz.1
  have hw := orbitRep_ne hz'
  have hE : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    mul_pos (X.S.ref.pos _ hw) (Real.exp_pos _)
  have hA : 0 < D.A'.h (orbitRep z) := D.A'.pos _ hw
  have hV : 0 ≤ ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z) :=
    Finset.prod_nonneg fun p' _ => vertFactor_nonneg p' _
  have hreg : (X.S.regLine t).h (orbitRep z) =
      X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) := by
    unfold LogLogRegularisationSetting.regLine
    exact hermOfFun_h_orbitRep _ _ hw hE
  obtain ⟨Ew, hEw⟩ : ∃ x, x = X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    ⟨_, rfl⟩
  obtain ⟨Vw, hVw⟩ : ∃ x, x = ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z) := ⟨_, rfl⟩
  have hN : ∀ q : ℕ, Real.log ((X.NbarQ B 1 q t).h z) =
      q * Real.log (refNorm (muTwDeg X.H B) z) + Real.log (refNorm D.a' z) +
        Real.log ((Ew * Vw) ^ q * D.A'.h (orbitRep z) /
          refNorm ((q : ℤ) • muTwDeg X.H B + ((1 : ℕ) : ℤ) • D.a') (orbitRep z)) := by
    intro q
    unfold ComponentSetting.NbarQ
    rw [smoothRep_h _ hz, log_hermOfFun _ _ hz']
    beta_reduce
    rw [log_refNorm_lin _ _ _ _ hz', ← hEw, ← hVw, mul_pow, pow_one, Nat.cast_one, one_mul]
  have hM : Real.log ((muReg X.H X.S B t).h z) = Real.log (refNorm (muTwDeg X.H B) z) +
      Real.log (Ew * Vw / refNorm (muTwDeg X.H B) (orbitRep z)) := by
    unfold muReg
    rw [smoothRep_h _ hz, log_hermOfFun _ _ hz']
    beta_reduce
    rw [hreg, ← hEw, ← hVw]
  have hLRw : ∀ q : ℕ, Real.log (refNorm ((q : ℤ) • muTwDeg X.H B + ((1 : ℕ) : ℤ) • D.a') (orbitRep z)) =
      q * Real.log (refNorm (muTwDeg X.H B) (orbitRep z)) + Real.log (refNorm D.a' (orbitRep z)) := fun q => by
    rw [log_refNorm_lin _ _ _ _ hw, Nat.cast_one, one_mul]
  have hEV : 0 ≤ Ew * Vw := by
    rw [hEw, hVw]
    exact mul_nonneg hE.le hV
  rcases hEV.eq_or_lt with h0 | hpos
  · refine ⟨Real.log (refNorm (muTwDeg X.H B) z), Real.log (refNorm D.a' z), fun q hq => ?_, ?_⟩
    · rw [hN q, ← h0, zero_pow (by omega : q ≠ 0), zero_mul, zero_div, Real.log_zero, add_zero]
    · rw [hM, ← h0, zero_div, Real.log_zero, add_zero]
  · refine ⟨Real.log (refNorm (muTwDeg X.H B) z) + Real.log (Ew * Vw) -
        Real.log (refNorm (muTwDeg X.H B) (orbitRep z)),
      Real.log (refNorm D.a' z) + Real.log (D.A'.h (orbitRep z)) - Real.log (refNorm D.a' (orbitRep z)),
      fun q hq => ?_, ?_⟩
    · rw [hN q, Real.log_div (mul_pos (pow_pos hpos q) hA).ne' (refNorm_pos _ hw).ne',
        Real.log_mul (pow_pos hpos q).ne' hA.ne', Real.log_pow, hLRw q]
      ring
    · rw [hM, Real.log_div hpos.ne' (refNorm_pos _ hw).ne']
      ring

theorem log_NbarQ_eq (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) (q : ℕ) (hq : 1 ≤ q) :
    Real.log ((X.NbarQ B 1 q t).h z) =
      q * (Real.log ((X.NbarQ B 1 2 t).h z) - Real.log ((X.NbarQ B 1 1 t).h z)) +
        (2 * Real.log ((X.NbarQ B 1 1 t).h z) - Real.log ((X.NbarQ B 1 2 t).h z)) := by
  obtain ⟨U, V, hUV, -⟩ := log_NbarQ_affine X B t hz
  rw [hUV q hq, hUV 1 le_rfl, hUV 2 (by norm_num)]
  push_cast
  ring

theorem log_muReg_eq (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    Real.log ((muReg X.H X.S B t).h z) =
      Real.log ((X.NbarQ B 1 2 t).h z) - Real.log ((X.NbarQ B 1 1 t).h z) := by
  obtain ⟨U, V, hUV, hU⟩ := log_NbarQ_affine X B t hz
  rw [hU, hUV 1 le_rfl, hUV 2 (by norm_num)]
  push_cast
  ring

end OmNPoly

theorem OmNPoly.proof (h₁ : NbarSemipos.Statement) (h₂ : OmNVbInt.Statement) (h₃ : PtsIntegrableStatement) :
    OmNPoly.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B _ _
  have hQ : IsArithVar (mCoordIdeal D.y) (D.n + 1) := D.arith
  let α : ℝ → ((Σ k, ι k) → ℂ) → ℝ := fun t z =>
    1 * Real.log ((X.NbarQ B 1 2 t).h z) + (-1) * Real.log ((X.NbarQ B 1 1 t).h z)
  let β : ℝ → ((Σ k, ι k) → ℂ) → ℝ := fun t z =>
    (-1) * Real.log ((X.NbarQ B 1 2 t).h z) + 2 * Real.log ((X.NbarQ B 1 1 t).h z)
  have hsm : ∀ q : ℕ, 1 ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (X.NbarQ B 1 q t) := by
    intro q hq
    obtain ⟨t₁, ht₁, h⟩ := h₁ II Ψ K ι Ω E D O Lt X B 1 q le_rfl hq
    filter_upwards [Ioc_mem_nhdsGT ht₁] with t ht
    exact (show IsSmoothHerm _ ∧ _ from h t ht.1 ht.2).1
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (X.NbarQ B 1 1 t) ∧ IsSmoothHerm (X.NbarQ B 1 2 t) ∧
      ∀ j : Fin (D.n + 1), IsSmoothHerm (X.NbarQ B 1 ((j : ℕ) + 1) t) ∧
        IsPtsIntegrable (mCoordIdeal D.y) (X.omN B 1 ((j : ℕ) + 1) t) (fun z => X.Cd.cuspWeight z / 2) :=
    (hsm 1 le_rfl).and ((hsm 2 (by norm_num)).and (eventually_all.2 fun j =>
      (hsm ((j : ℕ) + 1) (by omega)).and (h₂ II Ψ K ι Ω E D O Lt X B 1 ((j : ℕ) + 1) le_rfl (by omega))))
  refine ⟨fun i t => if i = 0 then
      ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ z => Real.log ((muReg X.H X.S B t).h z))
        (fun z => X.Cd.cuspWeight z / 2)
    else (D.n.choose i : ℝ) * ptsIntegral (mCoordIdeal D.y) (mixW (e := D.n) (α t) (β t) i)
        (fun z => X.Cd.cuspWeight z / 2),
    fun i t => if i = 0 then geomDeg (mCoordIdeal D.y) (muReg X.H X.S B t) D.n
    else (D.n.choose i : ℝ) * ptsIntegral (mCoordIdeal D.y) (mixW (e := D.n) (α t) (β t) i) (fun _ => 1),
    rfl, rfl, fun q hq => ?_⟩
  filter_upwards [hall] with t ht
  obtain ⟨hs1, hs2, hnodes⟩ := ht
  have hα : ∀ Ψp, IsC2AlongSheets (e := D.n) (mCoordIdeal D.y) Ψp (α t) := fun Ψp =>
    (isC2AlongSheets_log_metric _ Ψp hs2).lin (isC2AlongSheets_log_metric _ Ψp hs1) 1 (-1)
  have hβ : ∀ Ψp, IsC2AlongSheets (e := D.n) (mCoordIdeal D.y) Ψp (β t) := fun Ψp =>
    (isC2AlongSheets_log_metric _ Ψp hs2).lin (isC2AlongSheets_log_metric _ Ψp hs1) (-1) 2
  have hom : ∀ r : ℕ, 1 ≤ r → ∀ (j : Fin D.n), ∀ z ∈ mcPts (mCoordIdeal D.y),
      X.omN B 1 r t j z = 1 * α t z + (1 / (r : ℝ)) * β t z := by
    intro r hr j z hz
    have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp only [ComponentSetting.omN, α, β]
    rw [OmNPoly.log_NbarQ_eq X B t hz r hr]
    field_simp
    ring
  have hpot : ∀ r : ℕ, 1 ≤ r → ∀ (j : Fin D.n), ∀ z ∈ mcPts (mCoordIdeal D.y),
      Real.log ((X.NbarQ B 1 r t).h z) = (r : ℝ) * α t z + 1 * β t z := by
    intro r hr j z hz
    simp only [α, β]
    rw [OmNPoly.log_NbarQ_eq X B t hz r hr]
    ring
  have hmu : ∀ (j : Fin D.n), ∀ z ∈ mcPts (mCoordIdeal D.y),
      Real.log ((muReg X.H X.S B t).h z) = α t z := by
    intro j z hz
    simp only [α]
    rw [OmNPoly.log_muReg_eq X B t hz]
    ring
  have hmixInt : ∀ g : ((Σ k, ι k) → ℂ) → ℝ,
      (∀ j : Fin (D.n + 1), IsPtsIntegrable (mCoordIdeal D.y) (X.omN B 1 ((j : ℕ) + 1) t) g) →
      ∀ Ψp : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D.n + 1) → ℂ), IsGoodProj (mCoordIdeal D.y) Ψp →
        ∀ i ∈ Finset.range (D.n + 1), Integrable (fun y => ∑ᶠ w ∈ fibre (mCoordIdeal D.y) Ψp y,
          sheetDensity (mCoordIdeal D.y) Ψp (mixW (α t) (β t) i) g y w) := by
    intro g hg Ψp hΨp i hi
    have hM := integrable_of_nodes (N := D.n + 1) (μ := volume)
      (fun i y => (D.n.choose i : ℝ) * ∑ᶠ w ∈ fibre (mCoordIdeal D.y) Ψp y,
        sheetDensity (mCoordIdeal D.y) Ψp (mixW (α t) (β t) i) g y w)
      (fun j => by
        refine (hg j Ψp hΨp).congr (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [fibreSum_pencil hQ hΨp (hα Ψp) (hβ Ψp) 1 (1 / (((j : ℕ) + 1 : ℕ) : ℝ))
          (hom _ (by omega)) g y]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring) i (Finset.mem_range.1 hi)
    have hc : (D.n.choose i : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).ne'
    refine (hM.const_mul (D.n.choose i : ℝ)⁻¹).congr (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hone : ∀ j : Fin (D.n + 1),
      IsPtsIntegrable (mCoordIdeal D.y) (X.omN B 1 ((j : ℕ) + 1) t) (fun _ => 1) := by
    intro j Ψp hΨp
    have hr1 : 1 ≤ (j : ℕ) + 1 := by omega
    have hr0 : (((j : ℕ) + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h := h₃ K ι (mCoordIdeal D.y) D.n Ψp (fun _ => X.NbarQ B 1 ((j : ℕ) + 1) t) oneLine 1 hQ hΨp
      (fun _ => (hnodes j).1) isSmoothHerm_oneLine (isSectionOn_one hQ.2.1.1 rfl)
    have hln : logNorm (oneLine (ι := ι)) 1 = fun _ => 1 := funext logNorm_oneLine
    rw [hln] at h
    refine (h.const_mul ((((j : ℕ) + 1 : ℕ) : ℝ) ^ D.n)⁻¹).congr (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [fibreSum_pencil hQ hΨp (hα Ψp) (hβ Ψp) (((j : ℕ) + 1 : ℕ) : ℝ) 1
        (φ := pot fun _ => X.NbarQ B 1 ((j : ℕ) + 1) t) (fun k z hz => hpot _ hr1 k z hz) _ y,
      fibreSum_pencil hQ hΨp (hα Ψp) (hβ Ψp) 1 (1 / (((j : ℕ) + 1 : ℕ) : ℝ)) (hom _ hr1) _ y,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact OmNPoly.rescale_inv_pow_mul _ _ _ _ _ hr0 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  have hintU := hmixInt _ fun j => (hnodes j).2
  have hint1 := hmixInt _ hone
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hmix0 : ∀ g : ((Σ k, ι k) → ℂ) → ℝ, ptsIntegral (mCoordIdeal D.y) (mixW (e := D.n) (α t) (β t) 0) g =
      ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ z => Real.log ((muReg X.H X.S B t).h z)) g := by
    intro g
    rw [mixW_zero]
    exact ptsIntegral_congr _ (fun j z hz => (hmu j z hz).symm) g
  refine ⟨?_, ?_⟩
  · show ptsIntegral (mCoordIdeal D.y) (X.omN B 1 q t) (fun z => X.Cd.cuspWeight z / 2) = _
    rw [ptsIntegral_pencil hQ hα hβ _ hintU 1 (1 / (q : ℝ)) (hom q hq)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = 0
    · subst hi
      simp [hmix0]
    · simp only [hi, ↓reduceIte]
      ring
  · show geomDeg (mCoordIdeal D.y) (X.NbarQ B 1 q t) D.n / (q : ℝ) ^ D.n = _
    unfold geomDeg
    rw [ptsIntegral_pencil hQ hα hβ _ hint1 (q : ℝ) 1 (hpot q hq), Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [OmNPoly.rescale_mul_div_pow _ _ _ _ _ hq0 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
    by_cases hi0 : i = 0
    · subst hi0
      simp only [↓reduceIte, hmix0, Nat.choose_zero_right, Nat.cast_one, one_mul]
    · simp only [hi0, ↓reduceIte]

end GroundTheory.Heights₂.Heights.LowerBoundFree
