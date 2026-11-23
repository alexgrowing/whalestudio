import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticVectorExponentialSeriesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorsInvariantSubspaceStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVectorStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditiveStatement
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.CommutatorAdjointHolds

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff NNReal ENNReal
open Topology Filter

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.AnalyticWords

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local notation "Jε" => ReciprocityTheory.ChartRestriction.DS.Jm

def projJ (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℝ) • (Y - Jε ε * Yᴴ * Jε ε)

theorem Jm_herm (ε : Fin n → Bool) : (Jε ε)ᴴ = Jε ε := by
  simp only [ReciprocityTheory.ChartRestriction.DS.Jm, diagonal_conjTranspose]
  congr 1; funext a; by_cases h : ε a <;> simp [h]

theorem inG_projJ (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : ReciprocityTheory.ChartRestriction.DS.inG ε (projJ ε Y) := by
  have hJ : Jε ε * Jε ε = 1 := CompanionTheory.D.gk.HC.Jm_sq_A
  show (projJ ε Y)ᴴ * Jε ε + Jε ε * projJ ε Y = 0
  have e : (projJ ε Y)ᴴ = (1 / 2 : ℝ) • (Yᴴ - Jε ε * Y * Jε ε) := by
    simp only [projJ, conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, Jm_herm, conjTranspose_conjTranspose,
      star_trivial, Matrix.mul_assoc]
  have e1 : Jε ε * Y * Jε ε * Jε ε = Jε ε * Y := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
  have e2 : Jε ε * (Jε ε * Yᴴ * Jε ε) = Yᴴ * Jε ε := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  rw [e, projJ, smul_mul_assoc, mul_smul_comm, Matrix.sub_mul, Matrix.mul_sub, e1, e2, ← smul_add]
  simp

theorem projJ_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : ReciprocityTheory.ChartRestriction.DS.inG ε X) :
    projJ ε X = X := by
  have hJ : Jε ε * Jε ε = 1 := CompanionTheory.D.gk.HC.Jm_sq_A
  have h : Xᴴ * Jε ε + Jε ε * X = 0 := hX
  have h1 : Xᴴ * Jε ε = -(Jε ε * X) := eq_neg_of_add_eq_zero_left h
  have h2 : Jε ε * Xᴴ * Jε ε = -X := by
    rw [Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  rw [projJ, h2, sub_neg_eq_add, ← two_smul ℝ X, smul_smul]
  norm_num

def projL (ε : Fin n → Bool) : (Fin n → Fin n → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun Y := projJ ε (Matrix.of Y)
  map_add' Y Z := by
    have e : (Matrix.of (Y + Z) : Matrix (Fin n) (Fin n) ℂ) = Matrix.of Y + Matrix.of Z := rfl
    simp only [projJ, e, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
    module
  map_smul' r Y := by
    have e : (Matrix.of (r • Y) : Matrix (Fin n) (Fin n) ℂ) = r • Matrix.of Y := rfl
    simp only [projJ, e, conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc, RingHom.id_apply]
    module

theorem mnorm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem mnorm_of_le (Y : Fin n → Fin n → ℂ) : mnorm (Matrix.of Y) ≤ (n : ℝ) ^ 2 * ‖Y‖ := by
  calc mnorm (Matrix.of Y) ≤ ∑ _a : Fin n, ∑ _b : Fin n, ‖Y‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          (norm_le_pi_norm (Y a) b).trans (norm_le_pi_norm Y a)
    _ = _ := by simp; ring

theorem mnorm_projL_le (ε : Fin n → Bool) (Y : Fin n → Fin n → ℂ) : mnorm (projL ε Y) ≤ (n : ℝ) ^ 2 * ‖Y‖ := by
  have hentry : ∀ a b, ‖projL ε Y a b‖ ≤ ‖Y‖ := fun a b => by
    have h1 : ‖Y a b‖ ≤ ‖Y‖ := (norm_le_pi_norm (Y a) b).trans (norm_le_pi_norm Y a)
    have h2 : ‖Y b a‖ ≤ ‖Y‖ := (norm_le_pi_norm (Y b) a).trans (norm_le_pi_norm Y b)
    have hs : ∀ a : Fin n, ‖(if ε a = true then (1 : ℂ) else -1)‖ = 1 := fun a => by by_cases h : ε a <;> simp [h]
    have e : projL ε Y a b = (1 / 2 : ℝ) • (Y a b - (if ε a = true then (1 : ℂ) else -1) * star (Y b a) *
        (if ε b = true then (1 : ℂ) else -1)) := by
      show projJ ε (Matrix.of Y) a b = _
      simp only [projJ, ReciprocityTheory.ChartRestriction.DS.Jm, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_diagonal,
        Matrix.diagonal_mul, conjTranspose_apply, Matrix.of_apply]
    rw [e, norm_smul]
    have h3 : ‖Y a b - (if ε a = true then (1 : ℂ) else -1) * star (Y b a) *
        (if ε b = true then (1 : ℂ) else -1)‖ ≤ ‖Y a b‖ + ‖Y b a‖ := by
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      rw [norm_mul, norm_mul, hs, hs, norm_star]; ring
    have h4 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [h4]
    linarith
  calc mnorm (projL ε Y) ≤ ∑ _a : Fin n, ∑ _b : Fin n, ‖Y‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hentry a b
    _ = _ := by simp; ring

theorem lieOf_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : ReciprocityTheory.ChartRestriction.DS.inG ε X) :
    X ∈ HCSS.lieOf (UJset ε) := fun t => ReciprocityTheory.ChartRestriction.DS.exp_smul_mem_UJset hX t

section Smooth

variable {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def smoothSub (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) : Submodule ℝ H where
  carrier := {v | IsSmoothVec G π v}
  add_mem' := fun {a b} ha hb => (GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep).1 a b ha hb
  zero_mem' := ⟨fun _ => 0, contDiff_const, fun z _ => map_zero _⟩
  smul_mem' := fun r x hx => by
    have h := (GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep).2.1 (r : ℂ) x hx
    rwa [Complex.coe_smul] at h

theorem dRep_smul (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (r : ℝ) : dRep π (r • X) v = r • dRep π X v := by
  have h := (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hv hX).1
  have h2 : HasDerivAt (fun t : ℝ => r * t) r 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
  have h3 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) (r * 0) := by simpa using h
  have h4 := h3.scomp 0 h2
  have e : ((fun t : ℝ => π (NormedSpace.exp (t • X)) v) ∘ fun t : ℝ => r * t) =
      fun t : ℝ => π (NormedSpace.exp (t • r • X)) v := by
    funext t
    simp only [Function.comp_apply, smul_smul, mul_comm]
  rw [e] at h4
  exact h4.deriv

def actX (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) : Module.End ℝ (smoothSub hG hrep) where
  toFun x := ⟨dRep π X x, (GlobalTheory.T.derived_action_of_smooth_vector hG hrep x.2 hX).2⟩
  map_add' x y := Subtype.ext (GlobalTheory.T.derived_action_additive hG hrep x.2 y.2 hX hX).2.1
  map_smul' r x := Subtype.ext (by
    have h := (GlobalTheory.T.derived_action_additive hG hrep x.2 x.2 hX hX).2.2 (r : ℂ)
    simp only [Complex.coe_smul] at h
    exact h)

end Smooth

section Series

variable {ε : Fin n → Bool} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem projL_mem (ε : Fin n → Bool) (Y : Fin n → Fin n → ℂ) : projL ε Y ∈ HCSS.lieOf (UJset ε) :=
  lieOf_of_inG (inG_projJ ε _)

def act (hG : IsLinRed (UJset ε)) (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) :
    (Fin n → Fin n → ℂ) →ₗ[ℝ] Module.End ℝ (smoothSub hG hrep) where
  toFun Y := actX hG hrep (projL_mem ε Y)
  map_add' Y Z := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show dRep π (projL ε (Y + Z)) x = dRep π (projL ε Y) x + dRep π (projL ε Z) x
    rw [map_add]
    exact (GlobalTheory.T.derived_action_additive hG hrep x.2 x.2 (projL_mem ε Y) (projL_mem ε Z)).1
  map_smul' r Y := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show dRep π (projL ε (r • Y)) x = r • dRep π (projL ε Y) x
    rw [map_smul]
    exact dRep_smul hG hrep x.2 (projL_mem ε Y) r

theorem word_eq (hG : IsLinRed (UJset ε)) (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π)
    (l : List (Fin n → Fin n → ℂ)) (x : smoothSub hG hrep) :
    (((l.map (act hG hrep)).prod x : smoothSub hG hrep) : H) = (l.map (projL ε)).foldr (dRep π) (x : H) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, Module.End.mul_apply]
    rw [← ih]
    rfl

theorem foldr_replicate_eq {α : Type*} (f : α → H → H) (X : α) (m : ℕ) (x : H) :
    (List.replicate m X).foldr f x = (f X)^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']

theorem exists_series [CompleteSpace H] (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π)
    (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε)) {v : H} (hs : IsSmoothVec (UJset ε) π v)
    (hw : WordBound (UJset ε) π v) :
    ∃ Φ : (Fin n → Fin n → ℂ) → H, AnalyticAt ℝ Φ 0 ∧
      ∀ᶠ Y in 𝓝 (0 : Fin n → Fin n → ℂ), ReciprocityTheory.ChartRestriction.DS.inG ε (Matrix.of Y) →
        Φ Y = π (NormedSpace.exp (Matrix.of Y)) v := by
  have hG : IsLinRed (UJset ε) := GlobalTheory.HCUnitary.isLinRed_UJset ε
  obtain ⟨r₀, hr₀, hsum⟩ := GlobalTheory.T.analytic_vector_exponential_series hG hrep hc hs hw
  obtain ⟨C, hC, hb⟩ := hw
  let v' : smoothSub hG hrep := ⟨v, hs⟩
  let ev : Module.End ℝ (smoothSub hG hrep) →ₗ[ℝ] H := (smoothSub hG hrep).subtype ∘ₗ LinearMap.applyₗ v'
  let q : ∀ m : ℕ, MultilinearMap ℝ (fun _ : Fin m => Fin n → Fin n → ℂ) H := fun m =>
    ((m.factorial : ℝ)⁻¹) • ev.compMultilinearMap
      ((MultilinearMap.mkPiAlgebraFin ℝ m (Module.End ℝ (smoothSub hG hrep))).compLinearMap fun _ => act hG hrep)
  have hq : ∀ m (Y : Fin m → Fin n → Fin n → ℂ), q m Y =
      ((m.factorial : ℝ)⁻¹) • (List.ofFn fun i => projL ε (Y i)).foldr (dRep π) v := fun m Y => by
    have h := word_eq hG hrep (List.ofFn Y) v'
    simp only [List.map_ofFn] at h
    simp only [q, MultilinearMap.smul_apply, LinearMap.compMultilinearMap_apply,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply]
    congr 1
  have hqb : ∀ m (Y : Fin m → Fin n → Fin n → ℂ), ‖q m Y‖ ≤ C ^ (m + 1) * ((n : ℝ) ^ 2) ^ m * ∏ i, ‖Y i‖ := by
    intro m Y
    have hmem : ∀ X ∈ List.ofFn (fun i => projL ε (Y i)), X ∈ HCSS.lieOf (UJset ε) := fun X hX => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hX
      exact projL_mem ε _
    have h := hb _ hmem
    rw [List.length_ofFn, List.map_ofFn, List.prod_ofFn] at h
    have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
    rw [hq, norm_smul, norm_inv, Real.norm_natCast, inv_mul_le_iff₀ hf]
    refine h.trans ?_
    have h2 : ∏ i, (mnorm ∘ fun i => projL ε (Y i)) i ≤ ((n : ℝ) ^ 2) ^ m * ∏ i, ‖Y i‖ := by
      refine (Finset.prod_le_prod (fun i _ => mnorm_nonneg _) fun i _ => mnorm_projL_le ε (Y i)).trans (le_of_eq ?_)
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq (by ring))
  let p : FormalMultilinearSeries ℝ (Fin n → Fin n → ℂ) H := fun m => (q m).mkContinuous _ (hqb m)
  let r : ℝ≥0 := ⟨(C * ((n : ℝ) ^ 2 + 1))⁻¹, by positivity⟩
  have hr : (r : ℝ) = (C * ((n : ℝ) ^ 2 + 1))⁻¹ := rfl
  have hrad : (r : ℝ≥0∞) ≤ p.radius := p.le_radius_of_bound C fun m => by
    refine (mul_le_mul_of_nonneg_right ((q m).mkContinuous_norm_le (by positivity) (hqb m)) (by positivity)).trans ?_
    have h1 : C * (n : ℝ) ^ 2 * r ≤ 1 := by
      rw [hr, ← div_eq_mul_inv, div_le_one (by positivity)]
      nlinarith
    calc C ^ (m + 1) * ((n : ℝ) ^ 2) ^ m * (r : ℝ) ^ m = C * (C * (n : ℝ) ^ 2 * r) ^ m := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) h1) hC.le
      _ = C := mul_one C
  have hpos : 0 < p.radius := lt_of_lt_of_le (by
    rw [ENNReal.coe_pos, ← NNReal.coe_pos, hr]; positivity) hrad
  have hP := (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  refine ⟨p.sum, hP.analyticAt, ?_⟩
  have hn1 : (0 : ℝ) < (n : ℝ) ^ 2 + 1 := by positivity
  filter_upwards [hP.eventually_hasSum, Metric.ball_mem_nhds 0 (show (0 : ℝ) < r₀ / ((n : ℝ) ^ 2 + 1) by positivity)]
    with Y hY hYr hGY
  rw [mem_ball_zero_iff, lt_div_iff₀ hn1] at hYr
  have hlt : mnorm (Matrix.of Y) < r₀ := by
    have h1 := mnorm_of_le Y
    nlinarith [norm_nonneg Y]
  have hs2 := hsum _ (lieOf_of_inG hGY) hlt
  rw [zero_add] at hY
  refine hY.unique ?_
  convert hs2 using 2 with m
  have hPY : projL ε Y = Matrix.of Y := projJ_of_inG hGY
  show q m _ = _
  rw [hq, List.ofFn_const, hPY, foldr_replicate_eq, ← Complex.coe_smul]
  push_cast
  rfl

theorem analytic_orbit [CompleteSpace H] (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π)
    (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε)) {v : H} (hs : IsSmoothVec (UJset ε) π v)
    (hw : WordBound (UJset ε) π v) : GlobalTheory.Published.AnalyticOnUJ ε fun g => π g v := by
  intro g₀ hg₀
  obtain ⟨Φ, hΦ, hΦe⟩ := exists_series hrep hc hs hw
  obtain ⟨L, hL, hL0, hLe⟩ := CompanionTheory.D.gk.HC.exists_logG_A ε
  have hJ : Jε ε * Jε ε = 1 := CompanionTheory.D.gk.HC.Jm_sq_A
  have hg : g₀ᴴ * Jε ε * g₀ = Jε ε := hg₀
  set h : Matrix (Fin n) (Fin n) ℂ := Jε ε * g₀ᴴ * Jε ε with hh
  have h1 : h * g₀ = 1 := by
    rw [hh, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g₀ᴴ, hg, hJ]
  have h2 : g₀ * h = 1 := mul_eq_one_comm.1 h1
  have hU : h ∈ UJset ε := by
    show hᴴ * Jε ε * h = Jε ε
    have e : hᴴ = Jε ε * g₀ * Jε ε := by
      rw [hh, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_herm, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    rw [e, Matrix.mul_assoc _ (Jε ε) (Jε ε), hJ, Matrix.mul_one, Matrix.mul_assoc, h2, Matrix.mul_one]
  let T₀ : (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun z => Matrix.of.symm (h * Matrix.of z)
      map_add' := fun a b => congrArg Matrix.of.symm (Matrix.mul_add h (Matrix.of a) (Matrix.of b))
      map_smul' := fun c a => congrArg Matrix.of.symm (Matrix.mul_smul h c (Matrix.of a)) }
  let T := LinearMap.toContinuousLinearMap T₀
  have hT : T (Matrix.of.symm g₀) = Matrix.of.symm 1 := congrArg Matrix.of.symm h1
  have aL : AnalyticAt ℝ (fun z => L (T z)) (Matrix.of.symm g₀) :=
    AnalyticAt.comp (g := L) (f := T) (hT ▸ hL) (T.analyticAt _)
  have aF : AnalyticAt ℝ (fun z => π g₀ (Φ (L (T z)))) (Matrix.of.symm g₀) :=
    (((π g₀).restrictScalars ℝ).analyticAt _).comp
      (AnalyticAt.comp (g := Φ) (f := fun z => L (T z)) (by rw [hT, hL0]; exact hΦ) aL)
  have t1 : Tendsto T (𝓝 (Matrix.of.symm g₀)) (𝓝 (Matrix.of.symm 1)) := hT ▸ T.continuous.tendsto _
  have t2 : Tendsto (fun z => L (T z)) (𝓝 (Matrix.of.symm g₀)) (𝓝 0) := by
    have := aL.continuousAt.tendsto
    rwa [hT, hL0] at this
  obtain ⟨U, hUp, hUo, hU0⟩ := eventually_nhds_iff.1
    (aF.eventually_analyticAt.and ((t1.eventually hLe).and (t2.eventually hΦe)))
  refine ⟨U, _, hUo, hU0, fun z hz => (hUp z hz).1, fun z hz hzU => ?_⟩
  obtain ⟨-, ⟨e1, e2⟩, e3⟩ := hUp z hz
  have hm : Matrix.of (T z) ∈ UJset ε := CompanionTheory.D.gk.HC.UJset_mul_mem hU hzU
  show π (Matrix.of z) v = π g₀ (Φ (L (T z)))
  rw [e3 (e2 hm), e1, ← ContinuousLinearMap.comp_apply, ← hrep.2 _ hg₀ _ hm]
  congr 2
  show Matrix.of z = g₀ * (h * Matrix.of z)
  rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

end Series

theorem analyticOnUJ_of_wordBound {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε)) {v : H}
    (hs : IsSmoothVec (UJset ε) π v) (hw : WordBound (UJset ε) π v) (w : H) :
    GlobalTheory.Published.AnalyticOnUJ ε fun g => ⟪w, π g v⟫_ℂ :=
  (analytic_orbit hrep hc hs hw).clm ((innerSL ℂ w).restrictScalars ℝ)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.AnalyticWords

end
