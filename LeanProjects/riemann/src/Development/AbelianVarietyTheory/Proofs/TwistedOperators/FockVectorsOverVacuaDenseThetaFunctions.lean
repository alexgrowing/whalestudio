import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LowVanishFockOfLowVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivCompress
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeisenbergSmoothVectorDerivativeCalculus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormCreationAnnihilationWordLeNumberOperatorPowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylNumberOperatorCommutationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowSubCreationVacuumFockBoundStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroAtOneOfIteratedDerivsVanishOfGrowthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumProjectorRangeAnnihilatedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEuclideanCoordsHermitianCartanInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFramesStatement

noncomputable section

namespace GlobalTheory.FockDensity

section Abstract

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size
open scoped RealInnerProductSpace Real ENNReal

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Φ : B →L[ℂ] H}
  {S : Submodule ℂ B}

set_option linter.unusedSectionVars false

theorem hasDerivAt_line (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (w : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ρ (s • w) f) (ρ (t • w) (dH ρ w f)) t := by
  have h0 : omJ J (t • w) w = 0 := by
    have := omJ_skew hJ w w
    have e : omJ J (t • w) w = t * omJ J w w := by simp [omJ, real_inner_smul_left]
    rw [e, show omJ J w w = 0 by linarith, mul_zero]
  have h2 : HasDerivAt (fun s : ℝ => s • w) w t := by simpa using (hasDerivAt_id t).smul_const w
  rw [VacBd.heis_dH h hf, h0]
  simpa [Function.comp_def] using (ContDiff.differentiable hf (by simp) (t • w)).hasFDerivAt.comp_hasDerivAt t h2

theorem inner_dH (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) (h : IsHeis (omJ J) ρ) {x y : B} (hx : Sm ρ x) (hy : Sm ρ y) (v : V) :
    inner ℂ (Φ (dH ρ v x)) (Φ y) = -inner ℂ (Φ x) (Φ (dH ρ v y)) := by
  have h1 := (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v hx)
  have h2 := (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v hy)
  have h3 := h1.inner ℂ h2
  simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars', Osc.inner_heis hΦ, zero_smul, h.1] at h3
  have := h3.unique (hasDerivAt_const _ _)
  linear_combination this

def dE (hS : ∀ f ∈ S, Sm ρ f) (hD : ∀ v, ∀ f ∈ S, dH ρ v f ∈ S) (v : V) : Module.End ℂ S where
  toFun f := ⟨dH ρ v f, hD v f f.2⟩
  map_add' f g := Subtype.ext (dH_add v (hS _ f.2) (hS _ g.2))
  map_smul' a f := Subtype.ext (dH_smul v a (hS _ f.2))

variable (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖)
  (hS : ∀ f ∈ S, Sm ρ f) (hD : ∀ v, ∀ f ∈ S, dH ρ v f ∈ S)

variable (J) in

def cE (z : V) : Module.End ℂ S := dE hS hD z - I • dE hS hD (J z)

variable (J) in

def aE (z : V) : Module.End ℂ S := -(dE hS hD z + I • dE hS hD (J z))

theorem coe_cE (z : V) (x : S) : (cE J hS hD z x : B) = dH ρ z x - I • dH ρ (J z) x := rfl

theorem aE_eq_zero (z : V) (x : S) : aE J hS hD z x = 0 ↔ dH ρ z x + I • dH ρ (J z) x = 0 :=
  Subtype.ext_iff.trans (neg_eq_zero (a := dH ρ z x + I • dH ρ (J z) x))

include hJ h in
theorem relations {κ : Type} [Fintype κ] (e : OrthonormalBasis κ ℝ V) (N : Module.End ℂ S)
    (hN : N = ∑ j, cE J hS hD (e j) * aE J hS hD (e j)) :
    (∀ z, aE J hS hD z * cE J hS hD z - cE J hS hD z * aE J hS hD z = ((4 * π * ‖z‖ ^ 2 : ℝ) : ℂ) • 1) ∧
      (∀ z, N * cE J hS hD z = cE J hS hD z * (N + ((8 * π : ℝ) : ℂ) • 1)) ∧
      (∀ z, N * aE J hS hD z = aE J hS hD z * (N - ((8 * π : ℝ) : ℂ) • 1)) ∧
      ∀ z, dE hS hD z ∈ Submodule.span ℂ (Set.range (fun j => aE J hS hD (e j)) ∪ Set.range fun j => cE J hS hD (e j)) := by
  refine GlobalTheory.T.weyl_number_operator_commutation_alt V _ κ J e (dE hS hD) (aE J hS hD) (cE J hS hD) N hJ
    (fun u v => LinearMap.ext fun f => Subtype.ext (dH_add_left ρ u v f.1))
    (fun r v => LinearMap.ext fun f => Subtype.ext ((dH_smul_left ρ r v f.1).trans (Complex.coe_smul r _).symm))
    (fun u v => LinearMap.ext fun f => Subtype.ext ?_) (fun _ => rfl) (fun _ => rfl) hN
  let om : V →L[ℝ] V →L[ℝ] ℝ := ((innerSL ℝ).comp (J : V →L[ℝ] V)).flip
  have e1 : ∀ x y, om x y = omJ J x y := fun x y => real_inner_comm _ _
  have h0 : ∀ x, om x x = 0 := fun x => by
    have := omJ_skew hJ x x
    rw [e1]; linarith
  have h' : IsHeis (fun x y => om x y) ρ := by simpa only [e1] using h
  have := (DCalc.dH_calculus V B om ρ h0 h' f.1 (hS _ f.2)).2.2.2.2 u v
  rw [e1] at this
  exact this

include h hΦ in
theorem adjoint (z : V) (x y : S) :
    inner ℂ (Φ (cE J hS hD z x)) (Φ y) = inner ℂ (Φ x) (Φ (aE J hS hD z y)) := by
  change inner ℂ (Φ (dH ρ z x - I • dH ρ (J z) x)) _ = inner ℂ _ (Φ (-(dH ρ z y + I • dH ρ (J z) y)))
  simp only [map_sub, map_neg, map_add, map_smul, inner_sub_left, inner_neg_right, inner_add_right, inner_smul_left,
    inner_smul_right, inner_dH hΦ h (hS _ x.2) (hS _ y.2), conj_I]
  ring

include hJ h hΦ in

theorem inner_translate (K : Submodule ℂ S) (hK : ∀ z, ∀ x ∈ K, cE J hS hD z x ∈ K) {v : S} (hv : v ∈ K)
    (ha : ∀ z, aE J hS hD z v = 0) {y : H} (hy : ∀ x ∈ K, inner ℂ y (Φ x) = 0) (w : V) :
    inner ℂ y (Φ (ρ w v)) = 0 := by
  have e : (1 / 2 : ℂ) • cE J hS hD w - (1 / 2 : ℂ) • aE J hS hD w = dE hS hD w := by
    unfold cE aE; module
  obtain ⟨h1, h2⟩ := GlobalTheory.T.pow_sub_creation_vacuum_fock_bound S H ((Φ : B →ₗ[ℂ] H) ∘ₗ S.subtype) ((1 / 2 : ℂ) • aE J hS hD w)
    ((1 / 2 : ℂ) • cE J hS hD w) (π * ‖w‖ ^ 2) v (by positivity)
    (fun x x' => by
      have := adjoint h hΦ hS hD w x x'
      simp only [LinearMap.smul_apply, map_smul, inner_smul_left, inner_smul_right]
      change _ * inner ℂ (Φ _) (Φ _) = _ * inner ℂ (Φ _) (Φ _)
      simp only [Submodule.subtype_apply, this]
      simp [map_ofNat])
    (by
      have := (relations hJ h hS hD (stdOrthonormalBasis ℝ V) _ rfl).1 w
      simp only [smul_mul_smul_comm, ← smul_sub, this, smul_smul]
      congr 1
      push_cast
      ring)
    (by rw [LinearMap.smul_apply, ha, smul_zero])
  rw [e] at h1 h2
  have h3 := h1 K hv fun x hx => K.smul_mem _ (hK w x hx)
  have := GlobalTheory.T.eq_zero_at_one_of_iteratedDerivs_vanish_of_growth (fun k t => inner ℂ y (Φ (ρ (t • w) ((dE hS hD w ^ k) v)))) (2 * (π * ‖w‖ ^ 2))
    (‖y‖ ^ 2 * ‖Φ v‖ ^ 2) (fun k t => ?_) (fun k => ?_) fun k t => ?_
  · simpa using this
  · have := (((innerSL ℂ y).comp Φ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_line hJ h (hS _ ((dE hS hD w ^ k) v).2) w t)
    rw [pow_succ']
    exact this
  · simp only [zero_smul, h.1]
    exact hy _ (h3 k)
  · calc _ ≤ (‖y‖ * ‖Φ ((dE hS hD w ^ k) v)‖) ^ 2 := by
          gcongr
          exact (norm_inner_le_norm _ _).trans_eq (by rw [hΦ])
      _ ≤ _ := by
          rw [mul_pow, mul_assoc, mul_assoc, ← mul_assoc (‖Φ v‖ ^ 2)]
          exact mul_le_mul_of_nonneg_left (h2 k) (by positivity)

include hJ hΦ in

theorem dense_zero (hρ : ∀ w, ∀ f ∈ S, ρ w f ∈ S) (hP : ∀ f ∈ S, proj h f ∈ S) (K : Submodule ℂ S)
    (hK : ∀ z, ∀ x ∈ K, cE J hS hD z x ∈ K) (hK0 : ∀ v, (∀ z, aE J hS hD z v = 0) → v ∈ K) (f : S) {δ : ℝ}
    (hδ : 0 < δ) : ∃ g ∈ K, ‖Φ (f - g)‖ < δ := by
  let K' := K.map ((Φ : B →ₗ[ℂ] H) ∘ₗ S.subtype)
  have hf : Φ f ∈ K'.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro y hy
    have g := Osc.good_of_sm hJ h (hS _ f.2)
    have e := ((innerSL ℂ y).comp Φ).integral_comp_comm (Osc.intw_integrable h (Osc.proj_proj hJ h) g)
    rw [g.inversion hJ] at e
    refine e.symm.trans (integral_eq_zero_of_ae (Filter.Eventually.of_forall fun w => ?_))
    let v : S := ⟨proj h (ρ (-w) f), hP _ (hρ _ _ f.2)⟩
    have ha : ∀ z, aE J hS hD z v = 0 := fun z =>
      (aE_eq_zero hS hD z v).2 (GlobalTheory.T.vacuumProjector_range_annihilated V B J ρ hJ h _ z)
    exact inner_translate hJ h hΦ hS hD K hK (hK0 v ha) ha
      (fun x hx => (Submodule.mem_orthogonal' _ _).1 hy _ ⟨x, hx, rfl⟩) w
  obtain ⟨_, ⟨g, hg, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 hf δ hδ
  exact ⟨g, hg, by rwa [map_sub, ← dist_eq_norm]⟩

theorem exists_preimage {T : Type} [AddCommGroup T] [Module ℂ T] (M : Module.End ℂ T) {r : ℝ} (hr : 0 < r)
    (p : T → Prop) (n : ℕ) : ∀ g ∈ Submodule.span ℂ {g | p g ∧ ∃ n : ℕ, M g = (((n + 1) * r : ℝ) : ℂ) • g},
      ∃ g' ∈ Submodule.span ℂ {g | p g ∧ ∃ n : ℕ, M g = (((n + 1) * r : ℝ) : ℂ) • g}, (M ^ n) g' = g := by
  set K := Submodule.span ℂ {g | p g ∧ ∃ n : ℕ, M g = (((n + 1) * r : ℝ) : ℂ) • g}
  have k1 : ∀ g ∈ K, ∃ g' ∈ K, M g' = g := fun g hg => by
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨n, hn⟩ := hg.2
      have : (((n + 1) * r : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by positivity)
      exact ⟨_, K.smul_mem (((n + 1) * r : ℝ) : ℂ)⁻¹ (Submodule.subset_span hg), by
        rw [map_smul, hn, smul_smul, inv_mul_cancel₀ this, one_smul]⟩
    | zero => exact ⟨0, K.zero_mem, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', a, rfl⟩ := hx
      obtain ⟨y', b, rfl⟩ := hy
      exact ⟨x' + y', K.add_mem a b, map_add _ _ _⟩
    | smul a x _ hx =>
      obtain ⟨x', b, rfl⟩ := hx
      exact ⟨a • x', K.smul_mem a b, map_smul _ _ _⟩
  induction n with
  | zero => exact fun g hg => ⟨g, hg, rfl⟩
  | succ n ih =>
    intro g hg
    obtain ⟨g₁, a, rfl⟩ := ih g hg
    obtain ⟨g₂, b, rfl⟩ := k1 g₁ a
    exact ⟨g₂, b, by rw [pow_succ, Module.End.mul_apply]⟩

theorem wordSum_le {X Y ι : Type} [Fintype ι] (A : ι → X → X) (p : X → ℝ≥0∞) (j : Y → X) (q : Y → ℝ≥0∞) (d : ℕ)
    (hc : ∀ l : List ι, l.length ≤ d → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ y, p (wordAct A l (j y)) ≤ C * q y) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ y, wordSum A p d (j y) ≤ C * q y := by
  choose! C hC hC' using hc
  have e : ∀ k ∈ Finset.range (d + 1), ∀ a : Fin k → ι, (List.ofFn a).length ≤ d := fun k hk a => by
    simpa using Nat.le_of_lt_succ (Finset.mem_range.1 hk)
  refine ⟨∑ k ∈ Finset.range (d + 1), ∑ a : Fin k → ι, C (List.ofFn a),
    ENNReal.sum_ne_top.2 fun k hk => ENNReal.sum_ne_top.2 fun a _ => hC _ (e k hk a), fun y => ?_⟩
  simp only [wordSum, Finset.sum_mul]
  exact Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun a _ => hC' _ (e k hk a) y

include hJ h hΦ in

theorem exists_number {ι : Type} [Fintype ι] (u : ι → V) (d : ℕ) : ∃ M : Module.End ℂ S,
    (∀ v, (∀ z, aE J hS hD z v = 0) → M v = ((8 * π : ℝ) : ℂ) • v) ∧
    (∀ z, M * cE J hS hD z = cE J hS hD z * (M + ((8 * π : ℝ) : ℂ) • 1)) ∧
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x : S, wordSum (fun i => dH ρ (u i)) (fun x => ‖Φ x‖ₑ) d x ≤ C * ‖Φ ((M ^ d) x)‖ₑ := by
  let e := stdOrthonormalBasis ℝ V
  obtain ⟨N, hN⟩ : ∃ N, N = ∑ j, cE J hS hD (e j) * aE J hS hD (e j) := ⟨_, rfl⟩
  obtain ⟨r1, r2, r3, r4⟩ := relations hJ h hS hD e N hN
  obtain ⟨M, hM⟩ : ∃ M : Module.End ℂ S, M = N + ((8 * π : ℝ) : ℂ) • 1 := ⟨_, rfl⟩
  have m2 : ∀ z, M * cE J hS hD z = cE J hS hD z * (M + ((8 * π : ℝ) : ℂ) • 1) := fun z => by
    rw [hM, add_mul, r2, mul_add _ (N + _), smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have m3 : ∀ z, M * aE J hS hD z = aE J hS hD z * (M - ((8 * π : ℝ) : ℂ) • 1) := fun z => by
    rw [hM, add_mul, r3, add_sub_cancel_right, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, sub_add_cancel]
  have hb := GlobalTheory.T.norm_creationAnnihilation_word_le_numberOperator_pow S H _ ((Φ : B →ₗ[ℂ] H) ∘ₗ S.subtype) (fun j => aE J hS hD (e j)) (fun j => cE J hS hD (e j)) M
    (8 * π) (4 * π) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_pos]) (fun j => adjoint h hΦ hS hD _)
    (fun j => by rw [r1, e.orthonormal.1 j, one_pow, mul_one]) (by rw [hM, hN]) (fun j => m3 _) fun j => m2 _
  have hw : ∀ (l : List ι) (x : S), ((l.map fun i => dE hS hD (u i)).prod x : B) =
      wordAct (fun i => dH ρ (u i)) l x := fun l x => by
    induction l with
    | nil => rfl
    | cons i l ih => rw [wordAct_cons, ← ih, List.map_cons, List.prod_cons, Module.End.mul_apply]; rfl
  refine ⟨M, fun v hv => by simp [hM, hN, hv], m2, wordSum_le _ _ _ _ d fun l hl => ?_⟩
  obtain ⟨C, hC⟩ := hb (l.map fun i => dE hS hD (u i)) d
    (fun X hX => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 hX; exact r4 _) (by simpa using hl)
  refine ⟨ENNReal.ofReal (max C 0), ENNReal.ofReal_ne_top, fun x => ?_⟩
  rw [← hw, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (le_max_right _ _)]
  exact ENNReal.ofReal_le_ofReal ((hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))

include hJ hΦ hS hD in

theorem dense_words (hρ : ∀ w, ∀ f ∈ S, ρ w f ∈ S) (hP : ∀ f ∈ S, proj h f ∈ S) (F : Submodule ℂ B)
    (hF0 : ∀ f ∈ S, (∀ z, dH ρ z f + I • dH ρ (J z) f = 0) → f ∈ F)
    (hF : ∀ z, ∀ f ∈ S, f ∈ F → dH ρ z f - I • dH ρ (J z) f ∈ F) {ι : Type} [Fintype ι] (u : ι → V) (d : ℕ)
    {f : B} (hf : f ∈ S) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ g ∈ F, g ∈ S ∧ wordSum (fun i => dH ρ (u i)) (fun x => ‖Φ x‖ₑ) d (f - g) < δ := by
  obtain ⟨M, m1, m2, C, c0, c1⟩ := exists_number hJ h hΦ hS hD u d
  have k2 := exists_preimage M (r := 8 * π) (by positivity) (fun g => g.1 ∈ F) d
  generalize hK : Submodule.span ℂ {g : S | g.1 ∈ F ∧ ∃ n : ℕ, M g = (((n + 1) * (8 * π) : ℝ) : ℂ) • g} = K at k2
  have k3 : K ≤ F.comap S.subtype := hK ▸ Submodule.span_le.2 fun g hg => hg.1
  have k4 : ∀ z, K ≤ K.comap (cE J hS hD z) := fun z => by
    subst hK
    refine Submodule.span_le.2 fun g hg => Submodule.mem_comap.2 (Submodule.subset_span ?_)
    obtain ⟨n, hn⟩ := hg.2
    refine ⟨by rw [coe_cE]; exact hF z _ g.2 hg.1, n + 1, ?_⟩
    rw [← Module.End.mul_apply, m2, Module.End.mul_apply, LinearMap.add_apply, hn, LinearMap.smul_apply,
      Module.End.one_apply, ← add_smul, map_smul]
    congr 1
    push_cast
    ring
  have k5 : ∀ v, (∀ z, aE J hS hD z v = 0) → v ∈ K := fun v hv =>
    hK ▸ Submodule.subset_span ⟨hF0 _ v.2 fun z => (aE_eq_zero hS hD z v).1 (hv z), 0, by
      rw [m1 v hv, Nat.cast_zero, zero_add, one_mul]⟩
  obtain ⟨ε, hε, hε'⟩ := ENNReal.exists_nnreal_pos_mul_lt c0 hδ.ne'
  obtain ⟨g, hg, hd⟩ := dense_zero hJ h hΦ hS hD hρ hP K (fun z x hx => k4 z hx) k5 ((M ^ d) ⟨f, hf⟩) (δ := ε) hε
  obtain ⟨g', hg', rfl⟩ := k2 g hg
  have c2 := c1 (⟨f, hf⟩ - g')
  rw [map_sub (M ^ d), Submodule.coe_sub, Submodule.coe_sub, mul_comm] at c2
  refine ⟨g', k3 hg', g'.2, c2.trans_lt (lt_of_le_of_lt ?_ hε')⟩
  refine mul_le_mul_left ?_ _
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hd.le

include hJ in

theorem dense_transport {V' : Type} [NormedAddCommGroup V'] [NormedSpace ℝ V'] (E : V ≃L[ℝ] V') {J' : V' → V'}
    (hE : ∀ x, E (J x) = J' (E x)) {ρ : V' → B →L[ℂ] B} (hρ : IsHeis (omJ J) fun v => ρ (E v))
    (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) {Y : Type} (T : Y → B →L[ℂ] B) (hT : ∀ y v f, T y (ρ v f) = ρ v (T y f))
    (F : Submodule ℂ B) (hS : ∀ f, f ∈ S ↔ Sm ρ f ∧ ∀ y, T y f = f)
    (hF0 : ∀ f ∈ S, (∀ z, dH ρ z f + I • dH ρ (J' z) f = 0) → f ∈ F)
    (hF : ∀ z, ∀ f ∈ S, f ∈ F → dH ρ z f - I • dH ρ (J' z) f ∈ F) {ι : Type} [Fintype ι] (u : ι → V') (d : ℕ)
    {f : B} (hf : f ∈ S) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ g ∈ F, g ∈ S ∧ wordSum (fun i => dH ρ (u i)) (fun x => ‖Φ x‖ₑ) d (f - g) < δ := by
  have hm : ∀ G, G ∈ S ↔ Sm (fun v => ρ (E v)) G ∧ ∀ y, T y G = G :=
    fun G => (hS G).trans (and_congr_left' (UnitaryOsc.sm_comp_iff E _ G).symm)
  have hd : ∀ z, dH (fun v => ρ (E v)) z = dH ρ (E z) := fun z => funext fun G => by
    have := E.comp_right_fderiv (f := fun v => ρ v G) (x := 0)
    rw [map_zero] at this
    exact DFunLike.congr_fun this z
  have a1 : ∀ G ∈ S, Sm (fun v => ρ (E v)) G := fun G hG => ((hm G).1 hG).1
  have a2 : ∀ v, ∀ G ∈ S, dH (fun v => ρ (E v)) v G ∈ S := fun v G hG =>
    (hm _).2 ⟨VacBd.sm_dH hρ (a1 G hG) v, fun y => by
      rw [← (dH_comm (T y) (fun v => hT y (E v)) (a1 G hG)).2, ((hm G).1 hG).2]⟩
  have a3 : ∀ w, ∀ G ∈ S, ρ (E w) G ∈ S := fun w G hG =>
    (hm _).2 ⟨Osc.sm_heis hρ w (a1 G hG), fun y => by rw [hT, ((hm G).1 hG).2]⟩
  have a4 : ∀ G ∈ S, proj hρ G ∈ S := fun G hG => (hm _).2 ⟨(Osc.good_proj hJ hρ G).sm hJ, fun y => by
    rw [Osc.proj_comm hρ _ (fun v => hT y (E v)), ((hm G).1 hG).2]⟩
  have := dense_words hJ hρ (fun v => hΦ (E v)) a1 a2 a3 a4 F
    (fun G hG hv => hF0 G hG fun z => by simpa only [hd, hE, E.apply_symm_apply] using hv (E.symm z))
    (fun z G hG hG' => by simpa only [hd, hE] using hF (E z) G hG hG') (fun i => E.symm (u i)) d hf hδ
  simpa only [hd, E.apply_symm_apply] using this

end Abstract

section Coord

open Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size
open scoped ENNReal ComplexOrder

theorem dense_coord {κ : Type} [Fintype κ] [DecidableEq κ] {Q s : Matrix κ κ ℂ} (hQ : Qᴴ = Q) (hs : s * s = 1)
    (hp : (Q * s).PosDef) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {ρ : (κ → ℂ) → B →L[ℂ] B} (h : IsHeis (fun x y => (star y ⬝ᵥ Q *ᵥ x).im) ρ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : B →L[ℂ] H) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) {Y : Type}
    (T : Y → B →L[ℂ] B) (hT : ∀ y v f, T y (ρ v f) = ρ v (T y f)) (S F : Submodule ℂ B)
    (hS : ∀ f, f ∈ S ↔ Sm ρ f ∧ ∀ y, T y f = f)
    (hF0 : ∀ f ∈ S, (∀ z, dH ρ z f + I • dH ρ (I • s *ᵥ z) f = 0) → f ∈ F)
    (hF : ∀ z, ∀ f ∈ S, f ∈ F → dH ρ z f - I • dH ρ (I • s *ᵥ z) f ∈ F) {ι : Type} [Fintype ι] (u : ι → κ → ℂ) (d : ℕ)
    {f : B} (hf : f ∈ S) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ g ∈ F, g ∈ S ∧ wordSum (fun i => dH ρ (u i)) (fun x => ‖Φ x‖ₑ) d (f - g) < δ := by
  obtain ⟨E, J, hJ, hE, hom⟩ := GlobalTheory.T.exists_euclideanCoords_hermitian_cartanInvolution κ Q s hQ hs hp
  have hρ : IsHeis (omJ J) fun v => ρ (E v) :=
    UnitaryOsc.isHeis_comp h (E : EuclideanSpace ℂ κ →L[ℝ] (κ → ℂ)) fun x y => hom x y
  exact dense_transport hJ E (J' := fun z => I • s *ᵥ z) hE hρ hΦ T hT F hS hF0 hF u d hf hδ

end Coord

section Theta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis
open scoped ENNReal Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}

def coeL (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : BB ψ V W →ₗ[ℂ] (WO V W → ℂ) where
  toFun G := G.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def atPl (τ : D.what₂.Tau) (y : Matrix (Fin W.rank) (Fin V.rank) ℂ) : Ix V W → ℂ := vecL (Pi.single τ y : RW W V)

theorem sum_atPl (x : Ix V W → ℂ) : x = ∑ τ, atPl τ (cpt x τ) := by
  unfold atPl
  rw [← map_sum]
  exact (congrArg vecL (Finset.univ_sum_single (unvecL x))).symm

theorem cpt_cplx (sS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (x : Ix V W → ℂ) (τ : D.what₂.Tau) :
    cpt (Complex.I • blk sT sS *ᵥ x) τ = cplxO (sS τ) (sT τ) (cpt x τ) := by
  unfold cplxO
  rw [← cpt_blk]
  rfl

theorem cplx_atPl (sS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (τ : D.what₂.Tau) (y : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    Complex.I • blk sT sS *ᵥ atPl τ y = atPl τ (cplxO (sS τ) (sT τ) y) := by
  have e : ∀ y τ', cpt (atPl (V := V) (W := W) τ y) τ' =
      (Pi.single τ y : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) τ' := fun _ _ => rfl
  funext p
  have : cpt (Complex.I • blk sT sS *ᵥ atPl τ y) p.2 = cpt (atPl τ (cplxO (sS τ) (sT τ) y)) p.2 := by
    rw [cpt_cplx, e, e]
    by_cases h : p.2 = τ
    · rw [h, Pi.single_eq_same, Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne h, cplxO]
  exact congrFun (congrFun this p.1.1) p.1.2

variable (h : Chart θ σ) (hψ : IsStdChar D ψ (-1))
include h

theorem coe_dH_atPl {G : BB ψ V W} (hG : GlobalTheory.RealWeil.Sm (rhoV hψ σ V W) G) (τ : D.what₂.Tau)
    (y : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    coeL ψ V W (dH (rhoV hψ σ V W) (atPl τ y) G) = Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y (coeL ψ V W G) := by
  funext w
  refine (ev_fderiv hψ G hG (atPl τ y) w).trans ?_
  have e : ∀ t : ℝ, iotaV σ V W (t • atPl τ y) = lineAt θ τ y t := fun t => by
    rw [GlobalTheory.VacUnique.Ann.lineAt_eq h V W τ y t]
    rfl
  simp only [e]
  rfl

theorem coe_dH {G : BB ψ V W} (hG : GlobalTheory.RealWeil.Sm (rhoV hψ σ V W) G) (x : Ix V W → ℂ) :
    coeL ψ V W (dH (rhoV hψ σ V W) x G) = ∑ τ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (cpt x τ) (coeL ψ V W G) := by
  have e : dH (rhoV hψ σ V W) x G = ∑ τ, dH (rhoV hψ σ V W) (atPl τ (cpt x τ)) G :=
    (congrArg (fderiv ℝ (fun u => rhoV hψ σ V W u G) 0) (sum_atPl x)).trans (map_sum _ _ _)
  simp only [e, map_sum, coe_dH_atPl h hψ hG]

theorem mem_level {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W))) (G : BB ψ V W) :
    G ∈ (thetaLevel ψ V W U).comap (coeL ψ V W) ↔ GlobalTheory.RealWeil.Sm (rhoV hψ σ V W) G ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → rhoB hψ u G = G := by
  refine ⟨fun hG => ⟨sm_of_theta h hψ G hG.1, fun u hu h0 => QB_ext fun x => ?_⟩, fun hG => ?_⟩
  · rw [coe_rhoB]
    exact congrFun (hG.2 u hu h0) x
  · have e : ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W u G.1 = G.1 := fun u hu h0 => by
      rw [← coe_rhoB hψ, hG.2 u hu h0]
    exact ⟨theta_of_sm h hψ G hG.1 ⟨U, hU, e⟩, e⟩

include hψ in

theorem crea_mem (A : Fr V) (B : Fr W) (U : AddSubgroup (WO V W)) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) {g : WO V W → ℂ} (hg : g ∈ fockSpan ψ θ A B U) :
    crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) z g ∈ fockSpan ψ θ A B U := by
  suffices H : IsThetaFunO ψ V W g ∧ crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) z g ∈ fockSpan ψ θ A B U from H.2
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨f, P, h1, h2, rfl⟩ := hg
    obtain ⟨Q, hQ⟩ := GlobalTheory.T.fockCreation_preserves_fockVectors_two_frames D V W A B θ ψ hψ h.inf f h1.1 τ z P
    exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ h.inf _ _ _ _ h1.1 P, Submodule.subset_span ⟨f, Q, h1, h2, hQ⟩⟩
  | zero =>
    have e := fun y => GlobalTheory.FockIndep.dRho_smul hψ h.inf τ y 0 (theta_zero (ψ := ψ) (S := V) (T := W))
    simp only [zero_smul] at e
    exact ⟨theta_zero, by simp only [crea, e, smul_zero, sub_zero, zero_mem]⟩
  | add x y _ _ hx hy =>
    refine ⟨theta_add hx.1 hy.1, ?_⟩
    convert add_mem hx.2 hy.2 using 1
    simp only [crea, fun z => GlobalTheory.FockIndep.dRho_add hψ h.inf τ z hx.1 hy.1]
    module
  | smul a x _ hx =>
    refine ⟨theta_smul a hx.1, ?_⟩
    convert Submodule.smul_mem _ a hx.2 using 1
    simp only [crea, fun z => GlobalTheory.FockIndep.dRho_smul hψ h.inf τ z a hx.1]
    module

theorem dense_vec (A : Fr V) (B : Fr W) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : BB ψ V W →L[ℂ] H)
    (hΦ : ∀ w G, ‖Φ (rhoB hψ w G)‖ = ‖Φ G‖) {ι : Type} [Fintype ι] (u : ι → Ix V W → ℂ) (d : ℕ) {f : BB ψ V W}
    (hf : f ∈ (thetaLevel ψ V W U).comap (coeL ψ V W)) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ g ∈ (fockSpan ψ θ A B U).comap (coeL ψ V W), g ∈ (thetaLevel ψ V W U).comap (coeL ψ V W) ∧
      wordSum (fun i => dH (rhoV hψ σ V W) (u i)) (fun x => ‖Φ x‖ₑ) d (f - g) < δ := by
  have hc := HM_cartan (Model.isCartanInv_cart A) (Model.isCartanInv_cart B)
  refine dense_coord HM_herm hc.1 hc.2 (isHeis_rhoB h hψ) Φ (fun v => hΦ _)
    (fun u : {u : WO V W // u ∈ U ∧ u.map (infPart D) = 0} => rhoB hψ u.1) (fun u => rhoB_comm h hψ u.2.2) _ _
    (fun G => (mem_level h hψ hU G).trans
      (and_congr_right' ⟨fun a u => a u.1 u.2.1 u.2.2, fun a u h1 h2 => a ⟨u, h1, h2⟩⟩))
    (fun G hG hv => ?_) (fun z G hG hF => ?_) u d hf hδ
  · have hs := ((mem_level h hψ hU G).1 hG).1
    refine Submodule.subset_span ⟨coeL ψ V W G, 1, ⟨hG.1, fun τ y => ?_⟩, hG, (GlobalTheory.FockIndep.pure_one _).symm⟩
    have := congrArg (coeL ψ V W) (hv (atPl τ y))
    rwa [cplx_atPl, map_add, map_smul, coe_dH_atPl h hψ hs, coe_dH_atPl h hψ hs, map_zero] at this
  · have hs := ((mem_level h hψ hU G).1 hG).1
    rw [Submodule.mem_comap, map_sub, map_smul, coe_dH h hψ hs, coe_dH h hψ hs, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    refine sum_mem fun τ _ => ?_
    rw [cpt_cplx]
    exact crea_mem h hψ A B U τ _ hF

theorem coe_word {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool)) {G : BB ψ V W}
    (hG : G ∈ (thetaLevel ψ V W U).comap (coeL ψ V W)) :
    wordAct (heisDer ψ θ) l (coeL ψ V W G) = coeL ψ V W (wordAct (fun a => dH (rhoV hψ σ V W)
      (atPl a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)))) l G) := by
  refine (wordAct_rel (R := fun x y => IsThetaFunO ψ V W x ∧ x = coeL ψ V W y) l ?_ ⟨hG.1, rfl⟩).2
  rintro a - _ y ⟨h1, rfl⟩
  exact ⟨theta_dRho h.inf hψ _ _ h1, (coe_dH_atPl h hψ (sm_of_theta h hψ y h1) _ _).symm⟩

omit h

theorem fockDense : ∀ D : D7, GlobalTheory.ChainFr.FockDense D := by
  intro D V W A B θ ψ hψ hθ μ 𝓕 hm f hf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨U, hU, hl⟩ := hf.level
  refine ⟨U, hU, ⟨hf, hl⟩, fun d δ hδ => ?_⟩
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL ψ V W (toB hψ f hf) = f := coe_toB hψ f hf
  have hF : toB hψ f hf ∈ (thetaLevel ψ V W U).comap (coeL ψ V W) := by
    rw [Submodule.mem_comap, e0]
    exact ⟨hf, hl⟩
  obtain ⟨g, h1, h2, h3⟩ := dense_vec h hψ A B hU (toL2 _ _ (μ.restrict 𝓕))
    (fun v G => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ μ 𝓕 hm.1 hm.2.1 _ G)
    (fun a : D.what₂.Tau × Fin W.rank × Fin V.rank × Bool =>
      atPl a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) d hF hδ
  refine ⟨coeL ψ V W g, h1, h2, lt_of_eq_of_lt ?_ h3⟩
  have e1 : ∀ G : BB ψ V W, l2O μ 𝓕 (coeL ψ V W G) = ‖toL2 _ _ (μ.restrict 𝓕) G‖ₑ := fun G =>
    (eLpNorm_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 (μ.restrict 𝓕) ℂ G.1)).symm.trans (Lp.enorm_def _).symm
  have e2 : f - coeL ψ V W g = coeL ψ V W (toB hψ f hf - g) := by rw [LinearMap.map_sub, e0]
  simp only [sobO, wordSum, e2, coe_word h hψ hU _ (sub_mem hF h2), e1]

end Theta

end GlobalTheory.FockDensity

end
