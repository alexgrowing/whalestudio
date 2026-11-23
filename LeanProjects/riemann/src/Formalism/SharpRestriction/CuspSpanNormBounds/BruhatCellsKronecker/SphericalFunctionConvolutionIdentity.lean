import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.FlagUnipotentLattices.HalfDeltaL1Bound

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory
open scoped InnerProductSpace ComplexOrder ENNReal

section Abs

theorem sesquilinear_eq_zero_of_diag {V : Type*} [AddCommGroup V] [Module ℂ V] (q : V → V → ℂ)
    (a1 : ∀ x x' y, q (x + x') y = q x y + q x' y) (s1 : ∀ (c : ℂ) x y, q (c • x) y = c * q x y)
    (a2 : ∀ x y y', q x (y + y') = q x y + q x y')
    (s2 : ∀ (c : ℂ) x y, q x (c • y) = (starRingEnd ℂ) c * q x y)
    (h0 : ∀ x, q x x = 0) (x y : V) : q x y = 0 := by
  have e1 := h0 (x + y)
  have e2 := h0 (x + Complex.I • y)
  rw [a1, a2, a2] at e1
  rw [a1, a2, a2, s1, s1, s2, s2, Complex.conj_I] at e2
  linear_combination (1 / 2 : ℂ) * e1 + (Complex.I / 2) * e2 - ((1 + Complex.I) / 2) * h0 x
    - ((1 + Complex.I) / 2) * h0 y + ((q x y - q y x + Complex.I * q y y) / 2) * Complex.I_sq

variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem unitary_rep_inner_map (σ : G →* (H →L[ℂ] H)) (hU : ∀ g x, ‖σ g x‖ = ‖x‖) (g : G) (x y : H) :
    ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ := LinearIsometry.inner_map_map ⟨(σ g).toLinearMap, hU g⟩ x y

theorem rep_mul_apply' (σ : G →* (H →L[ℂ] H)) (g h : G) (x : H) : σ (g * h) x = σ g (σ h x) := by
  rw [map_mul, ContinuousLinearMap.mul_apply]

theorem rep_one_apply' (σ : G →* (H →L[ℂ] H)) (x : H) : σ 1 x = x := by
  rw [map_one, ContinuousLinearMap.one_apply]

theorem inner_map_inv_eq (σ : G →* (H →L[ℂ] H)) (hU : ∀ g x, ‖σ g x‖ = ‖x‖) (g : G) (x y : H) :
    ⟪x, σ g⁻¹ y⟫_ℂ = ⟪σ g x, y⟫_ℂ := by
  rw [← unitary_rep_inner_map σ hU g x (σ g⁻¹ y), ← rep_mul_apply']
  simp

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

theorem sigma_finite_of_integrable_positive [μ.IsMulLeftInvariant] (f : G → ℝ) (hf : Continuous f) (hi : Integrable f μ) (h1 : 0 < f 1) :
    SigmaFinite μ := by
  have hUo : IsOpen {h : G | f 1 / 2 < f h} := isOpen_lt continuous_const hf
  have h1U : (1 : G) ∈ {h : G | f 1 / 2 < f h} := by
    show f 1 / 2 < f 1
    linarith
  have hUfin : μ {h : G | f 1 / 2 < f h} < ⊤ := by
    refine lt_of_le_of_lt (measure_mono fun h hh => ?_) (hi.measure_norm_ge_lt_top (half_pos h1))
    have hh' : f 1 / 2 < f h := hh
    show f 1 / 2 ≤ ‖f h‖
    rw [Real.norm_eq_abs]
    exact hh'.le.trans (le_abs_self _)
  haveI : IsLocallyFiniteMeasure μ := by
    refine ⟨fun g => ⟨(fun h => g⁻¹ * h) ⁻¹' {h : G | f 1 / 2 < f h}, ?_, ?_⟩⟩
    · apply (continuous_mul_left g⁻¹).continuousAt.preimage_mem_nhds
      simpa using hUo.mem_nhds h1U
    · rw [measure_preimage_mul]
      exact hUfin
  exact sigmaFinite_of_locallyFinite

theorem inv_invariant_of_bi_invariant [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure] [SigmaFinite μ]
    (f : G → ℝ) (hf : Continuous f) (hi : Integrable f μ) (h1 : 0 < f 1) : μ.IsInvInvariant := by
  have hUo : IsOpen {h : G | f 1 / 2 < f h} := isOpen_lt continuous_const hf
  have h1U : (1 : G) ∈ {h : G | f 1 / 2 < f h} := by
    show f 1 / 2 < f 1
    linarith
  have hUfin : μ {h : G | f 1 / 2 < f h} < ⊤ := by
    refine lt_of_le_of_lt (measure_mono fun h hh => ?_) (hi.measure_norm_ge_lt_top (half_pos h1))
    have hh' : f 1 / 2 < f h := hh
    show f 1 / 2 ≤ ‖f h‖
    rw [Real.norm_eq_abs]
    exact hh'.le.trans (le_abs_self _)
  have hso : IsOpen ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹) := hUo.inter hUo.inv
  have hs1 : (1 : G) ∈ {h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹ :=
    ⟨h1U, by rw [Set.mem_inv, inv_one]; exact h1U⟩
  have hsinv : ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹)⁻¹ =
      {h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹ := by
    rw [Set.inter_inv, inv_inv, Set.inter_comm]
  have hs0 : μ ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹) ≠ 0 :=
    hso.measure_ne_zero μ ⟨1, hs1⟩
  have hstop : μ ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hUfin).ne
  have key := measure_eq_div_smul μ.inv μ hs0 hstop
  rw [Measure.inv_apply, hsinv, ENNReal.div_self hs0 hstop, one_smul] at key
  exact ⟨key⟩

def SchurOrthogonalityRelation (σ : G →* (H →L[ℂ] H)) (d : ℝ) : Prop :=
  ∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d

theorem continuous_inner_rep_apply (σ : G →* (H →L[ℂ] H)) (hc : ∀ x, Continuous fun g => σ g x) (x y : H) :
    Continuous fun g => ⟪y, σ g x⟫_ℂ := continuous_const.inner (hc x)

theorem schur_product_integrable (σ : G →* (H →L[ℂ] H)) (hc : ∀ x, Continuous fun g => σ g x) (d : ℝ)
    (hS : SchurOrthogonalityRelation μ σ d) (x1 x2 y1 y2 : H) :
    Integrable (fun g => ⟪y1, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪y2, σ g x2⟫_ℂ) μ := by
  refine Integrable.mono' ((hS x1 y1).1.add (hS x2 y2).1)
    ((continuous_inner_rep_apply σ hc x1 y1).mul (Complex.continuous_conj.comp (continuous_inner_rep_apply σ hc x2 y2))).aestronglyMeasurable
    (ae_of_all _ fun g => ?_)
  show ‖⟪y1, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪y2, σ g x2⟫_ℂ‖ ≤ ‖⟪y1, σ g x1⟫_ℂ‖ ^ 2 + ‖⟪y2, σ g x2⟫_ℂ‖ ^ 2
  rw [norm_mul, RCLike.norm_conj]
  nlinarith [norm_nonneg ⟪y1, σ g x1⟫_ℂ, norm_nonneg ⟪y2, σ g x2⟫_ℂ,
    sq_nonneg (‖⟪y1, σ g x1⟫_ℂ‖ - ‖⟪y2, σ g x2⟫_ℂ‖)]

theorem schur_relation_polarized_first (σ : G →* (H →L[ℂ] H)) (hc : ∀ x, Continuous fun g => σ g x) (d : ℝ)
    (hS : SchurOrthogonalityRelation μ σ d) (y x1 x2 : H) :
    ∫ g, ⟪y, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g x2⟫_ℂ ∂μ - ⟪x2, x1⟫_ℂ * ⟪y, y⟫_ℂ / d = 0 := by
  have hI : ∀ u v : H, Integrable (fun g => ⟪y, σ g u⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g v⟫_ℂ) μ :=
    fun u v => schur_product_integrable μ σ hc d hS u v y y
  refine sesquilinear_eq_zero_of_diag (fun a b => ∫ g, ⟪y, σ g a⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g b⟫_ℂ ∂μ - ⟪b, a⟫_ℂ * ⟪y, y⟫_ℂ / d)
    ?_ ?_ ?_ ?_ ?_ x1 x2
  · intro a a' b
    have hpt : ∀ g, ⟪y, σ g (a + a')⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g b⟫_ℂ =
        ⟪y, σ g a⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g b⟫_ℂ + ⟪y, σ g a'⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g b⟫_ℂ := by
      intro g
      rw [map_add, inner_add_right, add_mul]
    simp only [hpt]
    rw [integral_add (hI a b) (hI a' b), inner_add_right]
    ring
  · intro c a b
    have hpt : ∀ g, ⟪y, σ g (c • a)⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g b⟫_ℂ =
        c * (⟪y, σ g a⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g b⟫_ℂ) := by
      intro g
      rw [map_smul, inner_smul_right, mul_assoc]
    simp only [hpt]
    rw [integral_const_mul, inner_smul_right]
    ring
  · intro a b b'
    have hpt : ∀ g, ⟪y, σ g a⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g (b + b')⟫_ℂ =
        ⟪y, σ g a⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g b⟫_ℂ + ⟪y, σ g a⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g b'⟫_ℂ := by
      intro g
      rw [map_add, inner_add_right, map_add, mul_add]
    simp only [hpt]
    rw [integral_add (hI a b) (hI a b'), inner_add_left]
    ring
  · intro c a b
    have hpt : ∀ g, ⟪y, σ g a⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g (c • b)⟫_ℂ =
        (starRingEnd ℂ) c * (⟪y, σ g a⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g b⟫_ℂ) := by
      intro g
      rw [map_smul, inner_smul_right, map_mul]
      ring
    simp only [hpt]
    rw [integral_const_mul, inner_smul_left]
    ring
  · intro a
    have hpt : ∀ g, ⟪y, σ g a⟫_ℂ * (starRingEnd ℂ) ⟪y, σ g a⟫_ℂ = ((‖⟪y, σ g a⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro g
      first
        | rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        | (rw [RCLike.mul_conj]; push_cast; rfl)
        | simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hn : ∀ v : H, ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      intro v
      first
        | exact_mod_cast inner_self_eq_norm_sq_to_K v
        | (rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl)
        | simp [inner_self_eq_norm_sq_to_K]
    simp only [hpt]
    rw [integral_complex_ofReal, (hS a y).2, hn a, hn y]
    push_cast
    ring

theorem schur_relation_polarized (σ : G →* (H →L[ℂ] H)) (hc : ∀ x, Continuous fun g => σ g x) (d : ℝ)
    (hS : SchurOrthogonalityRelation μ σ d) (x1 x2 y1 y2 : H) :
    ∫ g, ⟪y1, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪y2, σ g x2⟫_ℂ ∂μ = ⟪x2, x1⟫_ℂ * ⟪y1, y2⟫_ℂ / d := by
  have hI : ∀ u v : H, Integrable (fun g => ⟪v, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪u, σ g x2⟫_ℂ) μ :=
    fun u v => schur_product_integrable μ σ hc d hS x1 x2 v u
  refine sub_eq_zero.mp (sesquilinear_eq_zero_of_diag (fun u v => ∫ g, ⟪v, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪u, σ g x2⟫_ℂ ∂μ - ⟪x2, x1⟫_ℂ * ⟪v, u⟫_ℂ / d)
    ?_ ?_ ?_ ?_ ?_ y2 y1)
  · intro a a' b
    have hpt : ∀ g, ⟪b, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪a + a', σ g x2⟫_ℂ =
        ⟪b, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪a, σ g x2⟫_ℂ + ⟪b, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪a', σ g x2⟫_ℂ := by
      intro g
      rw [inner_add_left, map_add, mul_add]
    simp only [hpt]
    rw [integral_add (hI a b) (hI a' b), inner_add_right]
    ring
  · intro c a b
    have hpt : ∀ g, ⟪b, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪c • a, σ g x2⟫_ℂ =
        c * (⟪b, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪a, σ g x2⟫_ℂ) := by
      intro g
      rw [inner_smul_left, map_mul, Complex.conj_conj]
      ring
    simp only [hpt]
    rw [integral_const_mul, inner_smul_right]
    ring
  · intro a b b'
    have hpt : ∀ g, ⟪b + b', σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪a, σ g x2⟫_ℂ =
        ⟪b, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪a, σ g x2⟫_ℂ + ⟪b', σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪a, σ g x2⟫_ℂ := by
      intro g
      rw [inner_add_left, add_mul]
    simp only [hpt]
    rw [integral_add (hI a b) (hI a b'), inner_add_left]
    ring
  · intro c a b
    have hpt : ∀ g, ⟪c • b, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪a, σ g x2⟫_ℂ =
        (starRingEnd ℂ) c * (⟪b, σ g x1⟫_ℂ * (starRingEnd ℂ) ⟪a, σ g x2⟫_ℂ) := by
      intro g
      rw [inner_smul_left]
      ring
    simp only [hpt]
    rw [integral_const_mul, inner_smul_left]
    ring
  · intro a
    exact schur_relation_polarized_first μ σ hc d hS a x1 x2

open Formalism.MainNotions.PlaceDegreeData (phA IsOpIntA)

theorem spherical_function_apply (d : ℝ) (σ : G →* (H →L[ℂ] H)) (w : H) (g : G) :
    phA d σ w g = (d : ℂ) * (starRingEnd ℂ) ⟪w, σ g w⟫_ℂ := rfl

theorem spherical_function_continuous (d : ℝ) (σ : G →* (H →L[ℂ] H)) (hc : ∀ x, Continuous fun g => σ g x) (w : H) :
    Continuous (phA d σ w) := by
  have e : phA d σ w = fun g => (d : ℂ) * (starRingEnd ℂ) ⟪w, σ g w⟫_ℂ := funext (spherical_function_apply d σ w)
  rw [e]
  exact continuous_const.mul (Complex.continuous_conj.comp (continuous_inner_rep_apply σ hc w w))

theorem spherical_function_integrable (d : ℝ) (σ : G →* (H →L[ℂ] H)) (w : H) (hm : Integrable (fun g => ⟪w, σ g w⟫_ℂ) μ) :
    Integrable (phA d σ w) μ := by
  have e : phA d σ w = fun g => (d : ℂ) * (starRingEnd ℂ) ⟪w, σ g w⟫_ℂ := funext (spherical_function_apply d σ w)
  have h2 : Integrable (fun g => (starRingEnd ℂ) ⟪w, σ g w⟫_ℂ) μ :=
    hm.mono (Complex.continuous_conj.comp_aestronglyMeasurable hm.aestronglyMeasurable)
      (ae_of_all _ fun g => le_of_eq (RCLike.norm_conj _))
  rw [e]
  exact h2.const_mul (d : ℂ)

theorem spherical_function_star_eq (d : ℝ) (σ : G →* (H →L[ℂ] H)) (hU : ∀ g x, ‖σ g x‖ = ‖x‖) (w : H) (g : G) :
    star (phA d σ w g⁻¹) = phA d σ w g := by
  rw [spherical_function_apply, spherical_function_apply, inner_map_inv_eq σ hU g w w, ← inner_conj_symm (σ g w) w]
  first
    | simp only [star_mul', Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]
    | simp [mul_comm]

theorem spherical_function_convolution_identity (d : ℝ) (hd : 0 < d) (σ : G →* (H →L[ℂ] H)) (hU : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hc : ∀ x, Continuous fun g => σ g x) (hS : SchurOrthogonalityRelation μ σ d) (w : H) (x y : G) :
    ∫ g, phA d σ w g * phA d σ w (x⁻¹ * g⁻¹ * y) ∂μ = ⟪w, σ x w⟫_ℂ * phA d σ w y := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpt : ∀ g, phA d σ w g * phA d σ w (x⁻¹ * g⁻¹ * y) =
      (d : ℂ) ^ 2 * (⟪σ y w, σ g (σ x w)⟫_ℂ * (starRingEnd ℂ) ⟪w, σ g w⟫_ℂ) := by
    intro g
    rw [spherical_function_apply, spherical_function_apply, show x⁻¹ * g⁻¹ * y = (g * x)⁻¹ * y by group, rep_mul_apply',
      inner_map_inv_eq σ hU, rep_mul_apply', ← inner_conj_symm (σ g (σ x w)) (σ y w), Complex.conj_conj]
    ring
  simp only [hpt]
  rw [integral_const_mul, schur_relation_polarized μ σ hc d hS (σ x w) w (σ y w) w, spherical_function_apply,
    ← inner_conj_symm (σ y w) w]
  rw [mul_div_assoc', div_eq_iff hd']
  ring

variable {Hp : Type} [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]

theorem vector_valued_integrand_integrable (φ : G → ℂ) (hφc : Continuous φ) (hφi : Integrable φ μ) (π : G →* (Hp →L[ℂ] Hp))
    (hU : ∀ g x, ‖π g x‖ = ‖x‖) (hc : ∀ x, Continuous fun g => π g x) (y : Hp) :
    Integrable (fun g => φ g • π g y) μ := by
  refine Integrable.mono' (hφi.norm.mul_const ‖y‖) (hφc.smul (hc y)).aestronglyMeasurable
    (ae_of_all _ fun g => ?_)
  exact le_of_eq (by rw [norm_smul, hU])

theorem convolution_operator_exists (φ : G → ℂ) (hφc : Continuous φ) (hφi : Integrable φ μ) (π : G →* (Hp →L[ℂ] Hp))
    (hU : ∀ g x, ‖π g x‖ = ‖x‖) (hc : ∀ x, Continuous fun g => π g x) :
    ∃ P : Hp →L[ℂ] Hp, IsOpIntA μ π φ P := by
  refine ⟨LinearMap.mkContinuous
    { toFun := fun y => ∫ g, φ g • π g y ∂μ
      map_add' := fun y1 y2 => by
        simp only [map_add, smul_add]
        exact integral_add (vector_valued_integrand_integrable μ φ hφc hφi π hU hc y1) (vector_valued_integrand_integrable μ φ hφc hφi π hU hc y2)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        congr 1
        funext g
        exact smul_comm _ _ _ }
    (∫ g, ‖φ g‖ ∂μ) (fun y => ?_), hφi, fun x y => ?_⟩
  · show ‖∫ g, φ g • π g y ∂μ‖ ≤ (∫ g, ‖φ g‖ ∂μ) * ‖y‖
    calc ‖∫ g, φ g • π g y ∂μ‖ ≤ ∫ g, ‖φ g • π g y‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖φ g‖ * ‖y‖ ∂μ := by
        congr 1
        funext g
        rw [norm_smul, hU]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖y‖ := integral_mul_const _ _
  · show ⟪x, ∫ g, φ g • π g y ∂μ⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ
    rw [← integral_inner (vector_valued_integrand_integrable μ φ hφc hφi π hU hc y)]
    simp only [inner_smul_right]

theorem convolution_operator_symmetric [μ.IsInvInvariant] (φ : G → ℂ) (hA : ∀ g, star (φ g⁻¹) = φ g) (π : G →* (Hp →L[ℂ] Hp))
    (hU : ∀ g x, ‖π g x‖ = ‖x‖) (P : Hp →L[ℂ] Hp) (hP : IsOpIntA μ π φ P) (x y : Hp) :
    ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ := by
  rw [hP.2 x y, ← inner_conj_symm (P x) y, hP.2 y x, ← integral_conj,
    ← integral_inv_eq_self (fun g => φ g * ⟪x, π g y⟫_ℂ) μ]
  congr 1
  funext g
  have h1 := hA g⁻¹
  rw [inv_inv] at h1
  rw [map_mul, inner_conj_symm, ← inner_map_inv_eq π hU g x y]
  show (starRingEnd ℂ) (φ g) * ⟪x, π g⁻¹ y⟫_ℂ = φ g⁻¹ * ⟪x, π g⁻¹ y⟫_ℂ
  rw [← h1, starRingEnd_apply]

theorem matrix_coefficient_norm_le (π : G →* (Hp →L[ℂ] Hp)) (hU : ∀ g x, ‖π g x‖ = ‖x‖) (u y : Hp) (h : G) :
    ‖⟪u, π h y⟫_ℂ‖ ≤ ‖u‖ * ‖y‖ := by
  rw [← hU h y]
  exact norm_inner_le_norm u (π h y)

theorem convolution_kernel_prod_integrable [μ.IsMulLeftInvariant] [SigmaFinite μ] (φ : G → ℂ) (hφc : Continuous φ) (hφi : Integrable φ μ)
    (π : G →* (Hp →L[ℂ] Hp)) (hU : ∀ g x, ‖π g x‖ = ‖x‖) (hc : ∀ x, Continuous fun g => π g x) (x : G) (u y : Hp) :
    Integrable (Function.uncurry fun g h => φ g * φ (x⁻¹ * g⁻¹ * h) * ⟪u, π h y⟫_ℂ) (μ.prod μ) := by
  have hmp : MeasurePreserving (fun z : G × G => (z.1, z.1⁻¹ * z.2)) (μ.prod μ) (μ.prod μ) :=
    measurePreserving_prod_inv_mul (μ := μ) (ν := μ)
  have hF : Integrable (fun z : G × G => φ z.1 * φ (x⁻¹ * z.2)) (μ.prod μ) :=
    hφi.mul_prod (hφi.comp_mul_left x⁻¹)
  have hF2 : Integrable (fun z : G × G => φ z.1 * φ (x⁻¹ * (z.1⁻¹ * z.2))) (μ.prod μ) :=
    (hmp.integrable_comp hF.aestronglyMeasurable).2 hF
  have h1 : Continuous fun z : G × G => φ z.1 := hφc.comp continuous_fst
  have h2' : Continuous fun z : G × G => x⁻¹ * z.1⁻¹ * z.2 := by fun_prop
  have h2 : Continuous fun z : G × G => φ (x⁻¹ * z.1⁻¹ * z.2) := hφc.comp h2'
  have h3 : Continuous fun z : G × G => π z.2 y := (hc y).comp continuous_snd
  have h4 : Continuous fun z : G × G => ⟪u, π z.2 y⟫_ℂ := continuous_const.inner h3
  have h5 : Continuous fun z : G × G => φ z.1 * φ (x⁻¹ * z.1⁻¹ * z.2) * ⟪u, π z.2 y⟫_ℂ :=
    (h1.mul h2).mul h4
  refine Integrable.mono' (hF2.norm.mul_const (‖u‖ * ‖y‖)) h5.aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  show ‖φ z.1 * φ (x⁻¹ * z.1⁻¹ * z.2) * ⟪u, π z.2 y⟫_ℂ‖ ≤ ‖φ z.1 * φ (x⁻¹ * (z.1⁻¹ * z.2))‖ * (‖u‖ * ‖y‖)
  rw [norm_mul (φ z.1 * φ (x⁻¹ * z.1⁻¹ * z.2)), mul_assoc x⁻¹]
  exact mul_le_mul_of_nonneg_left (matrix_coefficient_norm_le π hU u y z.2) (norm_nonneg _)

theorem convolution_operator_sandwich_eq [μ.IsMulLeftInvariant] [SigmaFinite μ] (φ : G → ℂ) (hφc : Continuous φ) (hφi : Integrable φ μ)
    (m : G → ℂ) (hB : ∀ x y : G, ∫ g, φ g * φ (x⁻¹ * g⁻¹ * y) ∂μ = m x * φ y)
    (π : G →* (Hp →L[ℂ] Hp)) (hU : ∀ g x, ‖π g x‖ = ‖x‖) (hc : ∀ x, Continuous fun g => π g x)
    (P : Hp →L[ℂ] Hp) (hP : IsOpIntA μ π φ P) (x : G) : P ∘L π x ∘L P = m x • P := by
  have hinv : ∀ (k : G) (a b : Hp), ⟪π k⁻¹ a, b⟫_ℂ = ⟪a, π k b⟫_ℂ := fun k a b => by
    rw [← inner_map_inv_eq π hU, inv_inv]
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun u => ?_
  have step : ∀ h : G, ⟪u, π h (π x (P y))⟫_ℂ = ∫ g, φ (x⁻¹ * h⁻¹ * g) * ⟪u, π g y⟫_ℂ ∂μ := by
    intro h
    rw [← rep_mul_apply', ← hinv, hP.2]
    calc ∫ g, φ g * ⟪π (h * x)⁻¹ u, π g y⟫_ℂ ∂μ
        = ∫ g, (fun g' => φ (x⁻¹ * h⁻¹ * g') * ⟪u, π g' y⟫_ℂ) (h * x * g) ∂μ := by
          congr 1
          funext g
          simp only [hinv, ← rep_mul_apply']
          rw [show x⁻¹ * h⁻¹ * (h * x * g) = g by group]
      _ = ∫ g, φ (x⁻¹ * h⁻¹ * g) * ⟪u, π g y⟫_ℂ ∂μ :=
          integral_mul_left_eq_self (fun g' => φ (x⁻¹ * h⁻¹ * g') * ⟪u, π g' y⟫_ℂ) (h * x)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    inner_smul_right, hP.2 u (π x (P y)), hP.2 u y]
  calc ∫ h, φ h * ⟪u, π h (π x (P y))⟫_ℂ ∂μ
      = ∫ h, ∫ g, φ h * φ (x⁻¹ * h⁻¹ * g) * ⟪u, π g y⟫_ℂ ∂μ ∂μ := by
        congr 1
        funext h
        rw [step h, ← integral_const_mul]
        congr 1
        funext g
        ring
    _ = ∫ g, ∫ h, φ h * φ (x⁻¹ * h⁻¹ * g) * ⟪u, π g y⟫_ℂ ∂μ ∂μ :=
        integral_integral_swap (convolution_kernel_prod_integrable μ φ hφc hφi π hU hc x u y)
    _ = ∫ g, m x * (φ g * ⟪u, π g y⟫_ℂ) ∂μ := by
        congr 1
        funext g
        rw [integral_mul_const, hB x g]
        ring
    _ = m x * ∫ g, φ g * ⟪u, π g y⟫_ℂ ∂μ := integral_const_mul _ _

theorem cyclic_of_schur_relation [CompleteSpace H] (d : ℝ) (hd : 0 < d) (σ : G →* (H →L[ℂ] H)) (hS : SchurOrthogonalityRelation μ σ d) (w : H)
    (hw : ‖w‖ = 1) : (Submodule.span ℂ (Set.range fun g => σ g w)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro v hv
  have h0 : ∀ g, ⟪v, σ g w⟫_ℂ = 0 := by
    intro g
    first
      | exact (Submodule.mem_orthogonal' _ _).mp hv _ (Submodule.subset_span ⟨g, rfl⟩)
      | exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp hv _ (Submodule.subset_span ⟨g, rfl⟩))
  have h2 := (hS w v).2
  have h3 : ∫ g, ‖⟪v, σ g w⟫_ℂ‖ ^ 2 ∂μ = 0 := by simp [h0]
  rw [h3, hw, one_pow, one_mul] at h2
  have h4 : ‖v‖ ^ 2 = 0 := by
    rcases div_eq_zero_iff.mp h2.symm with h | h
    · exact h
    · exact absurd h hd.ne'
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h4)

end Abs

private theorem exists_linearIsometry_intertwining_of_cyclic {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Hp : Type} [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]
    (σ : G →* (H →L[ℂ] H)) (π : G →* (Hp →L[ℂ] Hp)) (w : H) (v : Hp)
    (hcyc : (Submodule.span ℂ (Set.range fun g => σ g w)).topologicalClosure = ⊤)
    (hcoef : ∀ g h : G, ⟪π g v, π h v⟫_ℂ = ⟪σ g w, σ h w⟫_ℂ) :
    ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u) := by
  classical
  let A : (G →₀ ℂ) →ₗ[ℂ] H := Finsupp.linearCombination ℂ (fun g => σ g w)
  let B : (G →₀ ℂ) →ₗ[ℂ] Hp := Finsupp.linearCombination ℂ (fun g => π g v)
  have hAB : ∀ c c' : G →₀ ℂ, ⟪B c, B c'⟫_ℂ = ⟪A c, A c'⟫_ℂ := by
    intro c c'
    simp only [A, B, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hcoef]
  have hnorm : ∀ c, ‖B c‖ = ‖A c‖ := by
    intro c
    have h := congrArg RCLike.re (hAB c c)
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]
  let f0 : LinearMap.range A →ₗ[ℂ] Hp :=
    (LinearMap.ker A).liftQ B hker ∘ₗ A.quotKerEquivRange.symm.toLinearMap
  have hf0 : ∀ c, f0 ⟨A c, LinearMap.mem_range_self A c⟩ = B c := by
    intro c
    simp only [f0, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hf0n : ∀ y : LinearMap.range A, ‖f0 y‖ = ‖y‖ := by
    rintro ⟨y, c, rfl⟩
    rw [hf0, hnorm]
    rfl
  let f1 : LinearMap.range A →L[ℂ] Hp := LinearMap.mkContinuous f0 1 (fun y => by rw [hf0n, one_mul])
  let e : LinearMap.range A →L[ℂ] H := (LinearMap.range A).subtypeL
  have hdense : DenseRange e := by
    intro x
    have h1 : LinearMap.range A = Submodule.span ℂ (Set.range fun g => σ g w) :=
      Finsupp.range_linearCombination ℂ
    have hx : x ∈ ((LinearMap.range A).topologicalClosure : Set H) := by
      rw [h1, hcyc]
      exact Submodule.mem_top
    rw [Submodule.topologicalClosure_coe] at hx
    refine closure_mono ?_ hx
    intro y hy
    exact ⟨⟨y, hy⟩, rfl⟩
  have hui : IsUniformInducing e := isometry_subtype_coe.isUniformInducing
  let io0 : H →L[ℂ] Hp := f1.extend e
  have hio0 : ∀ c, io0 (A c) = B c := by
    intro c
    have h := ContinuousLinearMap.extend_eq f1 hdense hui ⟨A c, LinearMap.mem_range_self A c⟩
    exact h.trans (hf0 c)
  have hiso : ∀ u, ‖io0 u‖ = ‖u‖ := by
    intro u
    refine hdense.induction_on u (isClosed_eq io0.continuous.norm continuous_norm) ?_
    rintro ⟨y, c, rfl⟩
    show ‖io0 (A c)‖ = ‖A c‖
    rw [hio0, hnorm]
  have hA1 : A (Finsupp.single 1 1) = w := by
    simp [A, rep_one_apply']
  have hB1 : B (Finsupp.single 1 1) = v := by
    simp [B, rep_one_apply']
  have hAg : ∀ (g : G) c, σ g (A c) = A (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    have e1 : Finsupp.linearCombination ℂ (fun h => σ h w) (Finsupp.mapDomain (g * ·) c) =
        Finsupp.linearCombination ℂ ((fun h => σ h w) ∘ (g * ·)) c := by
      rw [Finsupp.linearCombination_mapDomain]
    show σ g (Finsupp.linearCombination ℂ (fun h => σ h w) c) =
      Finsupp.linearCombination ℂ (fun h => σ h w) (Finsupp.mapDomain (g * ·) c)
    rw [e1, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
    simp only [map_smul, Function.comp_apply, rep_mul_apply']
  have hBg : ∀ (g : G) c, π g (B c) = B (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    have e1 : Finsupp.linearCombination ℂ (fun h => π h v) (Finsupp.mapDomain (g * ·) c) =
        Finsupp.linearCombination ℂ ((fun h => π h v) ∘ (g * ·)) c := by
      rw [Finsupp.linearCombination_mapDomain]
    show π g (Finsupp.linearCombination ℂ (fun h => π h v) c) =
      Finsupp.linearCombination ℂ (fun h => π h v) (Finsupp.mapDomain (g * ·) c)
    rw [e1, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
    simp only [map_smul, Function.comp_apply, rep_mul_apply']
  refine ⟨⟨io0.toLinearMap, hiso⟩, ?_, ?_⟩
  · show io0 w = v
    rw [← hA1, hio0, hB1]
  · intro g u
    show io0 (σ g u) = π g (io0 u)
    refine hdense.induction_on u (isClosed_eq (io0.continuous.comp (σ g).continuous)
      ((π g).continuous.comp io0.continuous)) ?_
    rintro ⟨y, c, rfl⟩
    show io0 (σ g (A c)) = π g (io0 (A c))
    rw [hAg, hio0, hio0, hBg]

theorem abstract_projector_statements_hold (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.PlaceDegreeData.AbstractGroupProjectorExists D := by
  intro G _ _ _ _ _ _ μ _ _ H _ _ _ σ hU hc d hd hS w hw hm
  have hS' : SchurOrthogonalityRelation μ σ d := hS
  have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have hfc : Continuous fun g => ‖⟪w, σ g w⟫_ℂ‖ ^ 2 := (continuous_inner_rep_apply σ hc w w).norm.pow 2
  have hf1 : (0 : ℝ) < ‖⟪w, σ 1 w⟫_ℂ‖ ^ 2 := by rw [rep_one_apply', hww]; simp
  have : SigmaFinite μ := sigma_finite_of_integrable_positive μ _ hfc (hS w w).1 hf1
  have : μ.IsInvInvariant := inv_invariant_of_bi_invariant μ _ hfc (hS w w).1 hf1
  have hφc := spherical_function_continuous d σ hc w
  have hφi := spherical_function_integrable μ d σ w hm
  have hA := spherical_function_star_eq d σ hU w
  have hB := spherical_function_convolution_identity μ d hd σ hU hc hS' w
  have hcyc := cyclic_of_schur_relation μ d hd σ hS' w hw
  refine ⟨hA, hB, ?_⟩
  intro Hp _ _ _ π hUp hcp
  refine ⟨convolution_operator_exists μ _ hφc hφi π hUp hcp, fun P hP => ?_⟩
  have hsym := convolution_operator_symmetric μ _ hA π hUp P hP
  have hPxP := convolution_operator_sandwich_eq μ _ hφc hφi (fun x => ⟪w, σ x w⟫_ℂ) hB π hUp hcp P hP
  have hidem : ∀ y, P (P y) = P y := by
    intro y
    have h1 := DFunLike.congr_fun (hPxP 1) y
    simp only [ContinuousLinearMap.comp_apply, rep_one_apply', hww, one_smul] at h1
    exact h1
  have hfix : ∀ v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp), P v = v := by
    rintro _ ⟨y, rfl⟩
    exact hidem y
  have key : ∀ v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp), ‖v‖ = 1 →
      (∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) ∧
      ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u) := by
    intro v hv hn
    have hco : ∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ :=
      Formalism.HermitianLatticeCounting.Final.S7.projCoeff G Hp (fun g => π g) P (fun x => ⟪w, σ x w⟫_ℂ) hsym hPxP v (hfix v hv) hn
    obtain ⟨J, hJ1, hJ2, _⟩ := Formalism.HermitianLatticeCounting.Final.S7.coeffIso G Hp H π σ hUp hU v w hco hcyc
    exact ⟨hco, J, hJ1, hJ2⟩
  refine ⟨⟨?_, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 hsym⟩, hPxP, key, ?_⟩
  · ext y
    exact hidem y
  · ext v
    constructor
    · intro hv
      by_cases h0 : v = 0
      · exact ⟨0, fun g => by simp, by simp [h0]⟩
      · have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 h0)
        have hv' : ((‖v‖ : ℂ)⁻¹) • v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp) := Submodule.smul_mem _ _ hv
        have hn' : ‖((‖v‖ : ℂ)⁻¹) • v‖ = 1 := by
          rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
        obtain ⟨_, J, hJ1, hJ2⟩ := key _ hv' hn'
        refine ⟨(‖v‖ : ℂ) • J.toContinuousLinearMap, fun g => ?_, ?_⟩
        · ext u
          show (‖v‖ : ℂ) • J (σ g u) = π g ((‖v‖ : ℂ) • J u)
          rw [hJ2, map_smul]
        · show v = (‖v‖ : ℂ) • J w
          rw [hJ1, smul_smul, mul_inv_cancel₀ hn, one_smul]
    · rintro ⟨io, hio, rfl⟩
      refine ⟨io w, ?_⟩
      show P (io w) = io w
      refine ext_inner_left ℂ fun x => ?_
      rw [hP.2]
      have e : (fun g => Formalism.MainNotions.PlaceDegreeData.phA d σ w g * ⟪x, π g (io w)⟫_ℂ) =
          fun g => (d : ℂ) * (⟪ContinuousLinearMap.adjoint io x, σ g w⟫_ℂ * (starRingEnd ℂ) ⟪w, σ g w⟫_ℂ) := by
        funext g
        have h1 : π g (io w) = io (σ g w) := (DFunLike.congr_fun (hio g) w).symm
        rw [h1, ContinuousLinearMap.adjoint_inner_left, spherical_function_apply]
        ring
      rw [e, integral_const_mul, schur_relation_polarized μ σ hc d hS', hww, ContinuousLinearMap.adjoint_inner_left]
      have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp

theorem abstract_projector_statement_of_proof (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.PlaceDegreeData.AbstractGroupProjectorForDatum D := abstract_projector_statements_hold D

theorem family_abstract_projector_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Formalism.MainNotions.PlaceDegreeData.FamilyAbstractProjectorEveryMember Fm := by
  unfold Formalism.MainNotions.PlaceDegreeData.FamilyAbstractProjectorEveryMember
  intro x i
  exact abstract_projector_statements_hold _

theorem family_abstract_projector_statement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Formalism.MainNotions.PlaceDegreeData.FamilyAbstractProjector Fm := family_abstract_projector_holds Fm

end Formalism.MainNotions.BridgeLemma

end
