import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HoweSpanFamiliesOfPlacesStatement
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJAvg

theorem eval_bounded_on_box {σ : Type} (p : MvPolynomial σ ℂ) (M : σ → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : σ → ℂ, (∀ v, ‖x v‖ ≤ M v) → ‖eval x p‖ ≤ B := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, norm_nonneg _, fun x _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨B1, h1, hB1⟩ := hp; obtain ⟨B2, h2, hB2⟩ := hq
    exact ⟨B1 + B2, by positivity, fun x hx => by
      rw [map_add]; exact (norm_add_le _ _).trans (add_le_add (hB1 x hx) (hB2 x hx))⟩
  | mul_X p n hp =>
    obtain ⟨B, h0, hB⟩ := hp
    refine ⟨B * max (M n) 0, by positivity, fun x hx => ?_⟩
    rw [map_mul, eval_X, norm_mul]
    exact mul_le_mul (hB x hx) ((hx n).trans (le_max_left _ _)) (norm_nonneg _) h0

def univSubst {ι : Type} [Fintype ι] {a b : ℕ} (P : FP ι a b) :
    MvPolynomial (ι × Fin b × Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
  aeval (fun v => ∑ j, C (X (v.1, v.2.2, j)) * X (v.1, v.2.1, j)) P

theorem mvZ_one_eq_map_univSubst {ι : Type} [Fintype ι] {a b : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : FP ι a b) :
    mvZ g (fun _ => 1) P = map (eval fun w => g w.1 w.2.1 w.2.2) (univSubst P) := by
  have : (mvZ g (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) : FP ι a b →ₐ[ℂ] FP ι a b) =
      (MvPolynomial.mapAlgHom (aeval fun w : ι × Fin a × Fin a => g w.1 w.2.1 w.2.2)).comp
        (aeval (fun v => ∑ j, C (X (v.1, v.2.2, j)) * X (v.1, v.2.1, j))) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [mvZ, aeval_X, AlgHom.comp_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      apply_ite C, C_0, map_sum, map_mul, mapAlgHom_apply, map_C, map_X]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq', coe_aeval_eq_eval]
  have h := DFunLike.congr_fun this P
  rw [h]; rfl

theorem linear_eq_sum_coeff {σ : Type} (Λ : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (S : Finset (σ →₀ ℕ)) (p : MvPolynomial σ ℂ)
    (hp : p.support ⊆ S) : Λ p = ∑ m ∈ S, coeff m p * Λ (monomial m 1) := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum, Finset.sum_subset hp]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [show monomial m (coeff m p) = coeff m p • monomial m (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  · intro m _ hm
    simp [notMem_support_iff.mp hm]

section
variable {ι : Type} [Fintype ι] {a : ℕ} {K : Type} [Group K] [TopologicalSpace K]
  {r : K → ι → Matrix (Fin a) (Fin a) ℂ}

theorem ontoUni_one (hr : OntoUni r) (τ : ι) : r 1 τ = 1 := by
  have hm : r 1 τ * r 1 τ = r 1 τ := by rw [← hr.mul, one_mul]
  have hu : star (r 1 τ) * r 1 τ = 1 := (Matrix.mem_unitaryGroup_iff'.mp (hr.uni 1 τ))
  calc r 1 τ = (star (r 1 τ) * r 1 τ) * r 1 τ := by rw [hu, one_mul]
    _ = star (r 1 τ) * (r 1 τ * r 1 τ) := by rw [mul_assoc]
    _ = 1 := by rw [hm, hu]

theorem ontoUni_inv (hr : OntoUni r) (k : K) (τ : ι) : (r k τ)⁻¹ = r k⁻¹ τ :=
  Matrix.inv_eq_left_inv (by rw [← hr.mul, inv_mul_cancel, ontoUni_one hr])

theorem integrable_avg_term [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (hr : OntoUni r) (p : MvPolynomial (ι × Fin a × Fin a) ℂ) (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Integrable (fun k => eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) p * evalAt (fun τ => r k τ * y τ) F) ν := by
  simp only [evalAt]
  have hc : Continuous (fun k => eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) p *
      eval (fun x => (r k x.1 * y x.1) x.2.1 x.2.2) F) := by
    apply Continuous.mul
    · exact (MvPolynomial.continuous_eval p).comp (continuous_pi fun w =>
        (((continuous_apply w.1).comp (hr.cont.comp continuous_inv))).matrix_elem _ _)
    · exact (MvPolynomial.continuous_eval F).comp (continuous_pi fun w =>
        ((((continuous_apply w.1).comp hr.cont)).matrix_mul continuous_const).matrix_elem _ _)
  obtain ⟨B1, h1, hB1⟩ := GlobalTheory.KJAvg.eval_bounded_on_box p (fun _ => 1)
  obtain ⟨B2, h2, hB2⟩ := GlobalTheory.KJAvg.eval_bounded_on_box F (fun w => ∑ l, ‖y w.1 l w.2.2‖)
  refine Integrable.of_bound hc.aestronglyMeasurable (B1 * B2) (Filter.Eventually.of_forall fun k => ?_)
  rw [norm_mul]
  refine mul_le_mul (hB1 _ fun w => entry_norm_bound_of_unitary (hr.uni _ _) _ _) (hB2 _ fun w => ?_)
    (norm_nonneg _) h1
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (entry_norm_bound_of_unitary (hr.uni _ _) _ _)

end

theorem avg_span : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b), 0 < a → ∀ (lam : ι → DomWeight a) (n : ι → ℕ) (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (r : K → ι → Matrix (Fin a) (Fin a) ℂ), OntoUni r → ∀ (y : ι → Matrix (Fin a) (Fin a) ℂ) (P : FP ι a b), ∃ (m : ℕ) (y' : Fin m → ι → Matrix (Fin b) (Fin b) ℂ) (s : Fin m → ℂ), (∀ j, IsInv (y' j)) ∧ ∀ F ∈ Vn lam n, ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, ∫ k, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) P) * evalAt (fun τ => r k τ * y τ) F ∂ν = ∑ j, s j * Λ (subY hab (y' j) F) := by
  intro ι _ a b hab ha lam n K _ _ _ _ _ ν _ _ r hr y P
  obtain ⟨-, hcomp, -, -, -, hev, -, -⟩ := GlobalTheory.T.fockSubstitution_identities ι a b hab
  let S := (univSubst P).support
  let c : (ι × Fin b × Fin a →₀ ℕ) → K → ℂ := fun m k =>
    eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) (coeff m (univSubst P))
  have hΛ : ∀ (Λ : FP ι a b →ₗ[ℂ] ℂ) k, Λ (mvZ (fun τ => r k⁻¹ τ) (fun _ => 1) P) =
      ∑ m ∈ S, c m k * Λ (monomial m 1) := by
    intro Λ k
    rw [mvZ_one_eq_map_univSubst, linear_eq_sum_coeff Λ S _ (support_map_subset _ _)]
    simp only [coeff_map]
    rfl
  have hint : ∀ m F, Integrable (fun k => c m k * evalAt (fun τ => r k τ * y τ) F) ν :=
    fun m F => integrable_avg_term ν hr _ y F
  let φ : (ι × Fin b × Fin a →₀ ℕ) → PY ι a →ₗ[ℂ] ℂ := fun m =>
    { toFun := fun F => ∫ k, c m k * evalAt (fun τ => r k τ * y τ) F ∂ν
      map_add' := fun F G => by
        have e : ∀ k, c m k * evalAt (fun τ => r k τ * y τ) (F + G) =
            c m k * evalAt (fun τ => r k τ * y τ) F + c m k * evalAt (fun τ => r k τ * y τ) G := by
          intro k; simp only [evalAt, map_add, mul_add]
        simp only [e]
        exact integral_add (hint m F) (hint m G)
      map_smul' := fun t F => by
        have e : ∀ k, c m k * evalAt (fun τ => r k τ * y τ) (t • F) =
            t * (c m k * evalAt (fun τ => r k τ * y τ) F) := by
          intro k; simp only [evalAt, smul_eval]; ring
        simp only [e, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul _ _ }
  let Q : PY ι a →ₗ[ℂ] FP ι a b := ∑ m ∈ S, (φ m).smulRight (monomial m 1)
  have hQ : ∀ (Λ : FP ι a b →ₗ[ℂ] ℂ) F, Λ (Q F) =
      ∫ k, Λ (mvZ (fun τ => r k⁻¹ τ) (fun _ => 1) P) * evalAt (fun τ => r k τ * y τ) F ∂ν := by
    intro Λ F
    have e : ∀ k, Λ (mvZ (fun τ => r k⁻¹ τ) (fun _ => 1) P) * evalAt (fun τ => r k τ * y τ) F =
        ∑ m ∈ S, c m k * evalAt (fun τ => r k τ * y τ) F * Λ (monomial m 1) := by
      intro k; rw [hΛ, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [e]
    rw [integral_finset_sum _ (fun m _ => (hint m F).mul_const _)]
    simp only [Q, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_mul_const]; rfl
  have heq : ∀ u, IsUni u → ∀ F ∈ Vn lam n, Q (lft u F) = mvZ u (fun _ => 1) (Q F) := by
    intro u hu F _
    obtain ⟨k0, rfl⟩ := hr.onto u hu
    ext m'
    have h1 := hQ (lcoeff ℂ m') (lft (r k0) F)
    have h2 := hQ ((lcoeff ℂ m').comp (mvZ (r k0) (fun _ => 1)).toLinearMap) F
    simp only [lcoeff_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h1 h2
    rw [h1, h2]
    conv_rhs => rw [← integral_mul_left_eq_self _ k0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have e1 : (fun τ => r (k0 * k)⁻¹ τ * r k0 τ) = fun τ => r k⁻¹ τ := by
      funext τ; rw [← hr.mul]; congr 2; group
    have e2 : (fun τ => r (k0 * k) τ * y τ) = fun τ => r k0 τ * (r k τ * y τ) := by
      funext τ; rw [hr.mul, mul_assoc]
    dsimp only
    rw [hev, hcomp, e1, e2, mul_one]
  obtain ⟨m, y', s, hinv, hspan⟩ := GlobalTheory.T.howeSpan_families_of_places ι a b hab ha lam n Q heq
  refine ⟨m, y', s, hinv, fun F hF Λ => ?_⟩
  simp_rw [ontoUni_inv hr]
  rw [← hQ, hspan F hF, map_sum]
  simp [map_smul]

end GlobalTheory.KJAvg
