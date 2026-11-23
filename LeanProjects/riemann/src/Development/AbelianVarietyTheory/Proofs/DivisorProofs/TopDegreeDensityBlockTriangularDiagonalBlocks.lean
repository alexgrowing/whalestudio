import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagTri

theorem eval_zero_of_const {A : Type} [CommRing A] [Algebra ℂ A] (l : A →ₗ[ℂ] ℂ) (Q : Polynomial A) (c : ℂ)
    (h : ∀ x : ℂ, x ≠ 0 → l (Q.eval (algebraMap ℂ A x)) = c) : l (Q.eval (algebraMap ℂ A 0)) = c := by
  have hc : Continuous fun x : ℂ => l (Q.eval (algebraMap ℂ A x)) := by
    clear h
    induction Q using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.eval_add, map_add]; exact hp.add hq
    | monomial k a =>
      have : (fun x : ℂ => l ((Polynomial.monomial k a).eval (algebraMap ℂ A x))) = fun x => x ^ k * l a := by
        funext x
        rw [Polynomial.eval_monomial, ← map_pow, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      rw [this]
      fun_prop
  have := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hc (continuous_const (y := c)) (fun x hx => h x hx)
  exact congrFun this 0

variable {n : ℕ}

def scale (c : Fin n → ℂ) : Alt n →ₐ[ℂ] Alt n :=
  ExteriorAlgebra.map (Matrix.toLin' (Matrix.diagonal (Sum.elim c c)))

theorem dens_scale (c : Fin n → ℂ) (β : Alt n) : dens (scale c β) = (∏ a, c a) ^ 2 * dens β := by
  simp only [dens, scale, bas]
  rw [exterior_repr_univ_map, LinearMap.det_toLin', Matrix.det_diagonal, Fintype.prod_sum_type, mul_div_assoc, sq]
  rfl

theorem scale_dz (c : Fin n → ℂ) (a : Fin n) : scale c (dz a) = c a • dz a ∧ scale c (dzb a) = c a • dzb a := by
  simp only [dz, dzb, ← map_smul]
  constructor <;> refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ (funext ?_)) <;> rintro (b | b) <;>
    by_cases h : b = a <;> simp [Matrix.mulVec_diagonal, Pi.single_apply, h]

theorem scale_sym (c : Fin n → ℂ) (a b : Fin n) :
    scale c (sym (a, b) : Ev n) = (c a * c b) • ((sym (a, b) : Ev n) : Alt n) := by
  change scale c (dz a * dzb b) = (c a * c b) • (dz a * dzb b)
  rw [map_mul, (scale_dz c a).1, (scale_dz c b).2, smul_mul_smul_comm]

theorem scale_pull {d : ℕ} {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (c : Fin n → ℂ) (hc : ∀ a, c (ε.symm (.inl a)) = 1)
    (α : Alt d) : scale c (pull (bsL ε) α) = pull (bsL ε) α := by
  have key (a : Fin d) (b : Fin n) : c b * bsL ε (coordVec b) a = bsL ε (coordVec b) a ∧
      c b * (starRingEnd ℂ) (bsL ε (coordVec b) a) = (starRingEnd ℂ) (bsL ε (coordVec b) a) := by
    rw [bsL_apply]
    by_cases h : ε.symm (.inl a) = b
    · subst h
      simp [hc]
    · simp [coordVec, h]
  rw [scale, pull, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, ← Matrix.toLin'_mul]
  congr 3
  ext (i | i) (j | j) <;> simp [Matrix.diagonal_mul, key]

theorem map_prod_pow {T : Type} (φ : Alt n →ₐ[ℂ] Alt n) (x y : T → Ev n) (r : T → ℕ)
    (h : ∀ t, φ (x t) = y t) (s : Finset T) :
    φ ((∏ t ∈ s, x t ^ r t : Ev n) : Alt n) = ((∏ t ∈ s, y t ^ r t : Ev n) : Alt n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, ih,
      Subalgebra.coe_pow, Subalgebra.coe_pow, map_pow, h]

theorem dens_blockTri : ∀ (n d : ℕ) (J T : Type) [Fintype J] [Fintype T] (ε : Fin n ≃ Fin d ⊕ J) (lev : J → T) (ρ : T → ℕ) (K : T → Fin n → Fin n → ℂ) (r : T → ℕ), (∀ t, r t = Fintype.card {j // lev j = t}) → (∀ t j, lev j ≠ t → ρ t ≤ ρ (lev j) → ∀ b, K t (ε.symm (.inr j)) b = 0 ∧ K t b (ε.symm (.inr j)) = 0) → ∀ α : Alt d, dens (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n) : Alt n)) = dens (pull (bsL ε) α * ((∏ t, (∑ a : {j // lev j = t}, ∑ b : {j // lev j = t}, K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1)) • sym (ε.symm (.inr a.1), ε.symm (.inr b.1))) ^ r t : Ev n) : Alt n)) := by
  intro n d J T _ _ ε lev ρ K r hr hK α
  let wt : Fin n → ℕ := fun a => (ε a).elim (fun _ => 0) fun j => ρ (lev j) + 1
  have w0 (a) : wt (ε.symm (.inl a)) = 0 := by simp [wt]
  have w1 (j) : wt (ε.symm (.inr j)) = ρ (lev j) + 1 := by simp [wt]
  have hw (t : T) (a : Fin n) (h : ∃ b, K t a b ≠ 0 ∨ K t b a ≠ 0) :
      wt a < ρ t + 1 ∨ ∃ j : {j // lev j = t}, ε.symm (.inr j.1) = a := by
    obtain ⟨a | j, rfl⟩ := ε.symm.surjective a
    · left; rw [w0]; omega
    · by_cases e : lev j = t
      · exact .inr ⟨⟨j, e⟩, rfl⟩
      · left
        rw [w1]
        by_contra hn
        obtain ⟨b, hb⟩ := h
        have := hK t j e (by omega) b
        tauto
  have hw' (t : T) (a : Fin n) (h : ∃ b, K t a b ≠ 0 ∨ K t b a ≠ 0) : wt a ≤ ρ t + 1 := by
    rcases hw t a h with h | ⟨j, rfl⟩
    · omega
    · rw [w1, j.2]
  let l : Ev n →ₗ[ℂ] ℂ :=
    { toFun := fun x => dens (pull (bsL ε) α * (x : Alt n))
      map_add' := fun x y => by simp [dens, mul_add, add_div]
      map_smul' := fun c x => by simp [dens, mul_div_assoc] }
  have hl (x : Ev n) : l x = dens (pull (bsL ε) α * (x : Alt n)) := rfl
  let e : T → Fin n → Fin n → ℕ := fun t a b => (ρ t + 1 - wt a) + (ρ t + 1 - wt b)
  let Q : Polynomial (Ev n) := ∏ t, (∑ a, ∑ b, Polynomial.monomial (e t a b) (K t a b • sym (a, b))) ^ r t
  have hQ (x : ℂ) : Q.eval (algebraMap ℂ (Ev n) x) =
      ∏ t, (∑ a, ∑ b, (x ^ e t a b * K t a b) • (sym (a, b) : Ev n)) ^ r t := by
    simp only [Q, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    refine Finset.prod_congr rfl fun t _ => congrArg (· ^ r t) ?_
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← map_pow, mul_comm, ← Algebra.smul_def, smul_smul]
  rw [← hl, ← hl, ← eval_zero_of_const l Q (l (∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n)) ?_]
  · rw [hQ]
    refine congrArg l (Finset.prod_congr rfl fun t _ => congrArg (· ^ r t) ?_)
    have inj : Function.Injective fun j : {j // lev j = t} => ε.symm (.inr j.1) :=
      fun i j h => Subtype.ext (Sum.inr_injective (ε.symm.injective h))
    symm
    refine Fintype.sum_of_injective _ inj _ _ (fun a ha => Finset.sum_eq_zero fun b _ => ?_) fun a => ?_
    · by_cases h : K t a b = 0
      · simp [h]
      · rcases hw t a ⟨b, .inl h⟩ with h' | h'
        · rw [zero_pow (by simp only [e]; omega), zero_mul, zero_smul]
        · exact absurd h' ha
    · refine Fintype.sum_of_injective _ inj _ _ (fun b hb => ?_) fun b => ?_
      · by_cases h : K t (ε.symm (.inr a.1)) b = 0
        · simp [h]
        · rcases hw t b ⟨_, .inr h⟩ with h' | h'
          · rw [zero_pow (by simp only [e]; omega), zero_mul, zero_smul]
          · exact absurd h' hb
      · simp [e, w1, a.2, b.2]
  · intro x hx
    have h1 := dens_scale (fun a => x⁻¹ ^ wt a)
      (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n) : Alt n))
    rw [map_mul, scale_pull ε _ (fun a => by simp [w0]),
      map_prod_pow _ _ (fun t => (x⁻¹ ^ (ρ t + 1)) ^ 2 • ∑ a, ∑ b, (x ^ e t a b * K t a b) • (sym (a, b) : Ev n)) r ?_,
      ← hl, ← hl] at h1
    · have h2 : ∏ a, x⁻¹ ^ wt a = ∏ t, (x⁻¹ ^ (ρ t + 1)) ^ r t := by
        rw [← ε.symm.prod_comp, Fintype.prod_sum_type]
        simp only [w0, w1, pow_zero, Finset.prod_const_one, one_mul]
        rw [← Fintype.prod_fiberwise lev]
        refine Finset.prod_congr rfl fun t _ => ?_
        rw [Finset.prod_congr rfl (g := fun _ => x⁻¹ ^ (ρ t + 1)) fun j _ => by rw [j.2], Finset.prod_const, hr]
        simp
      simp only [smul_pow, Finset.prod_smul] at h1
      rw [map_smul, ← hQ, h2, ← Finset.prod_pow, smul_eq_mul] at h1
      simp only [← pow_mul, mul_right_comm _ (r _) 2] at h1
      refine mul_left_cancel₀ (Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (inv_ne_zero hx)) h1
    · intro t
      simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, map_sum, map_smul, scale_sym, Finset.smul_sum,
        smul_smul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1
      by_cases h : K t a b = 0
      · simp [h]
      · obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le (hw' t a ⟨b, .inl h⟩)
        obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (hw' t b ⟨a, .inr h⟩)
        have : e t a b = p + q := by simp only [e]; omega
        rw [this, sq]
        nth_rw 1 [hp]
        rw [hq]
        simp only [inv_pow]
        field_simp
        ring

end GlobalTheory.FlagTri
