import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinR
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinI
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinE
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCTie

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts Matrix

variable {E : Type} [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] {d : ℕ}

def muC (E : Type) [Field E] [NumberField E] : ℝ :=
  Real.sqrt ((finrank ℚ E : ℝ) * ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E) / 2)

theorem muC_sq : muC E ^ 2 =
    (finrank ℚ E : ℝ) * ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E) / 2 := by
  unfold muC
  rw [Real.sq_sqrt]
  positivity

theorem muC_pos : 0 < muC E := by
  unfold muC
  apply Real.sqrt_pos.mpr
  have h1 : (0 : ℝ) < finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have h0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have h2 : (0 : ℝ) < (((discr E).natAbs : ℝ) ^ 2)⁻¹ := by positivity
  positivity

theorem repr_left (b : Basis (Fin d) ℤ Y) (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (y z : Y) :
    ∑ j, (b.repr y j : ℝ) * β (b j) z = β y z := by
  conv_rhs => rw [← b.sum_repr y]
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul]

theorem repr_right (b : Basis (Fin d) ℤ Y) (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (y z : Y) :
    ∑ j, β z (b j) * (b.repr y j : ℝ) = β z y := by
  conv_rhs => rw [← b.sum_repr y]
  simp only [map_sum, map_zsmul, zsmul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem repr_smul_expand (b : Basis (Fin d) ℤ Y) (u : 𝓞 E) (y : Y) (a : Fin d) :
    (b.repr (u • y) a : ℝ) = ∑ j, (b.repr y j : ℝ) * (b.repr (u • b j) a : ℝ) := by
  have h : u • y = ∑ j, b.repr y j • (u • b j) := by
    conv_lhs => rw [← b.sum_repr y]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm u (b.repr y j) (b j)
  rw [h, map_sum, Finsupp.finset_sum_apply, Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, Finsupp.smul_apply, smul_eq_mul, Int.cast_mul]

def Kmat (b : Basis (Fin d) ℤ Y) (u : 𝓞 E) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a c => (b.repr (u • b c) a : ℝ)

theorem Kmat_mul (b : Basis (Fin d) ℤ Y) (u v : 𝓞 E) : Kmat b u * Kmat b v = Kmat b (u * v) := by
  ext a c
  simp only [Kmat, Matrix.mul_apply, Matrix.of_apply]
  rw [mul_smul, repr_smul_expand b u (v • b c) a]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem Kmat_nat (b : Basis (Fin d) ℤ Y) (N : ℕ) : Kmat b (N : 𝓞 E) = (N : ℝ) • 1 := by
  ext a c
  simp only [Kmat, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [show ((N : 𝓞 E) • b c) = N • b c from Nat.cast_smul_eq_nsmul _ _ _, map_nsmul, b.repr_self,
    Finsupp.smul_apply, Finsupp.single_apply]
  by_cases h : a = c
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem Kmat_det (b : Basis (Fin d) ℤ Y) (θ : 𝓞 E) (hθ : θ ≠ 0) : IsUnit (Kmat b θ).det := by
  have hint : IsIntegral ℤ θ := by
    first
    | exact NumberField.RingOfIntegers.isIntegral θ
    | exact Algebra.IsIntegral.isIntegral θ
  have hc0 : (minpoly ℤ θ).coeff 0 ≠ 0 := by
    intro h0c
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr h0c
    rcases (minpoly.irreducible hint).isUnit_or_isUnit hr with hu | hu
    · exact Polynomial.not_isUnit_X hu
    · have h := minpoly.aeval ℤ θ
      rw [hr, map_mul, Polynomial.aeval_X] at h
      exact hθ (((hu.map (Polynomial.aeval θ)).mul_left_eq_zero).mp h)
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := minpoly ℤ θ)
  have h0 : Polynomial.aeval θ (minpoly ℤ θ) = 0 := minpoly.aeval ℤ θ
  have h1 : θ * Polynomial.aeval θ q = -(((minpoly ℤ θ).coeff 0 : ℤ) : 𝓞 E) := by
    have h := congrArg (Polynomial.aeval θ) hq
    simp only [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, h0, zero_sub,
      eq_intCast, map_intCast] at h
    linear_combination -h
  have h2 : θ * (-(Polynomial.aeval θ q) * (((minpoly ℤ θ).coeff 0 : ℤ) : 𝓞 E)) =
      (((minpoly ℤ θ).coeff 0).natAbs ^ 2 : ℕ) := by
    have hc : ((((minpoly ℤ θ).coeff 0).natAbs ^ 2 : ℕ) : 𝓞 E) =
        (((minpoly ℤ θ).coeff 0 : ℤ) : 𝓞 E) ^ 2 := by
      have h' : ((((minpoly ℤ θ).coeff 0).natAbs ^ 2 : ℕ) : ℤ) = ((minpoly ℤ θ).coeff 0) ^ 2 := by
        push_cast
        first
        | exact sq_abs _
        | exact Int.natAbs_sq _
      rw [← Int.cast_natCast, h', Int.cast_pow]
    rw [hc]
    linear_combination (-(((minpoly ℤ θ).coeff 0 : ℤ) : 𝓞 E)) * h1
  have h3 := Kmat_mul b θ (-(Polynomial.aeval θ q) * (((minpoly ℤ θ).coeff 0 : ℤ) : 𝓞 E))
  rw [h2, Kmat_nat] at h3
  have h4 := congrArg Matrix.det h3
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h4
  have hN : ((((minpoly ℤ θ).coeff 0).natAbs ^ 2 : ℕ) : ℝ) ^ Fintype.card (Fin d) ≠ 0 := by
    have : ((minpoly ℤ θ).coeff 0).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc0
    positivity
  rw [isUnit_iff_ne_zero]
  intro h
  rw [h, zero_mul] at h4
  exact hN h4.symm

theorem bs_comp (b : Basis (Fin d) ℤ Y) (u : 𝓞 E) (a : Fin d) :
    bs b a ∘ₗ smulZ u = ∑ j, Kmat b u a j • bs b j := by
  ext y
  have h1 : ∀ (a : Fin d) (z : Y), bs b a z = (b.repr z a : ℝ) := fun a z => by
    simp [bs]
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, h1,
    smul_eq_mul]
  have h2 : smulZ u y = u • y := rfl
  rw [h2, repr_smul_expand]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  rfl

section Main

variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj

theorem Pm_comm (η ζ : Y →ₗ[ℤ] ℝ) : Pm hcj η ζ = Pm hcj ζ η := by
  apply Subtype.ext
  apply LinearMap.ext₂
  intro a c
  simp only [Pm_apply]
  exact Pf_comm η ζ a c

theorem Pm_skew (θ : 𝓞 E) (hθ : ∀ σ : E →+* ℂ, star (σ (θ : E)) = -σ (θ : E))
    (η ζ : Y →ₗ[ℤ] ℝ) : Pm hcj (η ∘ₗ smulZ θ) ζ = -Pm hcj η (ζ ∘ₗ smulZ θ) := by
  apply Subtype.ext
  apply LinearMap.ext₂
  intro a c
  simp only [Submodule.coe_neg, LinearMap.neg_apply, Pm_apply]
  exact Pf_skew θ hθ η ζ a c

theorem main_ineq (hne : ∃ z : E, cj z ≠ z) [Module.Free ℤ Y] [Module.Finite ℤ Y] (hd : 0 < d)
    (b : Basis (Fin d) ℤ Y) (β : SymB cj Y)
    (hG : (Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c)).PosDef)
    (l : SymB cj Y →ₗ[ℝ] ℝ)
    (hint : ∀ β' : SymB cj Y, (∀ a c, ∃ z : ℤ, (β' : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) →
      ∃ z : ℤ, l β' = z)
    (hpos : ∀ β' : SymB cj Y, (∀ a, 0 ≤ (β' : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β' ≠ 0 → 0 < l β')
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : Fin d → Fin d → ℤ, LinearIndependent ℤ c ∧ ∀ j,
      (fun i => (c j i : ℝ)) ⬝ᵥ ((Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c)) *ᵥ
        fun i => (c j i : ℝ)) ≤ (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 := by
  classical
  obtain ⟨m, x, x', htie⟩ := phiCTie_holds E cj Y l hint
  obtain ⟨θ, hθ0, hθ⟩ := exists_theta hcj hne
  have hθs : ∀ σ : E →+* ℂ, star (σ (θ : E)) = -σ (θ : E) := fun σ => by rw [← hcj, hθ, map_neg]
  set G := Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) with hGdef
  set L : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun a c => l (Pm hcj (bs b a) (bs b c)) / 2 with hLdef
  set K := Kmat b θ with hKdef
  have hPmsum : ∀ t : Fin d → ℝ, Pm hcj (∑ a, t a • bs b a) (∑ a, t a • bs b a) =
      ∑ a, ∑ c, (t a * t c) • Pm hcj (bs b a) (bs b c) := by
    intro t
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
      smul_smul]
    rw [Finset.sum_comm (f := fun x y => (t x * t y) • Pm hcj (bs b y) (bs b x))]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]
  have hLq : ∀ t : Fin d → ℝ, t ⬝ᵥ (L *ᵥ t) =
      l (Pm hcj (∑ a, t a • bs b a) (∑ a, t a • bs b a)) / 2 := by
    intro t
    rw [hPmsum]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct, Matrix.mulVec, hLdef, Matrix.of_apply,
      Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  have hbs_ne : ∀ t : Fin d → ℝ, t ≠ 0 → ∑ a, t a • bs b a ≠ 0 := by
    intro t ht h0
    apply ht
    funext a
    have h1 := LinearMap.congr_fun h0 (b a)
    simpa [bs_apply, Basis.repr_self, Finsupp.single_apply, LinearMap.sum_apply] using h1
  have hLsym : ∀ a c, L a c = L c a := by
    intro a c
    simp only [hLdef, Matrix.of_apply, Pm_comm hcj (bs b a) (bs b c)]
  have hLpd : L.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun t ht => ?_
    · exact Matrix.IsHermitian.ext fun i j => by rw [star_trivial, hLsym]
    · rw [star_trivial, hLq]
      have := hpos _ (Pm_psd hcj _) (Pm_ne_zero hcj (hbs_ne t ht))
      linarith
  obtain ⟨R, hRdet, hLR⟩ := whiten_holds d L hLpd
  have hKG : Kᵀ * G = -(G * K) := by
    ext a c
    simp only [hKdef, hGdef, Kmat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.neg_apply]
    rw [repr_left b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (θ • b a) (b c),
      repr_right b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (θ • b c) (b a)]
    have hbal := β.2.2 θ (-θ) (by rw [hθ]; exact map_neg (algebraMap (𝓞 E) E) θ) (b a) (b c)
    rw [hbal, neg_smul, map_neg]
  have hKL : K * L = -(L * Kᵀ) := by
    ext a c
    have e1 : (K * L) a c = l (Pm hcj (bs b a ∘ₗ smulZ θ) (bs b c)) / 2 := by
      rw [bs_comp b θ a]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        Matrix.mul_apply, hLdef, hKdef, Matrix.of_apply, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : (L * Kᵀ) a c = l (Pm hcj (bs b a) (bs b c ∘ₗ smulZ θ)) / 2 := by
      rw [bs_comp b θ c]
      simp only [map_sum, map_smul, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, hLdef,
        hKdef, Matrix.of_apply, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Matrix.neg_apply, e1, e2, Pm_skew hcj θ hθs, map_neg]
    ring
  have hKdet : IsUnit K.det := Kmat_det b θ (fun h => hθ0 (by rw [h]; simp))
  have htr : trace (L * G) = l β := by
    rw [l_expand hcj b l β]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hLdef, hGdef, Matrix.of_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [β.2.1 (b c) (b a)]
    ring
  have hlow : ∀ t : Fin d → ℤ, t ≠ 0 →
      muC E ^ 2 ≤ (fun i => (t i : ℝ)) ⬝ᵥ (L *ᵥ fun i => (t i : ℝ)) := by
    intro t ht
    rw [hLq, muC_sq]
    have hη : ∑ a, (t a : ℝ) • bs b a = Algebra.linearMap ℤ ℝ ∘ₗ (∑ a, t a • b.coord a) := by
      refine LinearMap.ext fun y => ?_
      simp [bs_apply, LinearMap.sum_apply, Basis.coord_apply]
    have hν : (∑ a, t a • b.coord a) ≠ 0 := by
      intro h0
      apply ht
      funext a
      have h1 := LinearMap.congr_fun h0 (b a)
      simpa [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, LinearMap.sum_apply] using h1
    rw [hη]
    have := lower_bound hcj l hpos x x' htie _ hν
    linarith
  obtain ⟨c, hcli, hcb⟩ := shortDual_holds d L R (muC E) hd hLR hRdet muC_pos hlow δ hδ
  refine ⟨c, hcli, fun j => ?_⟩
  have h1 := halfTrace_holds d L G K R hLR hRdet hG.posSemidef hKG hKL hKdet (fun i => (c j i : ℝ))
  rw [htr] at h1
  have hlβ : 0 ≤ l β := by
    by_cases h0 : β = 0
    · rw [h0, map_zero]
    · refine (hpos β (fun y => ?_) h0).le
      have h2 := hG.posSemidef.dotProduct_mulVec_nonneg (fun a => bs b a y)
      rw [star_trivial] at h2
      have h3 : (fun a => bs b a y) ⬝ᵥ (G *ᵥ fun a => bs b a y) =
          (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y y := by
        rw [← gram_expand b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y y]
        simp only [dotProduct, Matrix.mulVec, hGdef, Matrix.of_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
      linarith
  calc _ ≤ _ := h1
    _ ≤ (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 :=
        mul_le_mul_of_nonneg_left (hcb j) (by linarith)

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
