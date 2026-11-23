import Mathlib
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassXRing

universe u

namespace GroundTheory.Arith.Modular

open Polynomial Polynomial.Bivariate

namespace Weierstrass

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem ringHom_eq_eval₂ {S : Type*} [CommRing S] (φ : R[X] →+* S) (q : R[X]) :
    φ q = q.eval₂ (φ.comp C) (φ X) := by
  conv_lhs => rw [← Polynomial.eval₂_C_X (p := q)]
  rw [Polynomial.hom_eval₂]

noncomputable def coordA [Nontrivial R] (a : W.toAffine.CoordinateRing) : Fin 3 →₀ R[X] :=
  (basisX W).repr (xAlgEquiv W a)

noncomputable def coordI [Nontrivial R] (b : InfChart W) : Fin 3 →₀ R[X] := (basisI W).repr b

theorem eq_sum_coordA [Nontrivial R] (a : W.toAffine.CoordinateRing) :
    a = ∑ i : Fin 3, (coordA W a i).eval₂ (algebraMap R _) (yC W) * xC W ^ (i : ℕ) := by
  apply (xAlgEquiv W).injective
  conv_lhs => rw [← (basisX W).sum_repr (xAlgEquiv W a)]
  simp only [map_sum, map_mul, map_pow, xAlgEquiv_xC, basisX_apply, coordA]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def]
  congr 1
  have e : ∀ q : R[X], xAlgEquiv W (q.eval₂ (algebraMap R _) (yC W)) =
      q.eval₂ ((xAlgEquiv W).toRingHom.comp (algebraMap R _)) (xAlgEquiv W (yC W)) :=
    fun q => Polynomial.hom_eval₂ q (algebraMap R _) (xAlgEquiv W).toRingEquiv.toRingHom (yC W)
  rw [ringHom_eq_eval₂ (algebraMap R[X] (XRing W)), e, xAlgEquiv_yC]
  congr 1
  ext r
  simp
  rfl

theorem eq_sum_coordI [Nontrivial R] (b : InfChart W) :
    b = ∑ i : Fin 3, (coordI W b i).eval₂ (algebraMap R _) (zI W) * xI W ^ (i : ℕ) := by
  conv_lhs => rw [← (basisI W).sum_repr b]
  simp only [basisI_apply, coordI]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def]
  congr 1
  rw [ringHom_eq_eval₂ (algebraMap R[X] (InfChart W))]
  rfl

section Coordinates

variable [Nontrivial R]

theorem coordA_sum (P : Fin 3 → R[X]) :
    coordA W (∑ i : Fin 3, (P i).eval₂ (algebraMap R _) (yC W) * xC W ^ (i : ℕ)) =
      Finsupp.equivFunOnFinite.symm P := by
  have e : ∀ q : R[X], xAlgEquiv W (q.eval₂ (algebraMap R _) (yC W)) = algebraMap R[X] _ q := by
    intro q
    rw [ringHom_eq_eval₂ (algebraMap R[X] (XRing W))]
    rw [show xAlgEquiv W (q.eval₂ (algebraMap R _) (yC W)) =
      q.eval₂ ((xAlgEquiv W).toRingEquiv.toRingHom.comp (algebraMap R _)) (xAlgEquiv W (yC W)) from
      Polynomial.hom_eval₂ q (algebraMap R _) (xAlgEquiv W).toRingEquiv.toRingHom (yC W)]
    rw [xAlgEquiv_yC]
    congr 1
    ext r
    simp
    rfl
  have h : xAlgEquiv W (∑ i : Fin 3, (P i).eval₂ (algebraMap R _) (yC W) * xC W ^ (i : ℕ)) =
      (basisX W).equivFun.symm P := by
    simp only [map_sum, map_mul, map_pow, e, xAlgEquiv_xC, Module.Basis.equivFun_symm_apply,
      basisX_apply, Algebra.smul_def]
  rw [coordA, h]
  ext i : 1
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem coordA_injective : Function.Injective (coordA W) := by
  intro a b h
  exact (xAlgEquiv W).injective ((basisX W).repr.injective h)

theorem coordA_yC_pow_mul (n : ℕ) (a : W.toAffine.CoordinateRing) :
    coordA W (yC W ^ n * a) = (X ^ n : R[X]) • coordA W a := by
  conv_lhs => rw [eq_sum_coordA W a, Finset.mul_sum]
  have : ∀ i : Fin 3, yC W ^ n * ((coordA W a i).eval₂ (algebraMap R _) (yC W) * xC W ^ (i : ℕ)) =
      (X ^ n * coordA W a i).eval₂ (algebraMap R _) (yC W) * xC W ^ (i : ℕ) := by
    intro i
    rw [eval₂_mul, eval₂_X_pow]
    ring
  simp only [this, coordA_sum]
  ext i
  simp

theorem yC_mul_eq_zero {a : W.toAffine.CoordinateRing} (h : yC W * a = 0) : a = 0 := by
  apply coordA_injective W
  have h2 := coordA_yC_pow_mul W 1 a
  rw [pow_one, h] at h2
  ext i k
  have h3 := congrArg (fun f : Fin 3 →₀ R[X] => (f i).coeff (k + 1)) h2
  simp only [Finsupp.smul_apply, smul_eq_mul, pow_one, coeff_X_mul] at h3
  rw [← h3]
  simp [coordA]

end Coordinates

section Overlap

noncomputable instance invertibleY :
    Invertible (algebraMap W.toAffine.CoordinateRing (Overlap W) (yC W)) :=
  ⟨yInv W, by rw [mul_comm]; exact yC_mul_yInv W, yC_mul_yInv W⟩

theorem invOf_yC : ⅟(algebraMap W.toAffine.CoordinateRing (Overlap W) (yC W)) = yInv W := rfl

theorem algebraMap_overlap_injective :
    Function.Injective (algebraMap W.toAffine.CoordinateRing (Overlap W)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton W.toAffine.CoordinateRing := Module.subsingleton R _
    exact fun a b _ => Subsingleton.elim a b
  have hy : Submonoid.powers (yC W) ≤ nonZeroDivisors _ := by
    rw [Submonoid.powers_le]
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun z hz => yC_mul_eq_zero W hz, fun z hz => yC_mul_eq_zero W (by rwa [mul_comm])⟩
  exact IsLocalization.injective (Overlap W) hy

theorem infToOverlap_eval₂ (q : R[X]) :
    infToOverlap W (q.eval₂ (algebraMap R _) (zI W)) =
      q.eval₂ (algebraMap R (Overlap W)) (yInv W) := by
  rw [show infToOverlap W (q.eval₂ (algebraMap R _) (zI W)) =
    q.eval₂ ((infToOverlap W).toRingHom.comp (algebraMap R _)) (infToOverlap W (zI W))
    from Polynomial.hom_eval₂ _ _ (infToOverlap W).toRingHom _, infToOverlap_zI]
  have hc : (infToOverlap W).toRingHom.comp (algebraMap R (InfChart W)) =
      algebraMap R (Overlap W) := (infToOverlap W).comp_algebraMap
  rw [hc]

variable [Nontrivial R]

theorem infToOverlap_eq (b : InfChart W) :
    infToOverlap W b = ∑ i : Fin 3, (coordI W b i).eval₂ (algebraMap R (Overlap W)) (yInv W) *
      (algebraMap _ (Overlap W) (xC W) * yInv W) ^ (i : ℕ) := by
  have h := congrArg (infToOverlap W) (eq_sum_coordI W b)
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, infToOverlap_xI, infToOverlap_eval₂]

theorem yC_pow_mul_infToOverlap (b : InfChart W) (N : ℕ)
    (hN : ∀ i : Fin 3, (coordI W b i).natDegree + i ≤ N) :
    algebraMap _ (Overlap W) (yC W) ^ N * infToOverlap W b =
      algebraMap _ (Overlap W) (∑ i : Fin 3, (reflect (N - i) (coordI W b i)).eval₂
        (algebraMap R _) (yC W) * xC W ^ (i : ℕ)) := by
  rw [infToOverlap_eq, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hq : (coordI W b i).natDegree ≤ N - i := by have := hN i; omega
  have hNi : N = (N - i) + i := by have := hN i; omega
  set y := algebraMap W.toAffine.CoordinateRing (Overlap W) (yC W)
  set x := algebraMap W.toAffine.CoordinateRing (Overlap W) (xC W)
  set q := coordI W b i
  have key : q.eval₂ (algebraMap R (Overlap W)) (yInv W) * y ^ (N - i) =
      (reflect (N - i) q).eval₂ (algebraMap R (Overlap W)) y := by
    have := eval₂_reflect_mul_pow (algebraMap R (Overlap W)) y (N - i) (reflect (N - i) q)
      (natDegree_reflect_le.trans (by simp [hq]))
    rwa [reflect_reflect, invOf_yC] at this
  rw [map_mul, map_pow, show algebraMap W.toAffine.CoordinateRing (Overlap W)
    ((reflect (N - i) q).eval₂ (algebraMap R _) (yC W)) =
      (reflect (N - i) q).eval₂ (algebraMap R (Overlap W)) y by
    rw [Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq], ← key]
  have hyu : y * yInv W = 1 := yC_mul_yInv W
  conv_lhs => rw [hNi, pow_add]
  calc y ^ (N - i) * y ^ (i : ℕ) * (q.eval₂ (algebraMap R (Overlap W)) (yInv W) * (x * yInv W) ^ (i : ℕ))
      = q.eval₂ (algebraMap R (Overlap W)) (yInv W) * y ^ (N - i) * x ^ (i : ℕ) *
          (y * yInv W) ^ (i : ℕ) := by ring
    _ = _ := by rw [hyu, one_pow, mul_one]

end Overlap

section Main

variable [Nontrivial R]

noncomputable def degBound (b : InfChart W) : ℕ := (∑ i : Fin 3, (coordI W b i).natDegree) + 3

theorem le_degBound (b : InfChart W) (i : Fin 3) :
    (coordI W b i).natDegree + i ≤ degBound W b := by
  have h1 : (coordI W b i).natDegree ≤ ∑ j : Fin 3, (coordI W b j).natDegree :=
    Finset.single_le_sum (f := fun j => (coordI W b j).natDegree) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h2 : (i : ℕ) < 3 := i.isLt
  unfold degBound
  omega

theorem coordA_eq_of_sub_eq (a : W.toAffine.CoordinateRing) (b : InfChart W) (r : R)
    (h : algebraMap _ (Overlap W) a - infToOverlap W b =
      r • (algebraMap _ (Overlap W) (xC W) ^ 2 * yInv W)) :
    (X ^ degBound W b : R[X]) • coordA W a = Finsupp.equivFunOnFinite.symm (fun i : Fin 3 =>
      reflect (degBound W b - i) (coordI W b i) +
        if i = 2 then C r * X ^ (degBound W b - 1) else 0) := by
  set N := degBound W b
  have hN3 : 3 ≤ N := by unfold N degBound; omega
  have hy := yC_pow_mul_infToOverlap W b N (le_degBound W b)
  have hA : yC W ^ N * a = ∑ i : Fin 3, (reflect (N - i) (coordI W b i) +
      if i = 2 then C r * X ^ (N - 1) else 0).eval₂ (algebraMap R _) (yC W) * xC W ^ (i : ℕ) := by
    apply algebraMap_overlap_injective W
    have h' : algebraMap _ (Overlap W) a = infToOverlap W b +
        r • (algebraMap _ (Overlap W) (xC W) ^ 2 * yInv W) := by rw [← h]; ring
    have hsplit : ∑ i : Fin 3, (reflect (N - i) (coordI W b i) +
        if i = 2 then C r * X ^ (N - 1) else 0).eval₂ (algebraMap R W.toAffine.CoordinateRing)
          (yC W) * xC W ^ (i : ℕ) =
        (∑ i : Fin 3, (reflect (N - i) (coordI W b i)).eval₂ (algebraMap R _) (yC W) *
          xC W ^ (i : ℕ)) + r • (xC W ^ 2 * yC W ^ (N - 1)) := by
      simp only [Fin.sum_univ_three, eval₂_add]
      simp [Algebra.smul_def]
      ring
    rw [hsplit, map_add, ← hy, map_mul, map_pow, h', mul_add]
    congr 1
    simp only [Algebra.smul_def, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    have hyu := yC_mul_yInv W
    have hN : N = (N - 1) + 1 := by omega
    conv_lhs => rw [hN, pow_succ]
    linear_combination (algebraMap R (Overlap W) r *
      algebraMap W.toAffine.CoordinateRing (Overlap W) (xC W) ^ 2 *
      algebraMap W.toAffine.CoordinateRing (Overlap W) (yC W) ^ (N - 1)) * hyu
  rw [← coordA_yC_pow_mul, hA, coordA_sum]

end Main

section Main2

variable [Nontrivial R]

theorem eq_zero_of_sub_eq_smul (a : W.toAffine.CoordinateRing) (b : InfChart W) (r : R)
    (h : algebraMap _ (Overlap W) a - infToOverlap W b =
      r • (algebraMap _ (Overlap W) (xC W) ^ 2 * yInv W)) : r = 0 := by
  have hc := congrArg (fun f : Fin 3 →₀ R[X] => (f 2).coeff (degBound W b - 1))
    (coordA_eq_of_sub_eq W a b r h)
  have hN3 : 3 ≤ degBound W b := by unfold degBound; omega
  have hq := le_degBound W b 2
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_equivFunOnFinite_symm] at hc
  simp only [coeff_add, coeff_X_pow_mul', coeff_reflect] at hc
  have hrev : revAt (degBound W b - ((2 : Fin 3) : ℕ)) (degBound W b - 1) = degBound W b - 1 :=
    revAt_eq_self_of_lt (by simp; omega)
  rw [if_neg (by omega), hrev, coeff_eq_zero_of_natDegree_lt (by simp at hq; omega), if_pos trivial,
    coeff_C_mul_X_pow, if_pos rfl, zero_add] at hc
  exact hc.symm

end Main2

section Kernel

variable [Nontrivial R]

end Kernel

section Span

noncomputable def cechMap : (W.toAffine.CoordinateRing × InfChart W) →ₗ[R] Overlap W :=
  (IsScalarTower.toAlgHom R W.toAffine.CoordinateRing (Overlap W)).toLinearMap.comp
      (LinearMap.fst R _ _) -
    (infToOverlap W).toLinearMap.comp (LinearMap.snd R _ _)

@[simp]
theorem cechMap_apply (p : W.toAffine.CoordinateRing × InfChart W) :
    cechMap W p = algebraMap _ (Overlap W) p.1 - infToOverlap W p.2 := rfl

noncomputable def cechGen : Overlap W := algebraMap _ (Overlap W) (xC W) ^ 2 * yInv W

noncomputable def cechSpan : Submodule R (Overlap W) :=
  LinearMap.range (cechMap W) ⊔ Submodule.span R {cechGen W}

theorem monomial_mem_cechSpan (k n : ℕ) (i : Fin 3) :
    algebraMap _ (Overlap W) (yC W ^ k * xC W ^ (i : ℕ)) * yInv W ^ n ∈ cechSpan W := by
  set y := algebraMap W.toAffine.CoordinateRing (Overlap W) (yC W)
  set x := algebraMap W.toAffine.CoordinateRing (Overlap W) (xC W)
  have hyu : y * yInv W = 1 := yC_mul_yInv W
  rw [map_mul, map_pow, map_pow]
  by_cases hnk : n ≤ k
  · apply Submodule.mem_sup_left
    refine ⟨(yC W ^ (k - n) * xC W ^ (i : ℕ), 0), ?_⟩
    simp only [cechMap_apply, map_zero, sub_zero, map_mul, map_pow]
    have hk : k = (k - n) + n := by omega
    conv_rhs => rw [hk, pow_add]
    calc y ^ (k - n) * x ^ (i : ℕ) = y ^ (k - n) * x ^ (i : ℕ) * (y * yInv W) ^ n := by
          rw [hyu, one_pow, mul_one]
      _ = _ := by ring
  · have hm : n = k + (n - k) := by omega
    have hval : y ^ k * x ^ (i : ℕ) * yInv W ^ n = x ^ (i : ℕ) * yInv W ^ (n - k) := by
      conv_lhs => rw [hm, pow_add]
      calc y ^ k * x ^ (i : ℕ) * (yInv W ^ k * yInv W ^ (n - k))
          = x ^ (i : ℕ) * yInv W ^ (n - k) * (y * yInv W) ^ k := by ring
        _ = _ := by rw [hyu, one_pow, mul_one]
    rw [hval]
    by_cases hi : (i : ℕ) ≤ n - k
    · apply Submodule.mem_sup_left
      refine ⟨(0, -(zI W ^ (n - k - i) * xI W ^ (i : ℕ))), ?_⟩
      simp only [cechMap_apply, map_zero, zero_sub, map_neg, neg_neg, map_mul, map_pow,
        infToOverlap_xI, infToOverlap_zI]
      have : n - k = (n - k - i) + i := by omega
      conv_rhs => rw [this, pow_add]
      ring
    · apply Submodule.mem_sup_right
      have hi2 : (i : ℕ) = 2 := by have := i.isLt; omega
      have hnk1 : n - k = 1 := by omega
      rw [hi2, hnk1, pow_one]
      exact Submodule.subset_span rfl

variable [Nontrivial R]

noncomputable def basisXR : Module.Basis (ℕ × Fin 3) R (XRing W) :=
  (Polynomial.basisMonomials R).smulTower (basisX W)

theorem xAlgEquiv_symm_basisXR (k : ℕ) (i : Fin 3) :
    (xAlgEquiv W).symm (basisXR W (k, i)) = yC W ^ k * xC W ^ (i : ℕ) := by
  rw [AlgEquiv.symm_apply_eq, map_mul, map_pow, map_pow, xAlgEquiv_xC, xAlgEquiv_yC, basisXR,
    Module.Basis.smulTower_apply, basisX_apply, Polynomial.coe_basisMonomials, Algebra.smul_def]
  congr 1
  rw [← map_pow]
  simp [Polynomial.monomial_one_right_eq_X_pow]

theorem cechSpan_eq_top : cechSpan W = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hv⟩ := IsLocalization.surj (Submonoid.powers (yC W)) v
  simp only at hv
  have hv' : v = algebraMap _ (Overlap W) a * yInv W ^ n := by
    rw [← hv, mul_assoc, map_pow, ← mul_pow, yC_mul_yInv W, one_pow, mul_one]
  rw [hv']
  let Ψ : XRing W →ₗ[R] Overlap W :=
    (LinearMap.mulRight R (yInv W ^ n)).comp
      ((IsScalarTower.toAlgHom R W.toAffine.CoordinateRing (Overlap W)).toLinearMap.comp
        (xAlgEquiv W).symm.toLinearMap)
  have hrange : LinearMap.range Ψ ≤ cechSpan W := by
    rw [LinearMap.range_eq_map, ← (basisXR W).span_eq, Submodule.map_span_le]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    simp only [Ψ, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
      xAlgEquiv_symm_basisXR, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
      LinearMap.mulRight_apply]
    exact monomial_mem_cechSpan W k n i
  have := hrange ⟨xAlgEquiv W a, rfl⟩
  simpa [Ψ] using this

end Span

section Cohomology

theorem subsingleton_of_subsingleton [Subsingleton R] : Subsingleton (Overlap W) := by
  have : Subsingleton W.toAffine.CoordinateRing := Module.subsingleton R _
  exact Module.subsingleton W.toAffine.CoordinateRing _

theorem eq_zero_of_smul_cechGen_mem {r : R} (h : r • cechGen W ∈ LinearMap.range (cechMap W)) :
    r = 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  obtain ⟨⟨a, b⟩, hab⟩ := h
  exact eq_zero_of_sub_eq_smul W a b r hab

noncomputable def cechCokernelEquiv :
    (Overlap W ⧸ LinearMap.range (cechMap W)) ≃ₗ[R] R :=
  (LinearEquiv.ofBijective ((LinearMap.range (cechMap W)).mkQ ∘ₗ
      LinearMap.toSpanSingleton R (Overlap W) (cechGen W))
    ⟨by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro r hr
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hr
      exact (Submodule.mem_bot R).2 (eq_zero_of_smul_cechGen_mem W hr),
    by
      rcases subsingleton_or_nontrivial R with hR | hR
      · have := subsingleton_of_subsingleton W
        intro q
        exact ⟨0, Subsingleton.elim _ _⟩
      intro q
      obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ q
      have hv : v ∈ cechSpan W := by rw [cechSpan_eq_top]; trivial
      obtain ⟨w, hw, s, hs, rfl⟩ := Submodule.mem_sup.1 hv
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hs
      refine ⟨r, ?_⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply,
        Submodule.mkQ_apply]
      rw [eq_comm, Submodule.Quotient.eq]
      simpa using hw⟩).symm

end Cohomology

end Weierstrass

end GroundTheory.Arith.Modular
