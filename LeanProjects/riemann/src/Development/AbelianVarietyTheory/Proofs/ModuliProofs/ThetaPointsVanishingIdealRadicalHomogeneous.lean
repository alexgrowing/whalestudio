import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.ThIdeal

theorem hasTh_unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {S : Scheme.{0}} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (h : t.HasTh x v) (c : R) (hc : IsUnit c) :
    t.HasTh x (fun a => c * v a) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, k1, k2, k3, k4, k5, k6, k7, k8⟩ := h3 p
  have hu : IsUnit (V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
    (hc.map _).map _
  obtain ⟨u', hu'⟩ : ∃ u' : Γ((Out.overRes (T := Over.mk x) V).left, ⊤)ˣ,
      u'.val = V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := hu
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, u' * u, k1, k2, k3, k4, k5, k6, k7, fun i => ?_⟩
  have e := k8 i
  have e1 : V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c * v i)) =
      V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
        V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) := by
    rw [map_mul]
    exact map_mul _ _ _
  refine e1.trans ?_
  rw [Units.val_mul, _root_.mul_assoc, hu']
  exact congrArg (fun y => V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * y) e

theorem coeff_scale {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ) :
    (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F).coeff e =
      MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial d c =>
    have hm : MvPolynomial.monomial d c ∈ MvPolynomial.homogeneousSubmodule σ R d.degree :=
      MvPolynomial.isHomogeneous_monomial c rfl
    rw [MvPolynomial.homogeneousComponent_of_mem hm]
    have : MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) (MvPolynomial.monomial d c) =
        Polynomial.C (MvPolynomial.eval₂Hom β w (MvPolynomial.monomial d c)) * Polynomial.X ^ d.degree := by
      simp only [MvPolynomial.eval₂Hom_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, RingHom.comp_apply, Finsupp.degree_apply]
      ring
    rw [this, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]

theorem component_eq_zero {R σ : Type} [CommRing R] (β : R →+* ℂ) (w : σ → ℂ)
    (F : MvPolynomial σ R) (e : ℕ)
    (h : ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂Hom β (fun i => c * w i) F = 0) :
    MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) = 0 := by
  rw [← coeff_scale]
  have : MvPolynomial.eval₂Hom ((Polynomial.C : ℂ →+* Polynomial ℂ).comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := {0}ᶜ) (fun c hc => ?_) (Set.finite_singleton (0 : ℂ)).infinite_compl
    have h1 := MvPolynomial.map_eval₂Hom ((Polynomial.C : ℂ →+* Polynomial ℂ).comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) (Polynomial.evalRingHom c) F
    rw [Set.mem_ofPred_eq, Polynomial.IsRoot.def, ← Polynomial.coe_evalRingHom, h1, ← h c hc]
    congr 2
    · ext r; simp
    · ext i; simp [_root_.mul_comm c]
  rw [this, Polynomial.coeff_zero]

theorem mem_thIdeal {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} (em : o →+* ℂ)
    (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (F : MvPolynomial (Ix g (N' ^ 2)) o) :
    F ∈ thIdeal em C ↔ ∀ t v, C t → t.HasTh (𝟙 _) v → MvPolynomial.eval₂Hom em v F = 0 := by
  simp only [thIdeal, Ideal.mem_iInf, RingHom.mem_ker, and_imp]

theorem thIdeal_radical_homogeneous_torsionFree :
    ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop), Function.Injective em → (thIdeal em C).IsRadical ∧ (∀ F ∈ thIdeal em C, ∀ e, MvPolynomial.homogeneousComponent e F ∈ thIdeal em C) ∧ ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ thIdeal em C → F ∈ thIdeal em C := by
  intro o _ g N' J b em C hem
  refine ⟨fun F hF => ?_, fun F hF e => ?_, fun c F hc hF => ?_⟩
  · obtain ⟨n, hn⟩ := hF
    rw [mem_thIdeal] at hn ⊢
    intro t v ht hv
    have := hn t v ht hv
    rw [map_pow] at this
    exact pow_eq_zero_iff'.mp this |>.1
  · rw [mem_thIdeal] at hF ⊢
    intro t v ht hv
    exact component_eq_zero em v F e fun c hc => hF t _ ht (hasTh_unit_mul hv c hc.isUnit)
  · rw [mem_thIdeal] at hF ⊢
    intro t v ht hv
    have := hF t v ht hv
    rw [map_mul, MvPolynomial.eval₂Hom_C] at this
    exact (mul_eq_zero.mp this).resolve_left ((map_ne_zero_iff em hem).mpr hc)

end GlobalTheory.ZM.ThIdeal
