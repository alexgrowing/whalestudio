import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.EvRing

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

variable (p Ω) in

def zpH : ℤ_[p] →+* Ω := (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp HahnSeries.C)

theorem zp_eq (z : ℤ_[p]) : zp Ω z = zpH p Ω z := rfl

theorem thL_coeff (a : Lau p) (r : ℤ) : (thL a).coeff r = (r : ℤ_[p]) * a.coeff r := rfl

theorem thL_mul (a b : Lau p) : thL (a * b) = thL a * b + a * thL b := by
  ext r
  have hs : (thL a).support ⊆ a.support := fun i hi h => hi (by simp [thL_coeff, h])
  have ht : (thL b).support ⊆ b.support := fun i hi h => hi (by simp [thL_coeff, h])
  rw [HahnSeries.coeff_add, thL_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul_left' a.isPWO_support hs,
    HahnSeries.coeff_mul_right' b.isPWO_support ht, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_addAntidiagonal] at hij
  rw [thL_coeff, thL_coeff, ← hij.2.2]
  push_cast
  ring

theorem thL_neg (a : Lau p) : thL (-a) = -thL a := by
  ext r
  simp [thL_coeff]

theorem ev_of_fintype {ι : Type} [Fintype ι] (ψ : O0 p →+* Ω) (c : ℤ → Ω) (x x' : Ω) (e : ι → Ω)
    (a : ι → Lau p) (he : ∀ t, IsInt p (e t) ∧ IsAlgZp p (e t))
    (hc : ∀ r, c r = ∑ t, e t * zp Ω ((a t).coeff r))
    (hx : x = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)))
    (hx' : x' = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t)))) : Ev ψ c x x' := by
  let σ := Fintype.equivFin ι
  refine ⟨Fintype.card ι, e ∘ σ.symm, a ∘ σ.symm, fun t => he _, fun r => ?_, ?_, ?_⟩
  · rw [hc r]; exact (Equiv.sum_comp σ.symm (fun t => e t * zp Ω ((a t).coeff r))).symm
  · rw [hx]; exact (Equiv.sum_comp σ.symm (fun t => e t * ψ (algebraMap (Lau p) (O0 p) (a t)))).symm
  · rw [hx']; exact (Equiv.sum_comp σ.symm (fun t => e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t))))).symm

theorem repr {d : ℕ} (e : Fin d → Ω) (a : Fin d → Lau p) (C : HahnSeries ℤ Ω)
    (h : ∀ r, C.coeff r = ∑ t, e t * zp Ω ((a t).coeff r)) :
    C = ∑ t, HahnSeries.C (e t) * (a t).map (zpH p Ω).toNonUnitalRingHom := by
  ext r
  rw [h r, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.map_coeff]
  rfl

theorem isAlgZp_mul {x y : Ω} (hx : IsAlgZp p x) (hy : IsAlgZp p y) : IsAlgZp p (x * y) := by
  letI : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ z : Ω, IsAlgZp p z ↔ IsAlgebraic ℤ_[p] z := by
    intro z; simp only [IsAlgZp, IsAlgebraic, Polynomial.aeval_map_algebraMap]
  rw [key] at hx hy ⊢
  exact hx.mul hy

theorem isAlgZp_gal (g : Gal p Ω) {x : Ω} (hx : IsAlgZp p x) : IsAlgZp p (g x) := by
  obtain ⟨P, hP, h⟩ := hx
  exact ⟨P, hP, by rw [Polynomial.aeval_algHom_apply, h, map_zero]⟩

end GlobalTheory.Glue.EvRing

namespace GlobalTheory.Glue.EvRing

open GlobalTheory.K5.Basic in

theorem ev_ring : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ →
    (∀ (C D : HahnSeries ℤ Ω) (x x' y y' : Ω), Ev ψ C.coeff x x' → Ev ψ D.coeff y y' →
      Ev ψ (C * D).coeff (x * y) (x' * y + x * y') ∧ Ev ψ (C + D).coeff (x + y) (x' + y') ∧
      Ev ψ (C - D).coeff (x - y) (x' - y')) ∧
    (∀ (c : ℤ → Ω) (x x' : Ω), Ev ψ c x x' → IsInt p x ∧ IsInt p x' ∧ (∃ C : HahnSeries ℤ Ω, C.coeff = c) ∧
      (∃ x'', Ev ψ (fun r => (r : Ω) * c r) x' x'') ∧
      (∀ e : Ω, IsInt p e → IsAlgZp p e → Ev ψ (fun r => e * c r) (e * x) (e * x')) ∧
      ∀ g : Gal p Ω, g (T.qq n) = T.qq n → Ev ψ (fun r => g (c r)) (g x) (g x')) := by
  intro p hp Ω _ _ _ T n ψ hreb
  refine ⟨?_, ?_⟩
  · rintro C D x x' y y' ⟨d, e, a, he, hc, hx, hx'⟩ ⟨d', f, b, hf, hd, hy, hy'⟩
    refine ⟨?_, ?_, ?_⟩
    · refine ev_of_fintype (ι := Fin d × Fin d') ψ _ _ _ (fun ts => e ts.1 * f ts.2)
        (fun ts => a ts.1 * b ts.2) (fun ts => ⟨IsIntegral.mul (he _).1 (hf _).1, isAlgZp_mul (he _).2 (hf _).2⟩)
        (fun r => ?_) ?_ ?_
      · rw [repr e a C hc, repr f b D hd, Finset.sum_mul_sum, HahnSeries.coeff_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [HahnSeries.coeff_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [show HahnSeries.C (e t) * (a t).map (zpH p Ω).toNonUnitalRingHom *
            (HahnSeries.C (f s) * (b s).map (zpH p Ω).toNonUnitalRingHom) =
            HahnSeries.C (e t * f s) * (a t * b s).map (zpH p Ω).toNonUnitalRingHom by
          rw [HahnSeries.map_mul, map_mul]; ring]
        rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.map_coeff]
        rfl
      · rw [hx, hy, Finset.sum_mul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
        simp only [map_mul]
        ring
      · rw [hx, hx', hy, hy', Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib,
          Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [thL_mul, map_add, map_mul]
        ring
    · refine ev_of_fintype (ι := Fin d ⊕ Fin d') ψ _ _ _ (Sum.elim e f) (Sum.elim a b)
        (by rintro (t | t) <;> simp [he, hf]) (fun r => ?_) ?_ ?_
      · simp [Fintype.sum_sum_type, hc, hd]
      · simp [Fintype.sum_sum_type, hx, hy]
      · simp [Fintype.sum_sum_type, hx', hy']
    · refine ev_of_fintype (ι := Fin d ⊕ Fin d') ψ _ _ _ (Sum.elim e f) (Sum.elim a fun s => -b s)
        (by rintro (t | t) <;> simp [he, hf]) (fun r => ?_) ?_ ?_
      · simp [Fintype.sum_sum_type, hc, hd, zp_eq, sub_eq_add_neg]
      · simp [Fintype.sum_sum_type, hx, hy, sub_eq_add_neg]
      · simp [Fintype.sum_sum_type, hx', hy', thL_neg, sub_eq_add_neg]
  · rintro c x x' ⟨d, e, a, he, hc, hx, hx'⟩
    have hq : IsIntegral (O0 p) (T.qq n) :=
      IsIntegral.of_pow (pow_pos hp.out.pos n) (by rw [qq_pow]; exact isIntegral_algebraMap)
    have hmem : ∀ y, ψ y ∈ Algebra.adjoin (O0 p) {T.qq n} := fun y => by
      have : ψ y ∈ ψ.range := ⟨y, rfl⟩
      rw [hreb.rng] at this
      exact this
    have hint : ∀ y, IsInt p (ψ y) := fun y => adjoin_le_integralClosure hq (hmem y)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx]; exact IsIntegral.sum _ fun t _ => IsIntegral.mul (he t).1 (hint _)
    · rw [hx']; exact IsIntegral.sum _ fun t _ => IsIntegral.mul (he t).1 (hint _)
    · refine ⟨∑ t, HahnSeries.C (e t) * (a t).map (zpH p Ω).toNonUnitalRingHom, funext fun r => ?_⟩
      rw [hc r, HahnSeries.coeff_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.map_coeff]
      rfl
    · refine ⟨_, ev_of_fintype ψ _ x' _ e (fun t => thL (a t)) he (fun r => ?_) hx' rfl⟩
      rw [hc r, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [thL_coeff, zp_eq, zp_eq, map_mul, map_intCast]
      ring
    · intro e0 hi ha
      refine ev_of_fintype ψ _ _ _ (fun t => e0 * e t) a
        (fun t => ⟨IsIntegral.mul hi (he t).1, isAlgZp_mul ha (he t).2⟩) (fun r => ?_) ?_ ?_
      · rw [hc r, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      · rw [hx, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      · rw [hx', Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
    · intro g hg
      have hfix : ∀ y, g (ψ y) = ψ y := fun y =>
        (AlgHom.eqOn_adjoin_iff (φ := (g : Ω →ₐ[O0 p] Ω)) (ψ := AlgHom.id (O0 p) Ω) (s := {T.qq n})).2
          (by intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact hg) (hmem y)
      refine ev_of_fintype ψ _ _ _ (fun t => g (e t)) a
        (fun t => ⟨isInt_gal g (he t).1, isAlgZp_gal g (he t).2⟩) (fun r => ?_) ?_ ?_
      · rw [hc r, map_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [map_mul]
        congr 1
        exact g.commutes _
      · rw [hx, map_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [map_mul, hfix]
      · rw [hx', map_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [map_mul, hfix]

end GlobalTheory.Glue.EvRing
