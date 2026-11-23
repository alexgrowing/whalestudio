import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace GenSecDomain

theorem eval₂_mul_of_isHomogeneous {k S : Type*} [CommSemiring k] [CommSemiring S] {n : ℕ} (f : k →+* S)
    (x : Fin n → S) (a : S) {q : MvPolynomial (Fin n) k} {d : ℕ} (hq : q.IsHomogeneous d) :
    eval₂ f (fun l => x l * a) q = a ^ d * eval₂ f x q := by
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have h := hq (mem_support_iff.mp hm)
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (u : Fin n → R) :
    MvPolynomial.map f (linForm u) = linForm (fun j => f (u j)) := by
  simp [linForm, map_sum]

variable {k : Type} [Field k] {n : ℕ}

abbrev SecR (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) : Type :=
  SecAlg (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
    (X : Par e n → MvPolynomial (Par e n) k)

abbrev xc (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) (j : Fin n) : SecR Q e :=
  secCoord (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
    (X : Par e n → MvPolynomial (Par e n) k) j

section Point

variable (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime] (e : ℕ)

abbrev Fn : Type := FractionRing (MvPolynomial (Fin n) k ⧸ Q)

abbrev Tgt : Type := MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) (Fn Q))

abbrev Om : Type := FractionRing (Tgt Q e)

def gsub (c : Fin n → Fn Q) : MvPolynomial (Fin e × Fin n) k →ₐ[k] MvPolynomial (Fin e × Fin n) (Fn Q) :=
  aeval (genSubst (genPt Q) c)

def ρ (c : Fin n → Fn Q) : MvPolynomial (Par e n) k →+* Tgt Q e :=
  (MvPolynomial.map (gsub Q e c).toRingHom).comp
    ((sumAlgEquiv k (Fin n) (Fin e × Fin n)).toRingHom.comp
      (renameEquiv k (Equiv.sumComm (Fin e × Fin n) (Fin n))).toRingHom)

omit [Q.IsPrime] in
theorem ρ_X_inl (c : Fin n → Fn Q) (i : Fin e) (j : Fin n) :
    ρ Q e c (X (.inl (i, j))) = C (genSubst (genPt Q) c (i, j)) := by
  simp [ρ, gsub, sumAlgEquiv_X_inr]

omit [Q.IsPrime] in
theorem ρ_X_inr (c : Fin n → Fn Q) (j : Fin n) : ρ Q e c (X (.inr j)) = X j := by
  simp [ρ, gsub, sumAlgEquiv_X_inl]

omit [Q.IsPrime] in
theorem ρ_C (c : Fin n → Fn Q) (a : k) : ρ Q e c (C a) = C (C (algebraMap k (Fn Q) a)) := by
  simp [ρ, gsub, sumAlgEquiv_C_inl]

omit [Q.IsPrime] in
theorem ρ_injective (c : Fin n → Fn Q) (h : Function.Injective (gsub Q e c)) :
    Function.Injective (ρ Q e c) :=
  (MvPolynomial.map_injective _ h).comp
    ((sumAlgEquiv k (Fin n) (Fin e × Fin n)).injective.comp
      (renameEquiv k (Equiv.sumComm (Fin e × Fin n) (Fin n))).injective)

def sT : Tgt Q e := ∑ l, X l * C (C (genPt Q l))

def ι : Fn Q →+* Om Q e := (algebraMap (Tgt Q e) (Om Q e)).comp ((C : _ →+* Tgt Q e).comp C)

def xs (l : Fin n) : Om Q e := ι Q e (genPt Q l) * (algebraMap (Tgt Q e) (Om Q e) (sT Q e))⁻¹

def Ψt (c : Fin n → Fn Q) : MvPolynomial (Fin n) (MvPolynomial (Par e n) k) →+* Om Q e :=
  eval₂Hom ((algebraMap (Tgt Q e) (Om Q e)).comp (ρ Q e c)) (xs Q e)

omit [Q.IsPrime] in
theorem eval₂_genPt (p : MvPolynomial (Fin n) k) :
    eval₂ (algebraMap k (Fn Q)) (genPt Q) p = algebraMap _ (Fn Q) (Ideal.Quotient.mk Q p) := by
  have h : (eval₂Hom (algebraMap k (Fn Q)) (genPt Q)) =
      (algebraMap (MvPolynomial (Fin n) k ⧸ Q) (Fn Q)).comp (Ideal.Quotient.mk Q) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun l => ?_)
    · simp only [coe_eval₂Hom, eval₂_C, RingHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k ⧸ Q) (Fn Q)]
      rfl
    · simp [genPt]
  exact congrArg (fun f : MvPolynomial (Fin n) k →+* Fn Q => f p) h

theorem sT_ne_zero (j : Fin n) (hj : genPt Q j ≠ 0) : sT Q e ≠ 0 := by
  intro h
  have h' := congrArg (eval (Pi.single j 1)) h
  simp [sT, Pi.single_apply] at h'
  exact hj h'

theorem secIdeal_le_ker (hQh : IsHomogIdeal Q) (c : Fin n → Fn Q) (hc : ∑ j, c j * genPt Q j = 1)
    (hs : sT Q e ≠ 0) :
    secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
      (X : Par e n → MvPolynomial (Par e n) k) ≤ RingHom.ker (Ψt Q e c) := by
  have hs' : algebraMap (Tgt Q e) (Om Q e) (sT Q e) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Tgt Q e) (Om Q e))).mpr hs
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, RingHom.mem_ker, Ψt, coe_eval₂Hom, eval₂_map]
    have hcoef : ((algebraMap (Tgt Q e) (Om Q e)).comp (ρ Q e c)).comp C =
        (ι Q e).comp (algebraMap k (Fn Q)) := by
      ext a
      simp [ι, ρ_C]
    rw [hcoef, ← sum_homogeneousComponent q, eval₂_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    have hx : xs Q e = fun l => ι Q e (genPt Q l) * (algebraMap _ (Om Q e) (sT Q e))⁻¹ := rfl
    rw [hx, eval₂_mul_of_isHomogeneous _ _ _ (homogeneousComponent_isHomogeneous d q)]
    have h2 : eval₂ ((ι Q e).comp (algebraMap k (Fn Q))) (fun l => ι Q e (genPt Q l))
        (homogeneousComponent d q) =
        ι Q e (eval₂ (algebraMap k (Fn Q)) (genPt Q) (homogeneousComponent d q)) :=
      (eval₂_comp_left _ _ _ _).symm
    rw [h2, eval₂_genPt, Ideal.Quotient.eq_zero_iff_mem.mpr (hQh q hq d), map_zero, map_zero, mul_zero]
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    have h1 : ∑ l, C (c l) * C (genPt Q l) = (1 : MvPolynomial (Fin e × Fin n) (Fn Q)) := by
      rw [← C_1, ← hc, map_sum]
      simp_rw [C_mul]
    have key : ∑ l, genSubst (genPt Q) c (i, l) * C (genPt Q l) = 0 := by
      simp only [genSubst]
      rw [show ∑ l, (X (i, l) - (∑ m, X (i, m) * C (genPt Q m)) * C (c l)) * C (genPt Q l) =
          ∑ l, X (i, l) * C (genPt Q l) - (∑ m, X (i, m) * C (genPt Q m)) * ∑ l, C (c l) * C (genPt Q l) by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring]
      rw [h1, mul_one, sub_self]
    rw [SetLike.mem_coe, RingHom.mem_ker, secForm, linForm, map_sum]
    simp only [map_mul, Ψt, coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.comp_apply, ρ_X_inl, xs, ι]
    simp_rw [← mul_assoc, ← map_mul]
    rw [← Finset.sum_mul, ← map_sum, ← map_sum, key, map_zero, map_zero, zero_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, chartForm, linForm]
    simp only [map_sub, map_one, map_sum, map_mul, Ψt, coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.comp_apply,
      ρ_X_inr, xs, ι]
    simp_rw [← mul_assoc, ← map_mul]
    rw [← Finset.sum_mul, ← map_sum]
    have : ∑ l, X l * (C (C (genPt Q l)) : Tgt Q e) = sT Q e := rfl
    rw [this, mul_inv_cancel₀ hs', sub_self]

end Point

theorem exists_point (h₂ : IncidenceGeneric.Statement) (h₃ : IncIdealBelow.Statement)
    (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (hQ : IsProjPrime Q) (hg : IsChowForm Q (e + 1) g) :
    ∃ (Ω : Type) (_ : Field Ω) (Ψ : SecR Q e →+* Ω),
      Function.Injective (Ψ.comp (algebraMap (MvPolynomial (Par e n) k) (SecR Q e))) ∧
        ∀ l, X l ∉ Q → Ψ (xc Q e l) ≠ 0 := by
  have := hQ.isPrime
  obtain ⟨j0, hj0⟩ := hQ.isRelevant
  have hξ : ∀ l, X l ∉ Q → genPt Q l ≠ 0 := fun l hl =>
    (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin n) k ⧸ Q) (Fn Q))).mpr
      fun h => hl (Ideal.Quotient.eq_zero_iff_mem.mp h)
  set c : Fin n → Fn Q := Pi.single j0 (genPt Q j0)⁻¹ with hcdef
  have hc : ∑ j, c j * genPt Q j = 1 := by
    simp [c, Pi.single_apply, inv_mul_cancel₀ (hξ j0 hj0)]
  have hσ : Function.Injective (gsub Q e c) := by
    refine (injective_iff_map_eq_zero _).mpr fun p hp => ?_
    have hmem := (h₂ k n e Q c hc p).mpr hp
    rw [h₃ k n e Q g hQ hg] at hmem
    exact (Submodule.mem_bot _).mp hmem
  have hs := sT_ne_zero Q e j0 (hξ j0 hj0)
  have hle := secIdeal_le_ker Q e hQ.isHomog c hc hs
  refine ⟨Om Q e, inferInstance,
    Ideal.Quotient.lift _ (Ψt Q e c) (fun a ha => RingHom.mem_ker.mp (hle ha)), ?_, fun l hl => ?_⟩
  · intro r r' h
    refine ρ_injective Q e c hσ (IsFractionRing.injective (Tgt Q e) (Om Q e) ?_)
    have hr : ∀ r : MvPolynomial (Par e n) k, algebraMap _ (SecR Q e) r =
        Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
          (X : Par e n → MvPolynomial (Par e n) k)) (C r) := fun _ => rfl
    simp only [RingHom.comp_apply, hr, Ψt, Ideal.Quotient.lift_mk, coe_eval₂Hom, eval₂_C] at h
    exact h
  · show Ψt Q e c (X l) ≠ 0
    rw [Ψt, coe_eval₂Hom, eval₂_X, xs]
    refine mul_ne_zero ?_ (inv_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (Tgt Q e) (Om Q e))).mpr hs))
    rw [ι, RingHom.comp_apply, RingHom.comp_apply]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (Tgt Q e) (Om Q e))).mpr
      (by simpa using hξ l hl)

theorem secR_isDomain (h₁ : ChartDomain.Statement) (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ)
    (hQ : IsProjPrime Q) {Ω : Type} [Field Ω] (Ψ : SecR Q e →+* Ω)
    (hΨ : ∀ l, X l ∉ Q → Ψ (xc Q e l) ≠ 0) : IsDomain (SecR Q e) := by
  classical
  have hQk : ∀ a : k, C a ∈ Q → a = 0 := fun a ha => by
    by_contra h
    exact hQ.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem Q ha ((isUnit_iff_ne_zero.mpr h).map C))
  have hdom : ∀ j, X j ∉ Q → IsDomain (Localization.Away (xc Q e j)) := fun j hj =>
    (h₁ k n e Q j hQ.isPrime hQk hj).1
  have hx0 : ∀ j, X j ∈ Q → xc Q e j = 0 := fun j hj => by
    rw [xc, secCoord, Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_sup_left (Ideal.mem_sup_left ?_)
    have := Ideal.mem_map_of_mem (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)) hj
    simpa using this
  have hspan : Ideal.span (Set.range (xc Q e)) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun j => Ideal.Quotient.mk _ (C (X (.inr j))), ?_⟩
    have h : Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
        (X : Par e n → MvPolynomial (Par e n) k)) (chartForm X - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rw [map_sub, map_one, sub_eq_zero, chartForm, linForm, map_sum] at h
    simpa [xc, secCoord] using h
  have hchart : ∀ j (a : SecR Q e), algebraMap _ (Localization.Away (xc Q e j)) a = 0 →
      ∃ N : ℕ, xc Q e j ^ N * a = 0 := by
    intro j a h
    obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (xc Q e j)) _ a).mp h
    exact ⟨N, hN⟩
  have hne : ∀ j l, X j ∉ Q → X l ∉ Q → algebraMap _ (Localization.Away (xc Q e j)) (xc Q e l) ≠ 0 := by
    intro j l hj hl h
    obtain ⟨N, hN⟩ := hchart j _ h
    have h' := congrArg Ψ hN
    rw [map_mul, map_pow, map_zero] at h'
    exact mul_ne_zero (pow_ne_zero _ (hΨ j hj)) (hΨ l hl) h'
  have hzero : ∀ a : SecR Q e, (∀ j, X j ∉ Q → ∃ N : ℕ, xc Q e j ^ N * a = 0) → a = 0 := by
    intro a ha
    have h' : ∀ j, ∃ N : ℕ, xc Q e j ^ N * a = 0 := fun j => by
      by_cases hj : X j ∈ Q
      · exact ⟨1, by rw [hx0 j hj, pow_one, zero_mul]⟩
      · exact ha j hj
    choose N hN using h'
    have hM : ∀ j, xc Q e j ^ (∑ i, N i) * a = 0 := fun j => by
      have : N j ≤ ∑ i, N i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      rw [← Nat.sub_add_cancel this, pow_add, mul_assoc, hN, mul_zero]
    have hone := Ideal.span_pow_eq_top _ hspan (∑ i, N i)
    rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at hone
    obtain ⟨c, hc⟩ := hone
    rw [← one_mul a, ← hc, Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => by simp only [Function.comp_apply, mul_assoc, hM, mul_zero]
  obtain ⟨j0, hj0⟩ := hQ.isRelevant
  have hkill : ∀ a : SecR Q e, algebraMap _ (Localization.Away (xc Q e j0)) a = 0 → a = 0 := by
    intro a ha
    obtain ⟨N, hN⟩ := hchart j0 a ha
    refine hzero a fun j hj => hchart j a ?_
    have := hdom j hj
    have h := congrArg (algebraMap _ (Localization.Away (xc Q e j))) hN
    rw [map_mul, map_pow, map_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (hne j j0 hj hj0))
  have : Nontrivial (SecR Q e) := RingHom.domain_nontrivial Ψ
  have := hdom j0 hj0
  have : NoZeroDivisors (SecR Q e) := ⟨fun {a b} hab => by
    have h := congrArg (algebraMap _ (Localization.Away (xc Q e j0))) hab
    rw [map_mul, map_zero] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hkill a h)
    · exact Or.inr (hkill b h)⟩
  exact NoZeroDivisors.to_isDomain _

theorem map_secIdeal (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    (secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
        (X : Par e n → MvPolynomial (Par e n) k)).map
        (MvPolynomial.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n))) =
      secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n) := by
  have h1 : (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k))).map
      (MvPolynomial.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n))) =
      Q.map (MvPolynomial.map (algebraMap k (GenParField k e n))) := by
    rw [Ideal.map_map]
    congr 1
    refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, MvPolynomial.map_map,
      IsScalarTower.algebraMap_eq k (MvPolynomial (Par e n) k) (GenParField k e n), MvPolynomial.algebraMap_eq]
  have h2 : (Ideal.span (Set.range (secForm (X : Par e n → MvPolynomial (Par e n) k)))).map
      (MvPolynomial.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n))) =
      Ideal.span (Set.range (secForm (genPar k e n))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp only [Function.comp_apply, secForm, map_linForm]
    rfl
  have h3 : (Ideal.span {chartForm (X : Par e n → MvPolynomial (Par e n) k) - 1}).map
      (MvPolynomial.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n))) =
      Ideal.span {chartForm (genPar k e n) - 1} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one, chartForm, chartForm, map_linForm]
    rfl
  rw [secIdeal, secIdeal, Ideal.map_sup, Ideal.map_sup, h1, h2, h3]

end GenSecDomain

open GenSecDomain in

theorem GenSecDomain.proof (h₁ : ChartDomain.Statement) (h₂ : IncidenceGeneric.Statement)
    (h₃ : IncIdealBelow.Statement) : GenSecDomain.Statement := by
  intro k _ n e Q g hQ hg
  obtain ⟨Ω, _, Ψ, hinj, hΨ⟩ := exists_point h₂ h₃ Q e g hQ hg
  have := secR_isDomain h₁ Q e hQ Ψ hΨ
  have hJ := map_secIdeal Q e
  let M : Submonoid (MvPolynomial (Fin n) (MvPolynomial (Par e n) k)) :=
    (nonZeroDivisors (MvPolynomial (Par e n) k)).map
      (C : MvPolynomial (Par e n) k →+* MvPolynomial (Fin n) (MvPolynomial (Par e n) k))
  let φ : SecR Q e →+* GenSec k e Q :=
    Ideal.quotientMap _ (MvPolynomial.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n)))
      (hJ ▸ Ideal.le_comap_map)
  let := φ.toAlgebra
  let : Algebra (MvPolynomial (Fin n) (MvPolynomial (Par e n) k)) (MvPolynomial (Fin n) (GenParField k e n)) :=
    MvPolynomial.algebraMvPolynomial
  have := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (MvPolynomial (Par e n) k))
    (GenParField k e n)
  have key := IsLocalization.of_surjective M
    (MvPolynomial (Fin n) (GenParField k e n)) (S' := GenSec k e Q)
    (Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
      (X : Par e n → MvPolynomial (Par e n) k))) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n))))
      (genPar k e n))) Ideal.Quotient.mk_surjective
    (Ideal.quotientMap_comp_mk _).symm
    (by rw [Ideal.mk_ker, Ideal.mk_ker, ← hJ]; rfl)
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (GenSec k e Q)
    (M := M.map (Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
      (X : Par e n → MvPolynomial (Par e n) k)))) ?_
  rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => nonZeroDivisors.ne_zero hr (hinj ?_)
  rw [map_zero]
  exact (congrArg Ψ h0).trans (map_zero Ψ)

end

end GroundTheory.Heights₂.Heights.Vertical
