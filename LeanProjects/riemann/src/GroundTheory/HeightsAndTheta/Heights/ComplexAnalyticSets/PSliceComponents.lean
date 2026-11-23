import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceComponents
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartHomogenise
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartDehomog
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PMinimalPrimeHomog
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PLocalMultOrd
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PDehomogOrd
import GroundTheory.HeightsAndTheta.Heights.ChowForms.POrdPolynomialLocalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SliceComponents

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F : Type} [Field F] {n : ℕ}

theorem isHomogIdeal_sup_linForm {J : Ideal (MvPolynomial (Fin n) F)} (hJ : IsHomogIdeal J) (u : Fin n → F) :
    IsHomogIdeal (J ⊔ Ideal.span {linForm u}) := by
  rw [isHomogIdeal_iff_isHomogeneous_degree] at hJ ⊢
  refine hJ.sup (Ideal.homogeneous_span _ _ fun x hx => ?_)
  rw [Set.mem_singleton_iff.mp hx]
  exact ⟨1, (mem_homogeneousSubmodule _ _).mpr (ChartLocDomain.linForm_isHomogeneous u)⟩

theorem le_of_le_sup {V W : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F} (hV : IsHomogIdeal V)
    (hW : W.IsPrime) (hWh : IsHomogIdeal W) (ht : linForm t ∉ W) (h : V ≤ W ⊔ Ideal.span {linForm t - 1}) :
    V ≤ W := fun g hg => by
  rw [← sum_homogeneousComponent g]
  exact Ideal.sum_mem _ fun d _ => ChartDehomog.proof F n W t _ d hW hWh ht
    (homogeneousComponent_isHomogeneous d g) (h (hV g hg d))

theorem isPrime_sup {W : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F} (hW : W.IsPrime)
    (hH : IsHomogIdeal W) (ht : linForm t ∉ W) : (W ⊔ Ideal.span {linForm t - 1}).IsPrime := by
  set a : MvPolynomial (Fin n) F ⧸ W := Ideal.Quotient.mk W (linForm t) with ha_def
  have ha : a ≠ 0 := fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let A := Localization.Away a
  have hM := powers_le_nonZeroDivisors_of_noZeroDivisors ha
  have : IsDomain A := IsLocalization.isDomain_localization hM
  let v : A := IsLocalization.Away.invSelf a
  let φ : MvPolynomial (Fin n) F →ₐ[F] A :=
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ W) A).comp (Ideal.Quotient.mkₐ F W)
  have hφ : ∀ g, aeval (fun m => φ (X m)) g = φ g := fun g => by
    rw [← comp_aeval_apply]; simp
  let ψ : MvPolynomial (Fin n) F →ₐ[F] A := aeval fun m => v * φ (X m)
  have hhom : ∀ {g : MvPolynomial (Fin n) F} {k : ℕ}, g.IsHomogeneous k → ψ g = v ^ k * φ g :=
    fun hg => by rw [← hφ]; exact ChartLocDomain.aeval_mul_of_isHomogeneous hg _ _
  have hle : W ⊔ Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    refine sup_le (fun g hg => ?_) ?_
    · rw [RingHom.mem_ker, ← sum_homogeneousComponent g, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hhom (homogeneousComponent_isHomogeneous k g)]
      have : φ (homogeneousComponent k g) = 0 := by
        simp [φ, Ideal.Quotient.eq_zero_iff_mem.mpr (hH g hg k)]
      rw [this, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
        hhom (ChartLocDomain.linForm_isHomogeneous t), pow_one]
      have : φ (linForm t) = algebraMap _ A a := rfl
      rw [this, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]
  have hv : IsUnit v := IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf a)
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) F ⧸ W) A) := IsLocalization.injective A hM
  suffices e : RingHom.ker ψ = W ⊔ Ideal.span {linForm t - 1} by rw [← e]; exact RingHom.ker_isPrime _
  refine le_antisymm (fun g hg => ?_) hle
  obtain ⟨G, D, hG, hGg⟩ :=
    ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) g (ChartLocDomain.linForm_isHomogeneous t)
  have h1 := hle (Ideal.mem_sup_right hGg)
  rw [RingHom.mem_ker, map_sub, (RingHom.mem_ker).mp hg, sub_zero, hhom hG] at h1
  have h2 : algebraMap _ A (Ideal.Quotient.mk W G) = 0 := (hv.pow D).mul_right_eq_zero.mp h1
  have hGW : G ∈ W := Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h2.trans (map_zero _).symm))
  rw [show g = G - (G - g) by ring]
  exact sub_mem (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hGg)

theorem mem_support_divCycle {J W : Ideal (MvPolynomial (Fin n) F)} {u : Fin n → F} :
    W ∈ (divCycle J u).support ↔
      W ∈ relComps (J ⊔ Ideal.span {linForm u}) ∧ localMult (J ⊔ Ideal.span {linForm u}) W ≠ 0 := by
  classical
  simp only [divCycle, fundCycle, Finsupp.mem_support_iff, Finsupp.onFinset_apply]
  split_ifs with h <;> simp [h]

theorem divCycle_apply {J W : Ideal (MvPolynomial (Fin n) F)} {u : Fin n → F}
    (h : W ∈ relComps (J ⊔ Ideal.span {linForm u})) :
    divCycle J u W = localMult (J ⊔ Ideal.span {linForm u}) W := by
  classical
  simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
  rw [if_pos h]

theorem localMult_ne_zero {A : Type} [CommRing A] [IsNoetherianRing A] {J W : Ideal A} {x : A}
    (hW : W ∈ (J ⊔ Ideal.span {x}).minimalPrimes) : localMult (J ⊔ Ideal.span {x}) W ≠ 0 := by
  have := hW.1.1
  have hP : (W.map (Ideal.Quotient.mk J)).IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact le_sup_left.trans hW.1.2)
  intro h0
  have e := LocalMultOrd.proof A J W x hW
  rw [h0, Nat.cast_zero, eq_comm, Ring.ord, Module.length_eq_zero_iff,
    Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top] at e
  have hx : Ideal.Quotient.mk J x ∈ W.map (Ideal.Quotient.mk J) :=
    Ideal.mem_map_of_mem _ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mp e hx

theorem mem_support_iff {J W : Ideal (MvPolynomial (Fin n) F)} {u ℓ : Fin n → F}
    (hℓ : ∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) :
    W ∈ (divCycle J u).support ↔ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes ∧ linForm ℓ ∉ W := by
  refine ⟨fun h => ⟨(mem_support_divCycle.mp h).1.1, hℓ W h⟩, fun ⟨hm, hW⟩ => ?_⟩
  refine mem_support_divCycle.mpr ⟨⟨hm, ?_⟩, localMult_ne_zero hm⟩
  by_contra hr
  simp only [IsRelevant, not_exists, not_not] at hr
  exact hW (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hr j))

end SliceComponents

open SliceComponents in

theorem SliceComponents.proof : SliceComponents.Statement := by
  intro n J u ℓ hJ hℓ
  have := hJ.isPrime
  set K := J ⊔ Ideal.span {linForm u} with hKdef
  set L : Ideal (MvPolynomial (Fin n) ℂ) := Ideal.span {linForm ℓ - 1} with hLdef
  have hK : IsHomogIdeal K := isHomogIdeal_sup_linForm hJ.isHomog u
  have hK' : J ⊔ L ⊔ Ideal.span {linForm u} = K ⊔ L := sup_right_comm _ _ _
  have hsupp := fun W => mem_support_iff (W := W) hℓ
  have hhom : ∀ W ∈ K.minimalPrimes, IsHomogIdeal W := fun W hW => MinimalPrimeHomog.proof ℂ n K W hK hW

  have hchart : ∀ Q : Ideal _, Q.IsPrime → K ⊔ L ≤ Q →
      ∃ V, IsProjPrime V ∧ linForm ℓ ∉ V ∧ V ⊔ L = Q ∧ K ≤ V := fun Q hQ hKQ => by
    obtain ⟨V, hV, hℓV, hVQ, hVmax⟩ :=
      ChartHomogenise.proof ℂ n Q ℓ hQ (hKQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact ⟨V, hV, hℓV, hVQ, hVmax K hK (le_sup_left.trans hKQ)⟩
  have hmin : ∀ W ∈ (divCycle J u).support, W ⊔ L ∈ (K ⊔ L).minimalPrimes := fun W hW => by
    obtain ⟨hWm, hℓW⟩ := (hsupp W).mp hW
    have := hWm.1.1
    refine ⟨⟨isPrime_sup hWm.1.1 (hhom W hWm) hℓW, sup_le_sup_right hWm.1.2 _⟩, fun Q ⟨hQ, hKQ⟩ hQW => ?_⟩
    obtain ⟨V, hV, -, hVQ, hKV⟩ := hchart Q hQ hKQ
    have hVW : V ≤ W :=
      le_of_le_sup hV.isHomog hWm.1.1 (hhom W hWm) hℓW ((le_sup_left.trans hVQ.le).trans hQW)
    rw [← hVQ]
    exact sup_le_sup_right (hWm.2 ⟨hV.isPrime, hKV⟩ hVW) _
  refine ⟨fun W₁ h₁ W₂ h₂ (e : W₁ ⊔ L = W₂ ⊔ L) => ?_, ?_, fun W hW => ?_⟩
  · obtain ⟨hm₁, hℓ₁⟩ := (hsupp W₁).mp h₁
    obtain ⟨hm₂, hℓ₂⟩ := (hsupp W₂).mp h₂
    exact le_antisymm
      (le_of_le_sup (hhom W₁ hm₁) hm₂.1.1 (hhom W₂ hm₂) hℓ₂ (e ▸ le_sup_left))
      (le_of_le_sup (hhom W₂ hm₂) hm₁.1.1 (hhom W₁ hm₁) hℓ₁ (e.symm ▸ le_sup_left))
  · rw [hK']
    ext Q
    refine ⟨fun ⟨W, hW, hWQ⟩ => hWQ ▸ hmin W hW, fun hQ => ?_⟩
    have := hQ.1.1
    obtain ⟨V, hV, hℓV, hVQ, hKV⟩ := hchart Q hQ.1.1 hQ.1.2
    have := hV.isPrime
    obtain ⟨W, hWm, hWV⟩ := Ideal.exists_minimalPrimes_le hKV
    have hW : W ∈ (divCycle J u).support := (hsupp W).mpr ⟨hWm, fun h => hℓV (hWV h)⟩
    have hle : W ⊔ L ≤ Q := hVQ ▸ sup_le_sup_right hWV _
    exact ⟨W, hW, le_antisymm hle (hQ.2 (hmin W hW).1 hle)⟩
  · obtain ⟨hWm, hℓW⟩ := (hsupp W).mp hW
    have := hWm.1.1
    have hWL := isPrime_sup hWm.1.1 (hhom W hWm) hℓW
    have hJW : J ≤ W := le_sup_left.trans hWm.1.2
    have : (W.map (Ideal.Quotient.mk J)).IsPrime := Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJW)
    have hmapeq : (W ⊔ L).map (Ideal.Quotient.mk (J ⊔ L)) = W.map (Ideal.Quotient.mk (J ⊔ L)) := by
      have hL0 : L.map (Ideal.Quotient.mk (J ⊔ L)) = ⊥ :=
        (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker]; exact le_sup_right)
      rw [Ideal.map_sup, hL0, sup_bot_eq]
    have hP' : ((W ⊔ L).map (Ideal.Quotient.mk (J ⊔ L))).IsPrime := Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact sup_le_sup_right hJW _)
    have : (W.map (Ideal.Quotient.mk (J ⊔ L))).IsPrime := hmapeq ▸ hP'
    rw [divCycle_apply (mem_support_divCycle.mp hW).1]
    have e₁ := LocalMultOrd.proof _ J W (linForm u) hWm
    have e₂ := DehomogOrd.proof OrdPolynomialLocalization.proof ℂ n J W ℓ hJ.isHomog (hhom W hWm) hJW hℓW
      (linForm u) 1 (ChartLocDomain.linForm_isHomogeneous u)
    have e₃ := LocalMultOrd.proof _ (J ⊔ L) (W ⊔ L) (linForm u) (hK' ▸ hmin W hW)
    have e₄ := ord_atPrime_congr hmapeq (Ideal.Quotient.mk (J ⊔ L) (linForm u))
    exact_mod_cast e₃.trans (e₄.trans (e₂.symm.trans e₁.symm))

end

end GroundTheory.Heights₂.Heights
