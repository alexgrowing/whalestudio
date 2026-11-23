import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section Local

variable {A : Type*} [CommRing A]

theorem mem_minimalPrimes_of_mul_mem {J J' W : Ideal A} {s t : A} (hs : s ∉ W) (ht : t ∉ W)
    (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) (hW : W ∈ J.minimalPrimes) :
    W ∈ J'.minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  refine ⟨⟨hWp, fun x hx => ?_⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, fun x hx => ?_⟩ hQW⟩
  · exact (hWp.mem_or_mem (hW.1.2 (htJ x hx))).resolve_left ht
  · exact (hQ.1.mem_or_mem (hQ.2 (hsJ x hx))).resolve_left (fun h => hs (hQW h))

theorem length_localized_eq_of_le {J J'' W : Ideal A} [W.IsPrime] (hle : J ≤ J'')
    (h : ∀ x ∈ J'', ∃ t ∉ W, t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J'')) := by
  let q : (A ⧸ J) →ₗ[A] (A ⧸ J'') := Submodule.factor hle
  let f := LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J)
  let g := LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J'')
  let m := IsLocalizedModule.map W.primeCompl f g q
  have hinj : Function.Injective m := by
    apply IsLocalizedModule.injective_of_map_zero W.primeCompl f
    intro x hx
    rw [IsLocalizedModule.map_apply] at hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective J x
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff W.primeCompl g).mp hx
    have hsy : (s : A) * y ∈ J'' := by
      have : (s : A) • (Submodule.mkQ J'' y) = 0 := hs
      rwa [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul] at this
    obtain ⟨t, ht, hty⟩ := h _ hsy
    refine (IsLocalizedModule.eq_zero_iff W.primeCompl f).mpr ⟨⟨t * s, W.primeCompl.mul_mem ht s.2⟩, ?_⟩
    show ((t * s : A)) • (Submodule.mkQ J y) = 0
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      mul_assoc]
    exact hty
  have hsurj : Function.Surjective m :=
    IsLocalizedModule.map_surjective W.primeCompl f g q (Submodule.factor_surjective hle)
  exact ((LinearEquiv.ofBijective m ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq

theorem length_localized_eq_of_mul_mem {J J' W : Ideal A} [W.IsPrime] {s t : A} (hs : s ∉ W)
    (ht : t ∉ W) (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J')) := by
  have key : ∀ {J J' : Ideal A} {t : A}, t ∉ W → (∀ x ∈ J', t * x ∈ J) →
      ∀ x ∈ J ⊔ J', ∃ t ∉ W, t * x ∈ J := by
    intro J J' t ht htJ x hx
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨t, ht, by rw [mul_add]; exact J.add_mem (J.mul_mem_left t ha) (htJ a' ha')⟩
  rw [length_localized_eq_of_le le_sup_left (key ht htJ),
    length_localized_eq_of_le le_sup_left (key hs hsJ), sup_comm]

end Local

section Divisors

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem divCycle_eq_of_mul_sub_mem {P : Ideal (MRing ι R)} {f g u v : MRing ι R}
    {W : Ideal (MRing ι R)} (hu : u ∉ W) (hv : v ∉ W) (h : u * f - v * g ∈ P) :
    divCycle P f W = divCycle P g W := by
  have h1 : ∀ x ∈ P ⊔ Ideal.span {f}, u * x ∈ P ⊔ Ideal.span {g} := by
    intro x hx
    obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have e : u * (p + c * f) = (u * p + c * (u * f - v * g)) + (c * v) * g := by ring
    rw [e]
    exact Submodule.add_mem_sup (P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h))
      (Ideal.mem_span_singleton'.mpr ⟨c * v, rfl⟩)
  have h2 : ∀ x ∈ P ⊔ Ideal.span {g}, v * x ∈ P ⊔ Ideal.span {f} := by
    intro x hx
    obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have e : v * (p + c * g) = (v * p - c * (u * f - v * g)) + (c * u) * f := by ring
    rw [e]
    exact Submodule.add_mem_sup (P.sub_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h))
      (Ideal.mem_span_singleton'.mpr ⟨c * u, rfl⟩)
  unfold divCycle
  by_cases hf : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W
  · have hg : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W :=
      ⟨mem_minimalPrimes_of_mul_mem hu hv h1 h2 hf.1, hf.2⟩
    rw [dif_pos hf, dif_pos hg]
    have : W.IsPrime := hf.1.1.1
    unfold multAt
    rw [length_localized_eq_of_mul_mem hu hv h1 h2]
  · have hg : ¬ (W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W) := fun hg =>
      hf ⟨mem_minimalPrimes_of_mul_mem hv hu h2 h1 hg.1, hg.2⟩
    rw [dif_neg hf, dif_neg hg]

theorem le_and_isRelevant_of_divCycle_ne_zero {P : Ideal (MRing ι R)} {f : MRing ι R}
    {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) : W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact ⟨hW.1.1.1, le_sup_left.trans hW.1.1.2, hW.2⟩
  · exact absurd rfl h

end Divisors

section Vertical

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem IsVerticalDivisor.of_unit_off_special {P : Ideal (MRing ι O)} {ϖ : O} {b : K → ℤ}
    {f g : MRing ι O}
    (degrees : ∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
      (fun k => (bf k : ℤ) - bg k) = b)
    (hf : f ∉ P) (hg : g ∉ P)
    (hunit : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
      (C ϖ : MRing ι O) ∉ W → ∃ u v : MRing ι O, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P) :
    IsVerticalDivisor P ϖ b f g where
  degrees := degrees
  num_not_mem := hf
  den_not_mem := hg
  unit_off_special := hunit
  vertical := by
    intro W hW
    by_contra hϖ
    have hsupp : W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
      by_cases h1 : divCycle P f W = 0
      · have h2 : divCycle P g W ≠ 0 := by
          intro h2; apply hW; unfold ratDiv; rw [h1, h2, sub_zero]
        exact le_and_isRelevant_of_divCycle_ne_zero h2
      · exact le_and_isRelevant_of_divCycle_ne_zero h1
    obtain ⟨u, v, hu, hv, h⟩ := hunit W hsupp.1 hsupp.2.1 hsupp.2.2 hϖ
    apply hW
    unfold ratDiv
    rw [divCycle_eq_of_mul_sub_mem hu hv h, sub_self]

end Vertical

section Graded

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R] {τ : Type*}

end Graded

section BlowUp

variable {O : Type*} [CommRing O]

abbrev TwoByTwo : Fin 2 → Type := fun _ => Fin 2

def blowUpParam (ϖ : O) : (Σ k : Fin 2, TwoByTwo k) → MvPolynomial (Fin 4) O :=
  fun v => ![![C ϖ * X 0 * X 2, X 1 * X 2], ![X 0 * X 3, X 1 * X 3]] v.1 v.2

def blowUpWeight : Fin 4 → Fin 2 → ℕ := ![0, 0, Pi.single 0 1, Pi.single 1 1]

def blowUpIdeal (ϖ : O) : Ideal (MRing TwoByTwo O) := RingHom.ker (aeval (blowUpParam ϖ))

end BlowUp

section BlowUpModel

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end BlowUpModel

section Nodal

variable {O : Type*} [CommRing O] [IsDomain O]

abbrev TwoByThree : Fin 2 → Type := fun _ => Fin 3

def nodalParam (ϖ : O) : (Σ k : Fin 2, TwoByThree k) → MvPolynomial (Fin 3) O :=
  fun v => ![![X 1 * X 0, X 1 * X 0 ^ 2, X 1 * (1 - C ϖ * X 0 ^ 3)],
    ![X 2 * (C ϖ * X 0 ^ 2), X 2 * X 0, X 2 * (C ϖ ^ 2 * X 0 ^ 3 - 1)]] v.1 v.2

def nodalWeight : Fin 3 → Fin 2 → ℕ := ![0, Pi.single 0 1, Pi.single 1 1]

def nodalIdeal (ϖ : O) : Ideal (MRing TwoByThree O) := RingHom.ker (aeval (nodalParam ϖ))

def nodeParam : (Σ k : Fin 2, TwoByThree k) → MvPolynomial (Fin 3) O :=
  fun v => ![![0, 0, X 1], ![0, 0, -X 2]] v.1 v.2

end Nodal

end

end GroundTheory.Heights₂.Heights.NumbersDVR
