import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassSt
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSubMemOfInert

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

section NoF

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem conjO_coe (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  rw [conjO_coe, conjO_coe, star_star]

theorem conjIdeal_eq_comap (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.comap (conjO K) := by
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro r ⟨s, hs, hrs⟩
    have hr : conjO K r = s := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      have h2 : (r : K) = star (s : K) := hrs
      rw [h2, star_star]
    show conjO K r ∈ P
    rw [hr]
    exact hs
  · intro x hx
    apply Ideal.subset_span
    refine ⟨conjO K x, hx, ?_⟩
    show (x : K) = star ((conjO K x : 𝓞 K) : K)
    rw [conjO_coe, star_star]

theorem exists_sub_conjO_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ θ : 𝓞 K, θ - conjO K θ ∉ P := by
  obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
  refine ⟨θ, ?_⟩
  have hθt : conjO K θ = t := by
    apply RingOfIntegers.ext
    rw [conjO_coe]
    exact ht.symm
  rwa [hθt]

omit [StarRing K] in
theorem absNorm_eq_card (I : Ideal (𝓞 K)) : Ideal.absNorm I = Nat.card (𝓞 K ⧸ I) := by
  first
  | rfl
  | (rw [Ideal.absNorm_apply]; rfl)
  | (rw [Ideal.absNorm_apply, Submodule.cardQuot_apply])

theorem conjIdeal_isMaximal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).IsMaximal := by
  rw [conjIdeal_eq_comap]
  haveI := hP
  exact Ideal.comap_isMaximal_of_surjective (conjO K) (fun y => ⟨conjO K y, conjO_conjO y⟩)

theorem conjIdeal_conjIdeal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = P := by
  ext x
  simp only [conjIdeal_eq_comap, Ideal.mem_comap, conjO_conjO]

theorem conjIdeal_eq_map (P : Ideal (𝓞 K)) : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.map (conjO K) := by
  rw [conjIdeal_eq_comap]
  apply le_antisymm
  · intro x hx
    have h := Ideal.mem_map_of_mem (conjO K) (show conjO K x ∈ P from hx)
    rwa [conjO_conjO] at h
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simpa only [Ideal.mem_comap, conjO_conjO] using hx

theorem absNorm_conjIdeal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (P : Ideal (𝓞 K)) :
    Ideal.absNorm (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = Ideal.absNorm P := by
  rw [absNorm_eq_card, absNorm_eq_card]
  let e : 𝓞 K ≃+* 𝓞 K :=
    { conjO K with
      invFun := conjO K
      left_inv := fun x => conjO_conjO x
      right_inv := fun x => conjO_conjO x }
  have h : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [conjIdeal_eq_map]
    rfl
  exact (Nat.card_congr (Ideal.quotientEquiv P _ e h).toEquiv).symm

theorem exists_sq_absNorm_of_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    ∃ q : ℕ, Ideal.absNorm P = q ^ 2 := by
  rw [conjIdeal_eq_comap] at hc
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [absNorm_eq_card]
  exact SplitPrimeIdeals.exists_sq_card_quot conjO_conjO hP hc hθ

end NoF

section WithF

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem conjO_eq_iff_mem_range (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (x : 𝓞 K) :
    conjO K x = x ↔ x ∈ Set.range (algebraMap (𝓞 F) (𝓞 K)) := by
  constructor
  · intro hx
    have hfix : star (x : K) = x := by rw [← conjO_coe, hx]
    obtain ⟨a, ha⟩ := (hF _).1 hfix
    have hint : IsIntegral ℤ (algebraMap F K a) := by
      rw [ha]
      first
      | exact RingOfIntegers.isIntegral_coe x
      | exact x.2
    have ha' : IsIntegral ℤ a := (isIntegral_algebraMap_iff (algebraMap F K).injective).1 hint
    refine ⟨⟨a, ha'⟩, ?_⟩
    apply RingOfIntegers.ext
    show algebraMap F K a = (x : K)
    exact ha
  · rintro ⟨y, rfl⟩
    apply RingOfIntegers.ext
    rw [conjO_coe]
    have hy : ((algebraMap (𝓞 F) (𝓞 K) y : 𝓞 K) : K) = algebraMap F K (y : F) := rfl
    rw [hy]
    exact (hF _).2 ⟨_, rfl⟩

theorem comap_eq_comap_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P Q : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hQ : Q.IsMaximal) :
    P.comap (algebraMap (𝓞 F) (𝓞 K)) = Q.comap (algebraMap (𝓞 F) (𝓞 K)) ↔ Q = P ∨ Q = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  rw [conjIdeal_eq_comap]
  exact SplitPrimeIdeals.comap_eq_comap_iff conjO_conjO (conjO_eq_iff_mem_range hF) hP hQ

theorem exists_maximal_over (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 := by
  haveI := h𝔭
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 K)) := by
    first
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
    | exact FaithfulSMul.algebraMap_injective _ _
    | (intro a b hab
       apply RingOfIntegers.ext
       apply (algebraMap F K).injective
       exact congrArg (fun z : 𝓞 K => (z : K)) hab)
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔭 := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
    exact bot_le
  exact Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭 hker

theorem absNorm_comap_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 = Ideal.absNorm P := by
  rw [conjIdeal_eq_comap] at hc
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [absNorm_eq_card, absNorm_eq_card]
  exact SplitPrimeIdeals.card_quot_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ

theorem absNorm_comap_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) = Ideal.absNorm P := by
  rw [conjIdeal_eq_comap] at hc
  rw [absNorm_eq_card, absNorm_eq_card]
  exact SplitPrimeIdeals.card_quot_split conjO_conjO (conjO_eq_iff_mem_range hF) hP hc

theorem etaF_comap (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    etaF K F (P.comap (algebraMap (𝓞 F) (𝓞 K))) = if Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P then -1 else 1 := by
  rw [conjIdeal_eq_comap]
  unfold etaF
  by_cases hc : P.comap (conjO K) = P
  · obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
    rw [SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ, if_pos hP.isPrime,
      if_pos hc]
  · rw [if_neg (SplitPrimeIdeals.not_isPrime_map_of_split conjO_conjO (conjO_eq_iff_mem_range hF) hP hc),
      if_neg hc]

end WithF

end Formalism.HermitianLattices.Ext.L3
