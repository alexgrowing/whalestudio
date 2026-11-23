import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldFinrankPowPrincipal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulFinrankMemDifferentIdeal

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayDiscr

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem exists_ideal {L' : Type} [Field L'] [NumberField L'] [Algebra K L'] [Algebra L' L] [IsScalarTower K L' L]
    [IsGalois K L'] {𝔪 : Ideal (𝓞 K)} (h : IsRayField K L 𝔪) (σ : L ≃ₐ[K] L) :
    ∃ I : Ideal (𝓞 K), I ≠ 0 ∧ IsCoprime I 𝔪 ∧ (∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = χ σ) ∧
      ∀ χ : (L' ≃ₐ[K] L') →* ℂˣ, heckeIdeal L' χ I = χ (AlgEquiv.restrictNormalHom L' σ) := by
  obtain ⟨hab, hun, hgen, -⟩ := h
  have hσ : σ ∈ Subgroup.closure _ := hgen ▸ Subgroup.mem_top σ
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨𝔭, hp, hx⟩ := hx
    refine ⟨𝔭.asIdeal, 𝔭.ne_bot, ?_, fun χ => ?_, fun χ => ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      have := 𝔭.isMaximal.eq_of_le hne le_sup_left
      exact hp (Ideal.dvd_iff_le.2 (this ▸ le_sup_right))
    · rw [GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hun 𝔭 hp) hx]
    · rw [GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L' χ (GlobalTheory.RayMaximal.unramIn_of_tower (hun 𝔭 hp))
        (GlobalTheory.RayMaximal.isFrob_restrictNormal hx)]
      rfl
  | one =>
    exact ⟨1, one_ne_zero, isCoprime_one_left, fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top, map_one, Units.val_one],
      fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top, map_one, map_one, Units.val_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨I, hI, hc, h1, h2⟩ := hx
    obtain ⟨J, hJ, hc', h3, h4⟩ := hy
    refine ⟨I * J, mul_ne_zero hI hJ, hc.mul_left hc', fun χ => ?_, fun χ => ?_⟩
    · rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hI hJ, h1, h3, map_mul, Units.val_mul]
    · rw [GlobalTheory.NT.Model.heckeIdeal_mul L' χ hI hJ, h2, h4, map_mul, map_mul, Units.val_mul]
  | inv x _ hx =>
    obtain ⟨I, hI, hc, h1, h2⟩ := hx
    have e : x⁻¹ = x ^ (Nat.card (L ≃ₐ[K] L) - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one']
    refine ⟨I ^ (Nat.card (L ≃ₐ[K] L) - 1), pow_ne_zero _ hI, hc.pow_left, fun χ => ?_, fun χ => ?_⟩
    · rw [RayExp.heckeIdeal_pow L χ hI, h1, e, map_pow, Units.val_pow_eq_pow_val]
    · rw [RayExp.heckeIdeal_pow L' χ hI, h2, e, map_pow, map_pow, Units.val_pow_eq_pow_val]

theorem pow_absNorm_sub_one (𝔭 : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ∉ 𝔭.asIdeal) :
    x ^ (Ideal.absNorm 𝔭.asIdeal - 1) - 1 ∈ 𝔭.asIdeal := by
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  let _ := Fintype.ofFinite (𝓞 K ⧸ 𝔭.asIdeal)
  let _ := Ideal.Quotient.field 𝔭.asIdeal
  rw [← Ideal.Quotient.eq, map_pow, map_one, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one _ (mt Ideal.Quotient.eq_zero_iff_mem.1 hx)

theorem inertia_pow (hR : RayField) (𝔭 : HeightOneSpectrum (𝓞 K)) {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥)
    (hp : ¬ 𝔭.asIdeal ∣ 𝔪) (h : IsRayField K L (𝔭.asIdeal * 𝔪)) {σ : L ≃ₐ[K] L} (hσ : InInertia L 𝔭 σ) :
    σ ^ (Ideal.absNorm 𝔭.asIdeal - 1) = 1 := by
  obtain ⟨L', _, _, _, _, h'⟩ := hR K 𝔪 hm
  have := h.1
  obtain ⟨f⟩ := nonempty_algHom_of_isRay_of_dvd (L := L) (L' := L') (mul_ne_zero 𝔭.ne_bot hm) (dvd_mul_left 𝔪 _) h.2 h'
  let _ := f.toRingHom.toAlgebra
  have : IsScalarTower K L' L := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  obtain ⟨I, hI, hc, h1, h2⟩ := exists_ideal (L' := L') h σ
  have hres : AlgEquiv.restrictNormalHom L' σ = 1 := by
    obtain ⟨P, hP, hPo, hx⟩ := hσ
    refine h'.1 𝔭 hp _ ⟨P.under (𝓞 L'), inferInstance, inferInstance, fun x => ?_⟩
    have h1 : algebraMap (𝓞 L') (𝓞 L) (AlgEquiv.restrictNormalHom L' σ • x) = σ • algebraMap (𝓞 L') (𝓞 L) x :=
      RingOfIntegers.ext (σ.restrictNormal_commutes L' x)
    rw [Ideal.mem_under, map_sub, h1]
    exact hx _
  obtain ⟨α, β, ⟨-, hb, -, hb', hab, hpos⟩, e⟩ := (h'.2.2 I hI hc.of_mul_right_right).1 fun χ => by
    rw [h2, hres, map_one, Units.val_one]
  obtain ⟨x, rfl⟩ : β ∣ α := by
    rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton, ← e]
    exact dvd_mul_left _ _
  have hb0 : Ideal.span {β} ≠ 0 := by simpa using hb
  obtain rfl : I = Ideal.span {x} := by
    rw [← Ideal.span_singleton_mul_span_singleton, mul_comm] at e
    exact mul_left_cancel₀ hb0 e
  have hx0 : x ≠ 0 := by simpa using hI
  have hx1 : x - 1 ∈ 𝔪 := by
    rw [← Ideal.dvd_span_singleton] at hab ⊢
    rw [show β * x - β = β * (x - 1) by ring, ← Ideal.span_singleton_mul_span_singleton] at hab
    exact hb'.symm.dvd_of_dvd_mul_left hab
  have hxp : x ∉ 𝔭.asIdeal := fun hx => 𝔭.prime.not_isUnit
    (hc.of_mul_right_left.isUnit_of_dvd' (Ideal.dvd_span_singleton.2 hx) dvd_rfl)
  have hcp : IsCoprime 𝔭.asIdeal 𝔪 := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have := 𝔭.isMaximal.eq_of_le hne le_sup_left
    exact hp (Ideal.dvd_iff_le.2 (this ▸ le_sup_right))
  set n := Ideal.absNorm 𝔭.asIdeal - 1
  have h3 := (h.2.2.2 (Ideal.span {x} ^ n) (pow_ne_zero _ hI) hc.pow_left).2 ⟨x ^ n, 1, ⟨pow_ne_zero _ hx0,
    one_ne_zero, by rw [← Ideal.span_singleton_pow]; exact hc.pow_left,
    by rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]; exact isCoprime_one_left, ?_, fun φ => ?_⟩,
    by rw [Ideal.span_singleton_one, Ideal.mul_top, Ideal.span_singleton_pow]⟩
  · refine GlobalTheory.RayMaximal.eq_of_forall_char fun χ => Units.ext ?_
    rw [map_pow, Units.val_pow_eq_pow_val, ← h1, ← RayExp.heckeIdeal_pow L χ hI, h3, map_one, Units.val_one]
  · rw [← Ideal.dvd_span_singleton]
    refine hcp.mul_dvd (Ideal.dvd_span_singleton.2 (pow_absNorm_sub_one 𝔭 hxp)) (Ideal.dvd_span_singleton.2 ?_)
    obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one x n
    rw [hc]
    exact 𝔪.mul_mem_right _ hx1
  · have h4 := hpos φ
    have h5 : φ ((β * x : 𝓞 K) : K) * φ β = φ x * (φ β * φ β) := by
      rw [show ((β * x : 𝓞 K) : K) = (β : K) * (x : K) from rfl, map_mul]; ring
    rw [h5] at h4
    have h6 : 0 < φ x := by nlinarith [mul_self_nonneg (φ β)]
    simpa using pow_pos h6 n

theorem exists_intTrace_not_mem [IsGalois K L] (P Q : Ideal (𝓞 L)) [P.IsPrime] (hPQ : P ⊔ Q = ⊤)
    (he : ((Nat.card (P.inertia (L ≃ₐ[K] L)) : ℕ) : 𝓞 L) ∉ P) :
    ∃ x ∈ Q, algebraMap (𝓞 K) (𝓞 L) (Algebra.intTrace (𝓞 K) (𝓞 L) x) ∉ P := by
  classical
  by_contra! H
  obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hPQ)
  let f : (L ≃ₐ[K] L) → (𝓞 L →* 𝓞 L ⧸ P) := fun σ =>
    ((Ideal.Quotient.mk P).comp (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) σ)).toMonoidHom
  have hf : ∀ σ y, f σ y = Ideal.Quotient.mk P (σ • y) := fun _ _ => rfl
  have hx1 : f 1 x = 1 := by
    rw [hf, one_smul, ← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq, ← hax]
    simpa using ha
  have h0 : ∑ σ, Finsupp.single (f σ) (f σ x) = 0 := by
    refine linearIndependent_iff.1 (linearIndependent_monoidHom (𝓞 L) (𝓞 L ⧸ P)) _ (funext fun y => ?_)
    have h1 := Ideal.Quotient.eq_zero_iff_mem.2 (H _ (Q.mul_mem_right y hx))
    rw [GlobalTheory.DifferentBound.algebraMap_intTrace_eq_sum, map_sum] at h1
    simp only [map_sum, Finsupp.linearCombination_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      ← map_mul, hf]
    simpa only [smul_mul'] using h1
  have h2 := DFunLike.congr_fun h0 (f 1)
  have h3 : ∀ σ, Finsupp.single (f σ) (f σ x) (f 1) = if σ ∈ P.inertia (L ≃ₐ[K] L) then 1 else 0 := by
    intro σ
    have : σ ∈ P.inertia (L ≃ₐ[K] L) ↔ f σ = f 1 := by
      rw [MonoidHom.ext_iff]
      refine forall_congr' fun y => ?_
      rw [hf, hf, one_smul, Ideal.Quotient.eq]
      rfl
    rw [Finsupp.single_apply, this]
    split_ifs with h
    · rw [h, hx1]
    · rfl
  rw [Finsupp.finsetSum_apply] at h2
  simp only [h3, Finset.sum_boole, Finsupp.zero_apply] at h2
  apply he
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h2

theorem not_sq_dvd {M : ℕ} (hM : Squarefree M) (hc : Nat.Coprime M (discr K).natAbs) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ¬ 𝔭.asIdeal ^ 2 ∣ Ideal.span {(M : 𝓞 K)} := by
  intro h
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K ⧸ 𝔭.asIdeal)
  have hpp : p.Prime := CharP.char_is_prime (𝓞 K ⧸ 𝔭.asIdeal) p
  have key : ∀ n : ℕ, (n : 𝓞 K) ∈ 𝔭.asIdeal ↔ p ∣ n := fun n => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff _ p]
  obtain ⟨m, rfl⟩ := (key M).1 (Ideal.dvd_span_singleton.1 ((dvd_pow_self _ two_ne_zero).trans h))
  have hm : ¬ 𝔭.asIdeal ∣ Ideal.span {(m : 𝓞 K)} := fun hd =>
    hpp.prime.not_isUnit (hM p (mul_dvd_mul_left p ((key m).1 (Ideal.dvd_span_singleton.1 hd))))
  rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton] at h
  have h1 := 𝔭.prime.pow_dvd_of_dvd_mul_right 2 hm h
  have hZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hpp
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hZ.ne_zero).2 hZ).isMaximal (by simpa using hpp.ne_zero)
  have h2 := pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(p : ℤ)}) 𝔭.asIdeal 2 (by simpa using hpp.ne_zero)
    (by simpa [Ideal.map_span] using h1)
  have h3 := Ideal.le_of_dvd h2 (Ideal.absNorm_mem _)
  rw [absNorm_differentIdeal K, pow_one, key] at h3
  exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc (dvd_mul_right p m) h3)

theorem card_not_mem {G : Type} [Group G] [Finite G] (P : Ideal (𝓞 L)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) {n : ℕ} (hn0 : n ≠ 0)
    (hn : (n : 𝓞 L) ∈ P) (h : ∀ g : G, g ^ (n - 1) = 1) : ((Nat.card G : ℕ) : 𝓞 L) ∉ P := by
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hP0
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 L ⧸ P)
  have hpp : p.Prime := CharP.char_is_prime (𝓞 L ⧸ P) p
  have key : ∀ n : ℕ, (n : 𝓞 L) ∈ P ↔ p ∣ n := fun n => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff _ p]
  rw [key] at hn ⊢
  intro hd
  have := Fact.mk hpp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : p ∣ n - 1 := hg ▸ orderOf_dvd_of_pow_eq_one (h g)
  have h2 := Nat.dvd_sub hn h1
  rw [show n - (n - 1) = 1 by omega] at h2
  exact hpp.one_lt.ne' (Nat.dvd_one.1 h2)

theorem natCast_mem_differentIdeal (hR : RayField) {M : ℕ} (hM : Squarefree M) (hc : Nat.Coprime M (discr K).natAbs)
    (h : IsRayField K L (natIdeal K M)) : (M : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  classical
  have := h.1
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := differentIdeal_ne_bot
  have hI : Ideal.span {(M : 𝓞 L)} ≠ ⊥ := by simpa using hM.ne_zero
  rw [← Ideal.dvd_span_singleton, UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hD0]
  intro P hP
  have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have hPm := hPp.isMaximal hP0
  have hp : P.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0
  let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨P.under (𝓞 K), inferInstance, hp⟩
  by_cases hnP : 𝔭.asIdeal ∣ natIdeal K M
  · obtain ⟨Q, hPQ, e⟩ := Ideal.eq_prime_pow_mul_coprime hI P
    obtain ⟨𝔪, hm⟩ := hnP
    have hm0 : 𝔪 ≠ ⊥ := by
      rintro rfl
      exact hM.ne_zero (by simpa using hm)
    have hpm : ¬ 𝔭.asIdeal ∣ 𝔪 := fun hd => not_sq_dvd hM hc 𝔭 (by
      rw [show Ideal.span {(M : 𝓞 K)} = _ from hm, sq]
      exact mul_dvd_mul_left _ hd)
    have he := card_not_mem (G := P.inertia (L ≃ₐ[K] L)) P hP0 (n := Ideal.absNorm 𝔭.asIdeal)
      (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hp)
      (by simpa using Ideal.mem_comap.1 (Ideal.absNorm_mem (P.under (𝓞 K))))
      fun g => Subtype.ext (inertia_pow hR 𝔭 hm0 hpm (hm ▸ h) ⟨P, hPp, ⟨rfl⟩, g.2⟩)
    obtain ⟨x, hx, htr⟩ := exists_intTrace_not_mem P Q hPQ he
    have h1 := not_dvd_differentIdeal_of_intTrace_not_mem (𝓞 K) (p := natIdeal K M) _ Q
      (by rw [Ideal.map_span, Set.image_singleton, map_natCast]; exact e.symm) x hx
      fun hmem => htr (Ideal.le_of_dvd ⟨𝔪, hm⟩ hmem)
    exact (emultiplicity_lt_iff_not_dvd.2 h1).le.trans (le_emultiplicity_of_pow_dvd ⟨Q, e⟩)
  · have h2 := GlobalTheory.DifferentBound.not_dvd_of_inertia K L P hP0 fun σ hσ => h.2.1 𝔭 hnP σ ⟨P, hPp, ⟨rfl⟩, hσ⟩
    rw [emultiplicity_eq_zero.2 h2]
    exact zero_le

theorem natAbs_discr_dvd : RayField → ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (M : ℕ), Squarefree M → Nat.Coprime M (discr K).natAbs → IsRayField K L (natIdeal K M) →
      (discr L).natAbs ∣ (discr K).natAbs ^ Module.finrank K L * M ^ Module.finrank ℚ L := by
  intro hR K L _ _ _ _ _ M hM hc h
  have h1 := map_dvd Ideal.absNorm (Ideal.dvd_span_singleton.2 (natCast_mem_differentIdeal hR hM hc h))
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h1
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L), mul_comm]
  exact mul_dvd_mul_left _ h1

end GlobalTheory.Mem.RayDiscr
