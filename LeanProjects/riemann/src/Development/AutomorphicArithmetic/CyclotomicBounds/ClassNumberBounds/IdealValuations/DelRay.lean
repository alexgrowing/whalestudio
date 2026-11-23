import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.ExistsUnitOfIsDecomp

open NumberField NumberField.IsCMField NumberField.Units IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

omit [IsCMField K] in
private theorem delRay_count_eq_zero (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (α : Kˣ)
    (hα : (α : K) = (a : K)) (ha : a ∉ w.asIdeal) :
    FractionalIdeal.count K w
      ((toPrincipalIdeal (𝓞 K) K α : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  rw [← exists_unit_locAt_iff]
  have hu : IsUnit (algebraMap (𝓞 K) (locAt w.asIdeal) a) :=
    IsLocalization.map_units (M := w.asIdeal.primeCompl) (locAt w.asIdeal) ⟨a, ha⟩
  exact ⟨hu.unit, by rw [hα, hu.unit_spec]; rfl⟩

theorem IsDel.apply_of_congr {l M : ℕ} (hl : l.Prime) {ι : Type*} [Fintype ι]
    {B : MinusBasis K l ι} {v : HeightOneSpectrum (𝓞 K)}
    {om : (𝓞 K ⧸ v.asIdeal)ˣ →* Multiplicative (ZMod (l ^ M))}
    {del : primeTo v →* Multiplicative (ZMod (l ^ M))} (hdel : IsDel B v om del)
    (a : 𝓞 K) (α : Kˣ) (hα : (α : K) = (a : K)) (r : (𝓞 K ⧸ v.asIdeal)ˣ)
    (hr : Ideal.Quotient.mk v.asIdeal a = r) (h1 : a - 1 ∈ (conjPrime v).asIdeal) :
    ∃ h : toPrincipalIdeal (𝓞 K) K α ∈ primeTo v, del ⟨_, h⟩ = om r := by
  have hav : a ∉ v.asIdeal := by
    intro h
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [hr] at h0
    exact r.ne_zero h0
  have hac : a ∉ (conjPrime v).asIdeal := by
    intro h
    apply (conjPrime v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using (conjPrime v).asIdeal.sub_mem h h1
  have hmem : toPrincipalIdeal (𝓞 K) K α ∈ primeTo v :=
    ⟨delRay_count_eq_zero v a α hα hav, delRay_count_eq_zero _ a α hα hac⟩
  refine ⟨hmem, ?_⟩
  set b : 𝓞 K := ringOfIntegersComplexConj K a with hb
  have hb1 : b - 1 ∈ v.asIdeal := by
    have h2 : ringOfIntegersComplexConj K (a - 1) ∈ v.asIdeal := h1
    rwa [map_sub, map_one] at h2
  have hbq : Ideal.Quotient.mk v.asIdeal b = 1 := by
    rw [← map_one (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq.mpr hb1
  have hbv : b ∉ v.asIdeal := by
    intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h] at hbq
    exact zero_ne_one hbq
  have hbK : (b : K) = complexConj K (α : K) := by rw [hα]; rfl
  have hb0 : complexConj K (α : K) ≠ 0 := by simp
  obtain ⟨u, hu⟩ := exists_unit_div_conj v (α := α) hmem (one_mem _) (by simp)
  rw [(hdel.values hl).1 α hmem u hu]
  congr 1
  have hres : IsResidue v.asIdeal ((α : K) / complexConj K (α : K)) r :=
    ⟨a, b, hbv, by rw [hbK, div_mul_cancel₀ _ hb0, hα], by rw [hbq, mul_one, hr]⟩
  obtain ⟨y, hy, hy2⟩ := (isResidue_iff _ _ _).mp hres
  have hyu : y = (u : locAt v.asIdeal) := Subtype.ext (hy.trans hu.symm)
  rw [hyu] at hy2
  exact Units.ext hy2

theorem IsDel.surjective {l M : ℕ} (hl : l.Prime) {ι : Type*} [Fintype ι]
    {B : MinusBasis K l ι} {v : HeightOneSpectrum (𝓞 K)} (hv : conjPrime v ≠ v)
    {om : (𝓞 K ⧸ v.asIdeal)ˣ →* Multiplicative (ZMod (l ^ M))} (hom : Function.Surjective om)
    {del : primeTo v →* Multiplicative (ZMod (l ^ M))} (hdel : IsDel B v om del) :
    Function.Surjective del := by
  intro t
  obtain ⟨r, rfl⟩ := hom t
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (r : 𝓞 K ⧸ v.asIdeal)
  have hco : v.asIdeal ⊔ (conjPrime v).asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne v.isMaximal (conjPrime v).isMaximal
      (fun h => hv (HeightOneSpectrum.ext h.symm))
  have h1 : (1 : 𝓞 K) ∈ v.asIdeal ⊔ (conjPrime v).asIdeal := by rw [hco]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  have hr : Ideal.Quotient.mk v.asIdeal (x + s * y) = r := by
    rw [← hs]
    refine Ideal.Quotient.eq.mpr ?_
    have e : x + s * y - s = (1 - s) * x := by linear_combination s * hxy
    rw [e]
    exact v.asIdeal.mul_mem_left _ hx
  have ha1 : x + s * y - 1 ∈ (conjPrime v).asIdeal := by
    have e : x + s * y - 1 = (s - 1) * y := by linear_combination hxy
    rw [e]
    exact (conjPrime v).asIdeal.mul_mem_left _ hy
  have ha0 : ((x + s * y : 𝓞 K) : K) ≠ 0 := by
    intro h
    rw [RingOfIntegers.coe_eq_zero_iff.mp h, map_zero] at hr
    exact r.ne_zero hr.symm
  obtain ⟨h, hh⟩ := hdel.apply_of_congr hl (x + s * y) (Units.mk0 _ ha0) rfl r hr ha1
  exact ⟨_, hh⟩

end KStar.IdealValuations
