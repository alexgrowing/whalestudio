import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum

namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

section
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

theorem krullDimLE_one_of_krullDim_eq (h : ringKrullDim A = 1) : Ring.KrullDimLE 1 A := by
  rw [Ring.krullDimLE_iff, h]
  simp

theorem krullDim_quotient_eq_one_iff_eq_bot [Ring.KrullDimLE 1 A] (h : ringKrullDim A = 1) (p : PrimeSpectrum A) :
    ringKrullDim (A ⧸ p.asIdeal) = 1 ↔ p.asIdeal = ⊥ := by
  constructor
  · intro hq
    by_contra hne
    have hmax : p.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot p.isPrime hne
    have h0 := ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
    rw [h0] at hq
    exact zero_ne_one hq
  · intro hp
    rw [ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hp).trans (RingEquiv.quotientBot A)), h]

theorem length_coker_ne_top (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Ring.KrullDimLE 1 A] {x : A} (hx : x ≠ 0) :
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) ≠ ⊤ := by
  have htors : Module.IsTorsionBy A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) x := by
    intro n
    refine Submodule.Quotient.induction_on _ n (fun m => ?_)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, rfl⟩
  have htors' : Module.IsTorsionBySet A (M ⧸ LinearMap.range (LinearMap.lsmul A M x))
      (Ideal.span {x} : Set A) :=
    (Module.isTorsionBySet_span_singleton_iff x).mpr htors
  letI : Module (A ⧸ Ideal.span {x}) (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) := htors'.module
  haveI : IsScalarTower A (A ⧸ Ideal.span {x}) (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) :=
    htors'.isScalarTower
  haveI : Ring.KrullDimLE 0 (A ⧸ Ideal.span {x}) := by
    rw [Ring.krullDimLE_zero_iff]
    intro P hP
    have hc : (Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P).IsPrime := Ideal.IsPrime.comap _
    have hne : Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P ≠ ⊥ := by
      intro h0
      have hxm : x ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P := by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)]
        exact P.zero_mem
      rw [h0, Ideal.mem_bot] at hxm
      exact hx hxm
    haveI hm := Ideal.IsPrime.isMaximal_of_ne_bot hc hne
    have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {x})) := Ideal.Quotient.mk_surjective
    have hmap := Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj
      (m := Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P) (by
        intro a ha
        rw [RingHom.mem_ker] at ha
        rw [Ideal.mem_comap, ha]
        exact P.zero_mem)
    rwa [Ideal.map_comap_of_surjective _ hsurj] at hmap
  haveI : IsArtinianRing (A ⧸ Ideal.span {x}) := isArtinianRing_iff_krullDimLE_zero.mpr inferInstance
  haveI : Module.Finite (A ⧸ Ideal.span {x}) (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hs : Function.Surjective (algebraMap A (A ⧸ Ideal.span {x})) := Ideal.Quotient.mk_surjective
  rw [Module.length_eq_of_surjective hs, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, inferInstance⟩

theorem length_ker_eq_zero_of_torsionFree (M : Type*) [AddCommGroup M] [Module A M] [Module.IsTorsionFree A M]
    {x : A} (hx : x ≠ 0) :
    length A (LinearMap.ker (LinearMap.lsmul A M x)) = 0 := by
  rw [Module.length_eq_zero_iff]
  have hreg : IsSMulRegular M x := IsSMulRegular.of_ne_zero hx
  have hker : LinearMap.ker (LinearMap.lsmul A M x) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fun a b hab => hreg (by simpa using hab))
  rw [hker]
  infer_instance

theorem length_localization_bot_eq_finrank (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    length (Localization.AtPrime (⊥ : Ideal A)) (LocalizedModule (⊥ : Ideal A).primeCompl M) =
      (finrank A M : ℕ∞) := by
  have hfield : IsField (Localization.AtPrime (⊥ : Ideal A)) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot]
  letI : Field (Localization.AtPrime (⊥ : Ideal A)) := hfield.toField
  have hle : (⊥ : Ideal A).primeCompl ≤ nonZeroDivisors A := by
    intro a ha
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => ha (by rw [h0]; exact Submodule.zero_mem _))
  haveI : Module.Finite (Localization.AtPrime (⊥ : Ideal A)) (LocalizedModule (⊥ : Ideal A).primeCompl M) :=
    Module.Finite.of_isLocalizedModule (⊥ : Ideal A).primeCompl
      (LocalizedModule.mkLinearMap (⊥ : Ideal A).primeCompl M)
  rw [Module.length_of_free_of_finite, Module.length_eq_one, mul_one]
  rw [IsLocalization.finrank_eq (Localization.AtPrime (⊥ : Ideal A)) (⊥ : Ideal A).primeCompl hle,
    IsLocalizedModule.finrank_eq (⊥ : Ideal A).primeCompl
      (LocalizedModule.mkLinearMap (⊥ : Ideal A).primeCompl M) hle]

theorem ordQuotient_bot (x : A) :
    ordMod ⟨⊥, Ideal.isPrime_bot⟩ x = Ring.ord A x := by
  unfold ordMod Ring.ord
  dsimp only
  have hs : Function.Surjective (algebraMap A (A ⧸ (⊥ : Ideal A))) := Ideal.Quotient.mk_surjective
  rw [← Module.length_eq_of_surjective hs]
  have h1 : Ideal.map (Ideal.Quotient.mkₐ A (⊥ : Ideal A)) (Ideal.span {x}) =
      Ideal.span {Ideal.Quotient.mk (⊥ : Ideal A) x} := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.Quotient.mkₐ_eq_mk]
  have e1 := (Ideal.quotientEquivAlgOfEq A h1).symm.trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ A ⊥ (Ideal.span {x})).trans
      (Ideal.quotientEquivAlgOfEq A (bot_sup_eq (Ideal.span {x}))))
  exact e1.toLinearEquiv.length_eq

end

theorem dimOneTorsionFreeFormula : LocalLengthAdditivityTorsionFree := by
  intro A _ _ _ _ M _ _ _ _ x h hx
  haveI : Ring.KrullDimLE 1 A := krullDimLE_one_of_krullDim_eq h
  obtain ⟨-, heq⟩ := dimOneFormula A M x h (length_coker_ne_top M hx)
  rw [heq, length_ker_eq_zero_of_torsionFree M hx, zero_add]
  have hset : {p : PrimeSpectrum A | ringKrullDim (A ⧸ p.asIdeal) = 1} = {⟨⊥, Ideal.isPrime_bot⟩} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [krullDim_quotient_eq_one_iff_eq_bot h p]
    constructor
    · intro hp
      ext1
      exact hp
    · intro hp
      rw [hp]
  change ∑ᶠ p ∈ {p : PrimeSpectrum A | ringKrullDim (A ⧸ p.asIdeal) = 1}, _ = _
  rw [hset, finsum_mem_singleton]
  dsimp only
  rw [length_localization_bot_eq_finrank, ordQuotient_bot]

end ReciprocityTheory.ChartRestriction.G.AI
