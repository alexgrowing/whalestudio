import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Unmixed

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence Pointwise

variable {R : Type*} [CommRing R] [IsLocalRing R]

private theorem annihilator_self_eq_bot' : Module.annihilator R R = ⊥ := by
  ext r
  simp only [Module.mem_annihilator, Submodule.mem_bot]
  exact ⟨fun h => by simpa using h 1, fun h m => by simp [h]⟩

private theorem smul_top_eq_self' (I : Ideal R) : (I • (⊤ : Submodule R R)) = I := by
  exact Ideal.mul_top I

private theorem span_singleton_eq_smul_top' (x : R) :
    (x • (⊤ : Submodule R R)) = Ideal.span {x} := by
  rw [← Submodule.ideal_span_singleton_smul, smul_top_eq_self']

private theorem isSMulRegular_of_mem_nonZeroDivisors' {x : R} (reg : x ∈ nonZeroDivisors R) :
    IsSMulRegular R x := by
  intro a b hab
  have h0 : (a - b) * x = 0 := by
    simp only [smul_eq_mul] at hab
    rw [sub_mul, mul_comm a, mul_comm b, hab, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp reg).2 _ h0)

private noncomputable def quotSMulTopEquivQuot' (x : R) :
    QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
  Submodule.quotEquivOfEq _ _ (span_singleton_eq_smul_top' x)

theorem IsCM.associatedPrimes_eq_minimalPrimes (h : IsCM R) :
    associatedPrimes R R = minimalPrimes R := by
  rw [(isCM_iff_isCMMod.mp h).associatedPrimes_eq_minimalPrimes, annihilator_self_eq_bot']

theorem IsCM.quotient_span_singleton (h : IsCM R) {x : R} (hx : x ∈ maximalIdeal R)
    (reg : x ∈ nonZeroDivisors R) [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsCM (R ⧸ Ideal.span {x}) := by
  haveI : IsNoetherianRing R := h.1
  exact (isCM_quotient_iff _).mpr ((isCMMod_congr (quotSMulTopEquivQuot' x)).mp
    ((isCM_iff_isCMMod.mp h).quotSMulTop hx (isSMulRegular_of_mem_nonZeroDivisors' reg)))

theorem isCM_of_quotient_span_singleton [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (reg : x ∈ nonZeroDivisors R) [IsLocalRing (R ⧸ Ideal.span {x})]
    (h : IsCM (R ⧸ Ideal.span {x})) : IsCM R := by
  exact isCM_iff_isCMMod.mpr (IsCMMod.of_quotSMulTop hx (isSMulRegular_of_mem_nonZeroDivisors' reg)
    ((isCMMod_congr (quotSMulTopEquivQuot' x)).mpr ((isCM_quotient_iff _).mp h)))

theorem IsCM.quotient_ofList (h : IsCM R) {rs : List R} (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (reg : IsRegular R rs) [IsLocalRing (R ⧸ Ideal.ofList rs)] :
    IsCM (R ⧸ Ideal.ofList rs) := by
  haveI : IsNoetherianRing R := h.1
  have h1 := (isCM_iff_isCMMod.mp h).quotient_ofList hrs reg
  exact (isCM_quotient_iff _).mpr
    ((isCMMod_congr (Submodule.quotEquivOfEq _ _ (smul_top_eq_self' _))).mp h1)

theorem IsCM.isRegular_of_isArtinianRing_quotient (h : IsCM R) (xs : List R)
    (hxs : ∀ r ∈ xs, r ∈ maximalIdeal R) (hlen : (xs.length : WithBot ℕ∞) = ringKrullDim R)
    (hart : IsArtinianRing (R ⧸ Ideal.ofList xs)) : IsRegular R xs := by
  apply (isCM_iff_isCMMod.mp h).isRegular_of_supportDim_quotient_le_zero xs hxs
  · rw [Module.supportDim_self_eq_ringKrullDim]; exact hlen
  · rw [Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEq _ _ (smul_top_eq_self' _)),
      Module.supportDim_quotient_eq_ringKrullDim]
    exact Ring.krullDimLE_iff.mp inferInstance

end ReciprocityTheory.CA
