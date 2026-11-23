import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsIotaAt
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.DivPtLocal.Count

variable {E : Type} [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))

def red (N m n : ℕ) : ↥(locDiv w N m n) →+
    (Fin m → Fin n → (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)})) where
  toFun X i j := Ideal.Quotient.mk _ (⟨(N : w.adicCompletion E) * X.1 i j, X.2 i j⟩ : w.adicCompletionIntegers E)
  map_zero' := by
    funext i j
    rw [Pi.zero_apply, Pi.zero_apply, ← map_zero (Ideal.Quotient.mk _)]
    congr 1
    apply Subtype.ext
    simp
  map_add' X Y := by
    funext i j
    rw [Pi.add_apply, Pi.add_apply, ← map_add]
    congr 1
    apply Subtype.ext
    simp [mul_add]

theorem natCast_ne_zero {N : ℕ} (hN : 0 < N) : (N : w.adicCompletion E) ≠ 0 := by
  have h : (N : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (N : E) := by simp
  rw [h]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hN.ne')

theorem red_surjective {N : ℕ} (hN : 0 < N) (m n : ℕ) : Function.Surjective (red w N m n) := by
  intro Y
  have hN' := natCast_ne_zero w hN
  choose Z hZ using fun i j => Ideal.Quotient.mk_surjective (Y i j)
  have key : ∀ i j, (N : w.adicCompletion E) * ((N : w.adicCompletion E)⁻¹ * (Z i j : w.adicCompletion E))
      = Z i j := fun i j => by rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]
  refine ⟨⟨Matrix.of fun i j => (N : w.adicCompletion E)⁻¹ * (Z i j : w.adicCompletion E), ?_⟩, ?_⟩
  · intro i j
    rw [Matrix.of_apply, key]
    exact (Z i j).2
  · funext i j
    rw [← hZ]
    change Ideal.Quotient.mk _ _ = _
    congr 1
    apply Subtype.ext
    exact key i j

theorem ker_red {N : ℕ} (hN : 0 < N) (m n : ℕ) :
    (red w N m n).ker = (locInt w m n).addSubgroupOf (locDiv w N m n) := by
  have hN' := natCast_ne_zero w hN
  ext X
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_locInt]
  simp only [funext_iff, Pi.zero_apply]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  change Ideal.Quotient.mk _ _ = _ ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have h := congrArg (fun z : w.adicCompletionIntegers E => (z : w.adicCompletion E)) hc
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast] at h
    rw [mul_left_cancel₀ hN' h]
    exact c.2
  · intro h
    refine ⟨⟨X.1 i j, h⟩, ?_⟩
    apply Subtype.ext
    simp

theorem card_locQ (E : Type) [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (N m n : ℕ) (hN : 0 < N) :
    Nat.card (GlobalTheory.DivPtLocal.LocQ w N m n) =
      Nat.card (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)}) ^ (m * n) := by
  have e := (QuotientAddGroup.quotientAddEquivOfEq (ker_red w hN m n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (red w N m n) (red_surjective w hN m n))
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp [mul_comm]

end GlobalTheory.DivPtLocal.Count

end
