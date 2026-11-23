import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.DenseSurj

namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem mem_span_l_iff {l : ℕ} [hl : Fact l.Prime] (K : FinExt l) (y : ↥(ball K)) :
    y ∈ Ideal.span {((l : ℕ) : ↥(ball K))} ↔
      ‖((y : ↥K.1) : Om l)‖ ≤ ‖((l : ℕ) : Om l)‖ := by
  have hl0' : ((l : ℕ) : Om l) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l))]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)
  have hl0 : ((l : ℕ) : ↥K.1) ≠ 0 := by
    intro h
    apply hl0'
    have h' : (((l : ℕ) : ↥K.1) : Om l) = 0 := by rw [h]; rfl
    simpa using h'
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : ‖((z : ↥K.1) : Om l)‖ ≤ 1 := z.2
    have hc : (((z * ((l : ℕ) : ↥(ball K)) : ↥(ball K)) : ↥K.1) : Om l) =
        ((z : ↥K.1) : Om l) * ((l : ℕ) : Om l) := by simp
    rw [hc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hz
  · intro h
    have hmem : ‖(((y : ↥K.1) / ((l : ℕ) : ↥K.1) : ↥K.1) : Om l)‖ ≤ 1 := by
      have hc : (((y : ↥K.1) / ((l : ℕ) : ↥K.1) : ↥K.1) : Om l) =
          ((y : ↥K.1) : Om l) / ((l : ℕ) : Om l) := by simp
      rw [hc, norm_div, div_le_one (norm_pos_iff.mpr hl0')]
      exact h
    refine ⟨⟨(y : ↥K.1) / ((l : ℕ) : ↥K.1), hmem⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    push_cast
    exact div_mul_cancel₀ _ hl0

theorem locDegOf_of (hB : BallCard) (hD : DenseSurj) (hK : KerProp) (hN : NormCard) :
    LocDegOf := by
  intro l hl E _ _ φ K hφK hdense v hv hφv
  let ψ : 𝓞 E →+* ↥(ball K) :=
    { toFun := fun x => ⟨⟨φ (x : E), hφK _⟩, (hφv x).1⟩
      map_one' := Subtype.ext <| Subtype.ext <| by simp
      map_mul' := fun a b => Subtype.ext <| Subtype.ext <| by simp
      map_zero' := Subtype.ext <| Subtype.ext <| by simp
      map_add' := fun a b => Subtype.ext <| Subtype.ext <| by simp }
  let q := (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ↥(ball K))})).comp ψ
  have hsurj : Function.Surjective q := by
    intro w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨x, hx⟩ := hD l E φ K hφK hdense ((y : ↥K.1) : Om l) (y : ↥K.1).2 y.2
    refine ⟨x, ?_⟩
    show Ideal.Quotient.mk _ (ψ x) = Ideal.Quotient.mk _ y
    rw [Ideal.Quotient.eq, mem_span_l_iff]
    have hc : (((ψ x - y : ↥(ball K)) : ↥K.1) : Om l) = φ (x : E) - ((y : ↥K.1) : Om l) := rfl
    rw [hc, norm_sub_rev]
    exact hx
  have hker : RingHom.ker q = v.asIdeal ^ v.asIdeal.ramificationIdx ℤ := by
    ext x
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk _ (ψ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (mem_span_l_iff K (ψ x)).trans (hK l E φ v hv hφv x)
  have hcard : Nat.card (𝓞 E ⧸ v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) =
      Nat.card (↥(ball K) ⧸ Ideal.span {((l : ℕ) : ↥(ball K))}) := by
    rw [← hker]
    exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv
  rw [hN l E v hv, hB l K] at hcard
  exact (Nat.pow_right_injective hl.out.two_le hcard).symm

end PI.CompDegEF
