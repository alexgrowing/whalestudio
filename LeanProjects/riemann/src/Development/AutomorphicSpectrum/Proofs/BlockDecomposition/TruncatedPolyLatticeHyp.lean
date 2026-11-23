import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

set_option autoImplicit false

noncomputable section

open DividedPowers CrystallineSemistableComparison.Pb Polynomial

namespace GlobalTheory.CompanionTheory.LatPolyB

variable (l : ℕ) [Fact l.Prime]

theorem dvd_pow_of_ne_zero {x : ℤ_[l]} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ (l : ℤ_[l]) ^ n := by
  have h := PadicInt.unitCoeff_spec hx
  refine ⟨x.valuation, ((PadicInt.unitCoeff hx)⁻¹ : ℤ_[l]ˣ), ?_⟩
  calc (l : ℤ_[l]) ^ x.valuation
      = (((PadicInt.unitCoeff hx)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) *
          (((PadicInt.unitCoeff hx : ℤ_[l]ˣ) : ℤ_[l]) * (l : ℤ_[l]) ^ x.valuation) :=
        (Units.inv_mul_cancel_left _ _).symm
    _ = (((PadicInt.unitCoeff hx)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * x := congrArg _ h.symm
    _ = x * (((PadicInt.unitCoeff hx)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := mul_comm _ _

def quotX : (ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])}) ≃+* ℤ_[l] :=
  (Ideal.quotEquivOfEq (by simp)).trans (Polynomial.quotientSpanXSubCAlgEquiv (0 : ℤ_[l])).toRingEquiv

theorem quotX_natCast (n : ℕ) : quotX l (n : ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])}) = n := map_natCast _ n

theorem cpl : IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])})})
    (ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])}) := by
  have h : IsAdicComplete (Ideal.span {(l : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]; infer_instance
  have e : (Ideal.span {(l : ℤ_[l])}).map ((quotX l).symm : ℤ_[l] →+* _) =
      Ideal.span {((l : ℕ) : ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])})} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  rw [← e]
  exact (IsAdicComplete.congr_ringEquiv _ (quotX l).symm).2 h

theorem padic_poly_graded_smul_pow (m i : ℕ) (hi : i < m) (a : ℤ_[l][X])
    (b : ℚ_[l][X] ⧸ Ideal.span {(X : ℚ_[l][X]) ^ m})
    (h : ((Ideal.Quotient.mk (Ideal.span {(X : ℚ_[l][X]) ^ m})).comp (Polynomial.mapRingHom (PadicInt.Coe.ringHom (p := l)))) a *
      ((Ideal.Quotient.mk (Ideal.span {(X : ℚ_[l][X]) ^ m})).comp (Polynomial.mapRingHom (PadicInt.Coe.ringHom (p := l)))) X ^ i =
      ((Ideal.Quotient.mk (Ideal.span {(X : ℚ_[l][X]) ^ m})).comp (Polynomial.mapRingHom (PadicInt.Coe.ringHom (p := l)))) X ^ (i + 1) * b) :
    X ∣ a := by
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X] at h
  rw [← map_pow, ← map_mul, ← map_pow, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  have h1 : (X : ℚ_[l][X]) ^ (i + 1) ∣ a.map (PadicInt.Coe.ringHom (p := l)) * X ^ i := by
    have h2 : (X : ℚ_[l][X]) ^ (i + 1) ∣ a.map (PadicInt.Coe.ringHom (p := l)) * X ^ i - X ^ (i + 1) * b' :=
      (pow_dvd_pow _ hi).trans h
    exact (dvd_sub_left (Dvd.intro _ rfl)).1 h2
  rw [pow_succ', mul_comm] at h1
  have h3 : (X : ℚ_[l][X]) ∣ a.map (PadicInt.Coe.ringHom (p := l)) :=
    (mul_dvd_mul_iff_left (pow_ne_zero i Polynomial.X_ne_zero)).1 (by simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h1)
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_map] at h3
  rw [Polynomial.X_dvd_iff]
  exact PadicInt.coe_eq_zero.1 h3

theorem hyp : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ), 1 ≤ m → Lat.Hyp ((Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial ℚ_[l]) ^ m})).comp (Polynomial.mapRingHom (PadicInt.Coe.ringHom (p := l)))) Polynomial.X l m := by
  intro l _ m hm
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine
    { one_le := hm
      nil := ?_
      gr := fun i hi a b h => padic_poly_graded_smul_pow l m i hi a b h
      dom := (quotX l).toMulEquiv.isDomain _
      val := fun x y => ?_
      dv := fun x hx => ?_
      l0 := ?_
      cpl := cpl l
      unit := fun n hn => ?_ }
  · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  · rcases ValuationRing.dvd_total (quotX l x) (quotX l y) with h | h
    · exact Or.inl ((map_dvd_iff (quotX l)).1 h)
    · exact Or.inr ((map_dvd_iff (quotX l)).1 h)
  · obtain ⟨n, hn⟩ := dvd_pow_of_ne_zero l (x := quotX l x) (by simpa using hx)
    refine ⟨n, (map_dvd_iff (quotX l)).1 ?_⟩
    simpa [quotX_natCast] using hn
  · intro h
    apply hl0
    have := congrArg (quotX l) h
    simpa [quotX_natCast] using this
  · have hn0 : (n : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hn
    obtain ⟨k, u, hu⟩ := dvd_pow_of_ne_zero l hn0
    refine ⟨k, C u, ?_⟩
    have := congrArg (C : ℤ_[l] →+* ℤ_[l][X]) hu
    simpa using this.symm

end GlobalTheory.CompanionTheory.LatPolyB
