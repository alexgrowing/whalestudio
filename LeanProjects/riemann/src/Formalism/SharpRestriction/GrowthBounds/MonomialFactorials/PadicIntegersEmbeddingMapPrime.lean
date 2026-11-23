import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Formalism.MainNotions.G

variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem castPow_zero (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (n : ℕ) :
    ((p ^ n : ℕ) : O ⧸ (IsLocalRing.maximalIdeal O) ^ n) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ n)) (p ^ n), Nat.cast_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hpm n

def iotaN (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (n : ℕ) :
    ℤ_[p] →+* O ⧸ (IsLocalRing.maximalIdeal O) ^ n :=
  RingHom.comp (ZMod.castHom (ringChar.dvd (castPow_zero p O hpm n)) (O ⧸ (IsLocalRing.maximalIdeal O) ^ n))
    (PadicInt.toZModPow n)

theorem iotaN_compat (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal O) hle).comp (iotaN p O hpm n) = iotaN p O hpm m := by
  have hz := PadicInt.zmod_cast_comp_toZModPow (p := p) m n hle
  have key : ∀ (f g : ZMod (p ^ n) →+* O ⧸ (IsLocalRing.maximalIdeal O) ^ m), f = g :=
    fun f g => RingHom.ext_zmod f g
  unfold iotaN
  rw [← hz]
  ext x
  simp only [RingHom.comp_apply]
  exact congrArg (fun f => f (PadicInt.toZModPow n x))
    (key ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal O) hle).comp
      (ZMod.castHom (ringChar.dvd (castPow_zero p O hpm n)) (O ⧸ (IsLocalRing.maximalIdeal O) ^ n)))
      ((ZMod.castHom (ringChar.dvd (castPow_zero p O hpm m)) (O ⧸ (IsLocalRing.maximalIdeal O) ^ m)).comp
        (ZMod.castHom (pow_dvd_pow p hle) (ZMod (p ^ m)))))

def iota0 (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : ℤ_[p] →+* O :=
  ((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal O)).symm : AdicCompletion (IsLocalRing.maximalIdeal O) O →+* O).comp
    (AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal O) (iotaN p O hpm) (fun hle => iotaN_compat p O hpm hle))

theorem padic_integers_embedding_map_prime (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) [IsAdicComplete (IsLocalRing.maximalIdeal O) O] :
    iota0 p O hpm (p : ℤ_[p]) = (p : O) :=
  map_natCast (iota0 p O hpm) p

theorem padic_integers_embedding_injective (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : Function.Injective (iota0 p O hpm) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hspec := PadicInt.unitCoeff_spec hne
  have h2 := congrArg (iota0 p O hpm) hspec
  rw [hx, map_mul, map_pow, padic_integers_embedding_map_prime] at h2
  have hu : IsUnit (iota0 p O hpm (PadicInt.unitCoeff hne : ℤ_[p])) := (Units.isUnit _).map _
  rcases mul_eq_zero.mp h2.symm with h3 | h3
  · exact hu.ne_zero h3
  · exact hp0 (pow_eq_zero_iff'.mp h3).1

def iotaQ (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : ℚ_[p] →+* KK O :=
  IsFractionRing.lift (A := ℤ_[p]) (K := ℚ_[p]) (g := (algebraMap O (KK O)).comp (iota0 p O hpm))
    ((IsFractionRing.injective O (KK O)).comp (padic_integers_embedding_injective p O hpm hp0))

theorem iotaQ_int (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : ℤ_[p]) :
    iotaQ p O hpm hp0 (x : ℚ_[p]) = algebraMap O (KK O) (iota0 p O hpm x) := by
  unfold iotaQ
  exact IsFractionRing.lift_algebraMap _ x

def iotaX (X : flipOneThree.Inst) : ℚ_[X.p] →+* KK X.O :=
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal X.O) X.O := X.setting.complete
  iotaQ X.p X.O X.setting.p_mem X.setting.p_ne

theorem iotaX_int (X : flipOneThree.Inst) (x : ℤ_[X.p]) :
    ∃ y : X.O, iotaX X (x : ℚ_[X.p]) = algebraMap X.O (KK X.O) y := by
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal X.O) X.O := X.setting.complete
  exact ⟨_, iotaQ_int X.p X.O X.setting.p_mem X.setting.p_ne x⟩

end Formalism.MainNotions.G.SymmetricFormBlocks

end
