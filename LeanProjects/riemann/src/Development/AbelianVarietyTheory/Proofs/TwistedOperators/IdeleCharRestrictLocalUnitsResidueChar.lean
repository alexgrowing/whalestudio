import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResLoc

open GlobalTheory.IdemSupport Formalism.L2.JoinChr Formalism.L2.Host

theorem val_alg {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (P.adicCompletion E) a) = P.valuation E a :=
  P.valuedAdicCompletion_eq_valuation' a

theorem le_exp_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem locK_eq_of_tame {E : Type} [Field E] [NumberField E] (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (ht : χ.TameAt P) (k l : Eˣ) (hk : P.valuation E (k : E) = 1) (hl : P.valuation E (l : E) = 1)
    (h : P.valuation E ((k : E) - l) ≤ WithZero.exp (-1 : ℤ)) : χ.locK P k = χ.locK P l := by
  have h1 : χ.locK P (k * l⁻¹) = 1 := by
    refine ht (atFin P (k * l⁻¹)) ?_ ?_
    · change Valued.v (algebraMap E (P.adicCompletion E) ((k * l⁻¹ : Eˣ) : E)) = 1
      rw [val_alg, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hk, hl, inv_one, one_mul]
    · change Valued.v (algebraMap E (P.adicCompletion E) ((k * l⁻¹ : Eˣ) : E) - 1) ≤ _
      have e : ((k * l⁻¹ : Eˣ) : E) - 1 = ((k : E) - l) * (l : E)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ l.ne_zero]
      rw [← map_one (algebraMap E (P.adicCompletion E)), ← map_sub, val_alg, e, map_mul, map_inv₀, hl, inv_one,
        mul_one]
      exact h
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

theorem exists_lift_lt_one {R T O K Γ : Type} [CommRing R] [CommRing T] [CommRing O] [CommRing K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (t : R →+* T) (ev : R →+* K) (S : Subring T) (o : O →+* S)
    (I : Ideal O) (hs : ∀ s : T, ∃ z, t z = s) (hint : ∀ z, t z ∈ S → v (ev z) ≤ 1)
    (hI : ∀ a ∈ I, ∃ z, t z = o a ∧ v (ev z) < 1) (s : S) (h : s ∈ I.map o) : ∃ z, t z = s ∧ v (ev z) < 1 := by
  refine Submodule.span_induction (p := fun (s : S) _ => ∃ z, t z = s ∧ v (ev z) < 1) ?_ ?_ ?_ ?_ h
  · rintro _ ⟨a, ha, rfl⟩
    exact hI a ha
  · exact ⟨0, map_zero _, by rw [map_zero, map_zero]; exact zero_lt_one⟩
  · rintro x y _ _ ⟨z, hz, h⟩ ⟨z', hz', h'⟩
    refine ⟨z + z', by rw [map_add, hz, hz']; rfl, ?_⟩
    rw [map_add]
    exact Valuation.map_add_lt _ h h'
  · rintro c x _ ⟨z, hz, h⟩
    obtain ⟨w, hw⟩ := hs c
    refine ⟨w * z, by rw [map_mul, hz, hw]; rfl, ?_⟩
    rw [map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint w (hw ▸ c.2))) h

theorem map_eq_one_of_supp {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {e x y k : R} (he : f e = 0)
    (hx : e * (x - 1) = x - 1) (hy : x = y * (1 + e * (k - 1))) : f y = 1 := by
  have h1 := congrArg f hx
  have h2 := congrArg f hy
  simp only [map_mul, map_add, map_sub, map_one, he, zero_mul, add_zero, mul_one] at h1 h2
  rw [← h2, ← sub_eq_zero, ← h1]

theorem map_eq_mul_of_supp {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {e x y k : R} (he : f e = 1)
    (hy : x = y * (1 + e * (k - 1))) : f x = f y * f k := by
  rw [hy]
  simp only [map_mul, map_add, map_sub, map_one, he]
  ring

theorem exists_units_quot {R : Type} [CommRing R] (x l : Rˣ) {r : R} (hl : (l : R) = r) :
    ∃ y : Rˣ, x = y * l ∧ (x : R) = y * r :=
  ⟨x * l⁻¹, (inv_mul_cancel_right x l).symm, by rw [← hl, ← Units.val_mul, inv_mul_cancel_right]⟩

variable {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}

def evAt (Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    AE D →+* Q.adicCompletion D.host.E :=
  (RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.adicCompletion D.host.E) Q).comp Φ

theorem ev_sub (a b : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (a - b) Q = Φ a Q - Φ b Q := by rw [map_sub]; rfl

theorem ev_one (Q : HeightOneSpectrum (𝓞 D.host.E)) : Φ 1 Q = 1 := by rw [map_one]; rfl

theorem ev_inc (hΦ : Comp D Φ) (a : D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (incA D a) Q = algebraMap D.host.E (Q.adicCompletion D.host.E) a := by rw [hΦ.inc]; rfl

theorem ev_eq_zero (hΦ : Comp D Φ) {z : AE D} (hz : finPart D z = 0) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ z Q = 0 := by
  let u : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)
  have h0 : finPart D u = 0 := TensorProduct.zero_tmul _ _
  have h1 : infPart D u = 1 := rfl
  have h2 : z = u * z := by
    refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
    · rw [RingHom.map_mul, h1, one_mul]
    · rw [RingHom.map_mul, hz, mul_zero]
  have h3 : Φ u Q = 0 := (hΦ.base _ Q).trans (map_zero _)
  rw [h2, ev_mul, h3, zero_mul]

theorem toEAf_surj (s : Datum.EAf D) : ∃ z : AE D, toEAf D z = s := by
  obtain ⟨y, rfl⟩ := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective s
  obtain ⟨z, -, hz⟩ := GlobalTheory.PlaceIdem.parts_surj D 0 y
  exact ⟨z, congrArg (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) hz⟩

theorem val_le_one (hΦ : Comp D Φ) {z : AE D} (hz : toEAf D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) : Valued.v (Φ z Q) ≤ 1 :=
  (hΦ.int z).1 ((mem_intAE_iff _).2 hz) Q

theorem val_lt_one_of_mem (hΦ : Comp D Φ) (P : HeightOneSpectrum (𝓞 D.host.E))
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (hs : s ∈ idS D.host.F P.asIdeal) :
    ∀ z : AE D, toEAf D z = s → Valued.v (Φ z P) < 1 := by
  have key : ∃ z : AE D, toEAf D z = s ∧ Valued.v (Φ z P) < 1 := by
    refine exists_lift_lt_one Valued.v (toEAf D) (evAt Φ P) (Formalism.L2.Herm.intAf D.host.F D.host.E)
      (oToS D.host.F D.host.E) P.asIdeal toEAf_surj (fun z hz => val_le_one hΦ hz P) (fun a ha => ?_) s hs
    refine ⟨incA D a, rfl, ?_⟩
    change Valued.v (Φ (incA D a) P) < 1
    rw [ev_inc hΦ, val_alg]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) P a).2 ha
  obtain ⟨w, hw, h⟩ := key
  intro z hz
  have h1 : finPart D (z - w) = 0 := by
    apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    change toEAf D (z - w) = _
    rw [RingHom.map_sub, hz, hw, sub_self, map_zero]
  have h2 := ev_eq_zero hΦ h1 P
  rw [ev_sub, sub_eq_zero] at h2
  rwa [h2]

theorem exists_modulus (hΦ : Comp D Φ) (c : (AE D)ˣ →* Circle) (hc : Continuous c) :
    ∃ N : ℕ, 0 < N ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (y : (AE D)ˣ), infPart D (y : AE D) = 1 →
      (∀ Q, Q ≠ P → Φ (y : AE D) Q = 1) → Valued.v (Φ (y : AE D) P) = 1 →
      Valued.v (Φ (y : AE D) P - 1) ≤ P.valuation D.host.E (N : D.host.E) → c y = 1 := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc
  refine ⟨N, hN, fun P y h0 h1 h2 h3 => ?_⟩
  have hN0 : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hv : ∀ Q, Valued.v (Φ (y : AE D) Q) = 1 := fun Q => by
    by_cases hQ : Q = P
    · rw [hQ, h2]
    · rw [h1 Q hQ, map_one]
  have hv' : ∀ Q, Valued.v (Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q) = 1 := fun Q => by
    have : Valued.v (Φ (y : AE D) Q) * Valued.v (Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q) = 1 := by
      rw [← map_mul, ← ev_mul, Units.mul_inv, ev_one, map_one]
    rwa [hv, one_mul] at this
  refine hker y ⟨h0, (hΦ.int _).2 fun Q => (hv Q).le, (hΦ.int _).2 fun Q => (hv' Q).le⟩
    ⟨finPart D (incA D (N : D.host.E)⁻¹ * ((y : AE D) - 1)), (hΦ.int _).2 fun Q => ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, ev_sub, ev_one, ev_inc hΦ, map_mul, val_alg, map_inv₀]
    by_cases hQ : Q = P
    · subst hQ
      exact (inv_mul_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hN0))).2 h3
    · rw [h1 Q hQ, sub_self, map_zero, mul_zero]
      exact zero_le
  · have e : (N : AE D) * (incA D (N : D.host.E)⁻¹ * ((y : AE D) - 1)) = (y : AE D) - 1 := by
      rw [← mul_assoc, ← map_natCast (incA D) N, ← RingHom.map_mul, mul_inv_cancel₀ hN0, RingHom.map_one, one_mul]
    rw [nsmul_eq_mul, ← map_natCast (finPart D) N, ← RingHom.map_mul, e, RingHom.map_sub, RingHom.map_one]

theorem val_sub_lt_one (hΦ : Comp D Φ) (P : Pl D.host.E) (x : AE D)
    (hi : toEAf D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (b : 𝓞 D.host.E)
    (hb : resS D.host.F P ⟨toEAf D x, hi⟩ = Ideal.Quotient.mk P.asIdeal b) :
    Valued.v (Φ x P - algebraMap D.host.E (P.adicCompletion D.host.E) (b : D.host.E)) < 1 := by
  have hm : (⟨toEAf D (x : AE D), hi⟩ - oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈
      idS D.host.F P.asIdeal := by
    have h0 : resS D.host.F P (⟨toEAf D (x : AE D), hi⟩ - oToS D.host.F D.host.E b) = 0 := by
      rw [RingHom.map_sub, resS_oToS, hb, sub_self]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (cmpS D.host.F P.asIdeal)
      (cmpS_bij (F := D.host.F) P.asIdeal P.ne_bot)).symm.injective).1 h0
  have h1 := val_lt_one_of_mem hΦ P _ hm ((x : AE D) - incA D b) (by rw [RingHom.map_sub]; rfl)
  rw [ev_sub, ev_inc hΦ] at h1
  exact h1

theorem resAt_of_tame (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ) (P : Pl D.host.E)
    (a : (kP P)ˣ →* ℂˣ) (ht : χ.TameAt P) (ha : IsRes χ P a) : GlobalTheory.StepLaw.ResAt c P a := by
  intro e he x hx hi u hu
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨d0, d1, d2⟩ := delta_of_isIdemAt hΦ he
  obtain ⟨N, hN, hker⟩ := exists_modulus hΦ c hc.1.1
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  have hbP : b ∉ P.asIdeal := fun h => by
    have := P.isPrime
    exact u.ne_zero (hb.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 h))
  have hb0 : (b : D.host.E) ≠ 0 := fun h => hbP (by rw [RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
  have hbv : P.valuation D.host.E (b : D.host.E) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) P (r := b)).2 hbP
  have h1 := val_sub_lt_one hΦ P x hi b (hu.symm.trans hb.symm)
  have h2 : Valued.v (Φ (x : AE D) P) = 1 := by
    rw [← hbv, ← val_alg]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rwa [val_alg, hbv]
  obtain ⟨k, k1, k2, k3⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P (Φ (x : AE D) P) (fun h => by
    rw [h, map_zero] at h2
    exact zero_ne_one h2)
  rw [h2] at k1
  rw [← k1, mul_one] at k2 k3
  have hpl : IsPlIdem D e P := by
    obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := he
    exact ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
  obtain ⟨l, hl⟩ : ∃ l : (AE D)ˣ, (l : AE D) = 1 + e * (incA D (k : D.host.E) - 1) := ⟨locU hpl.1 k, rfl⟩
  obtain ⟨y, hy, hy'⟩ := exists_units_quot x l hl
  have hyP : Φ (x : AE D) P = Φ (y : AE D) P * algebraMap D.host.E _ (k : D.host.E) := by
    rw [← ev_inc hΦ]
    exact map_eq_mul_of_supp (evAt Φ P) d1 hy'
  have hcy : c y = 1 := by
    refine hker P y (map_eq_one_of_supp (infPart D) d0 hx hy')
      (fun Q hQ => map_eq_one_of_supp (evAt Φ Q) (d2 Q hQ) hx hy') ?_ ?_
    · rwa [hyP, map_mul, val_alg, ← k1, mul_one] at h2
    · rwa [hyP, ← sub_one_mul, map_mul, val_alg, ← k1, mul_one] at k2
  have hcx : c x = c l := by rw [hy, map_mul, hcy, one_mul]
  rw [ha b (Units.mk0 _ hb0) u rfl hb.symm, hcx, hc.2 P e hpl k l hl,
    locK_eq_of_tame χ P ht k (Units.mk0 _ hb0) k1.symm hbv]
  have e5 : algebraMap D.host.E (P.adicCompletion D.host.E) ((k : D.host.E) - (b : D.host.E)) =
      (Φ (x : AE D) P - algebraMap D.host.E _ (b : D.host.E)) - (Φ (x : AE D) P - algebraMap D.host.E _ (k : D.host.E)) := by
    rw [map_sub]
    ring
  rw [Units.val_mk0, ← val_alg, e5]
  exact Valuation.map_sub_le _ (le_exp_of_lt_one h1) k3

theorem resAt_of_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ PP : Pl D.host.E, (∀ a : (kP PP)ˣ →* ℂˣ, χ.TameAt PP → IsRes χ PP a → GlobalTheory.StepLaw.ResAt c PP a) ∧ (χ.UnrAt PP → GlobalTheory.StepLaw.ResAt c PP 1) := by
  intro D c χ hc P
  refine ⟨fun a => resAt_of_tame c χ hc P a, fun h => resAt_of_tame c χ hc P 1 (fun x hx _ => h x hx) ?_⟩
  intro b k u hk hu
  refine (h (atFin P k) ?_).symm
  change Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1
  rw [val_alg, hk]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) P (r := b)).2 fun hb => ?_
  have := P.isPrime
  exact u.ne_zero (hu.trans (Ideal.Quotient.eq_zero_iff_mem.2 hb))

end GlobalTheory.ResLoc

end
