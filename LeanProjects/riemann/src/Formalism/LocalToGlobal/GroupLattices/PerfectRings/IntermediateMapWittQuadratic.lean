import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.CharZeroWittQuadratic

noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.FormalGroupSystem IsLocalRing IntermediateField Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

instance instCharZeroWW : CharZero (WW p) := by
  obtain ⟨q, hq⟩ := CharP.exists (WW p)
  rcases CharP.char_is_prime_or_zero (WW p) q with h | h
  · exfalso
    have h0 : ((q : ℕ) : WW p) = 0 := CharP.cast_eq_zero _ q
    have h1 : ((q : ℕ) : kb p) = 0 := by
      have := congrArg (WittVector.constantCoeff (p := p) (R := kb p)) h0
      rwa [map_natCast, map_zero] at this
    have h2 : p ∣ q := (CharP.cast_eq_zero_iff (kb p) p q).1 h1
    have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h2
    exact (WittVector.irreducible p (k := kb p)).ne_zero (h3 ▸ h0)
  · subst h
    exact CharP.charP_to_charZero _

instance charZero_witt_fraction : CharZero (K0 p) :=
  charZero_of_injective_algebraMap (IsFractionRing.injective (WW p) (K0 p))

theorem completeWW : IsAdicComplete (maximalIdeal (WW p)) (WW p) := by
  rw [(WittVector.irreducible p (k := kb p)).maximalIdeal_eq]
  infer_instance

abbrev Kc : Type := AlgebraicClosure (K0 p)

def Oc : Subring (Kc p) := (integralClosure (WW p) (Kc p)).toSubring

theorem mem_Oc (x : Kc p) : x ∈ Oc p ↔ IsIntegral (WW p) x := Iff.rfl

theorem witt_mem_integers_Cp (x : WW p) : algebraMap (K0 p) (Kc p) (algebraMap (WW p) (K0 p) x) ∈ Oc p := by
  rw [mem_Oc, ← IsScalarTower.algebraMap_apply]
  exact isIntegral_algebraMap

theorem Oc_val (x : Kc p) : x ∈ Oc p ∨ x⁻¹ ∈ Oc p := by
  have hx : IsIntegral (K0 p) x := Algebra.IsIntegral.isIntegral x
  have : FiniteDimensional (K0 p) (K0 p)⟮x⟯ := adjoin.finiteDimensional hx
  have hD : IsDiscreteValuationRing (integralClosure (WW p) (K0 p)⟮x⟯) :=
    IntCl.isDVR (WW p) (K0 p) (K0 p)⟮x⟯ (completeWW p)
  have hF : IsFractionRing (integralClosure (WW p) (K0 p)⟮x⟯) (K0 p)⟮x⟯ := IntCl.frac (WW p) (K0 p) (K0 p)⟮x⟯
  have : IsScalarTower (WW p) (K0 p)⟮x⟯ (Kc p) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let x' : (K0 p)⟮x⟯ := ⟨x, mem_adjoin_simple_self _ _⟩
  have key : ∀ y : (K0 p)⟮x⟯, IsLocalization.IsInteger (integralClosure (WW p) (K0 p)⟮x⟯) y →
      IsIntegral (WW p) (y : Kc p) := by
    rintro y ⟨b, rfl⟩
    exact (b.2 : IsIntegral (WW p) (b : (K0 p)⟮x⟯)).map (IsScalarTower.toAlgHom (WW p) (K0 p)⟮x⟯ (Kc p))
  rcases ValuationRing.isInteger_or_isInteger (integralClosure (WW p) (K0 p)⟮x⟯) x' with h | h
  · exact Or.inl (key _ h)
  · exact Or.inr (key _ h)

theorem Oc_rank1 (x : Kc p) (_hx : x ≠ 0) : ∃ m : ℕ, (p : Kc p) ^ m / x ∈ Oc p := by
  have halg : IsAlgebraic (WW p) x⁻¹ :=
    (IsFractionRing.isAlgebraic_iff (WW p) (K0 p) (Kc p)).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨a, ha, hint⟩ := halg.exists_integral_multiple
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' a ha
  refine ⟨m, ?_⟩
  rw [mem_Oc]
  have h1 : (p : Kc p) ^ m / x = ((u⁻¹ : (WW p)ˣ) : WW p) • (a • x⁻¹) := by
    rw [smul_smul, hu, mul_comm ((p : WW p) ^ m), ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow,
      map_natCast, div_eq_mul_inv]
  rw [h1]
  exact hint.smul _

theorem p_inv_notMem_Oc : (p : Kc p)⁻¹ ∉ Oc p := by
  rw [mem_Oc]
  intro h
  have hK : (p : Kc p)⁻¹ = algebraMap (K0 p) (Kc p) (p : K0 p)⁻¹ := by simp
  rw [hK, isIntegral_algebraMap_iff (algebraMap (K0 p) (Kc p)).injective] at h
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  have h1 : algebraMap (WW p) (K0 p) (y * p) = 1 := by
    rw [map_mul, hy, map_natCast, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hp.out.ne_zero)]
  have h2 : y * (p : WW p) = 1 := IsFractionRing.injective (WW p) (K0 p) (by rw [h1, map_one])
  exact (WittVector.irreducible p).not_isUnit ⟨⟨(p : WW p), y, by rw [mul_comm]; exact h2, h2⟩, rfl⟩

variable (n : ℕ)

def gF : F2 p n →+* kb p := (IsAlgClosed.lift : F2 p n →ₐ[ZMod p] kb p).toRingHom

def gW : W2 p n →+* Kc p := (algebraMap (WW p) (Kc p)).comp (WittVector.map (gF p n))

theorem gW_injective : Function.Injective (gW p n) := by
  have h1 : Function.Injective (algebraMap (WW p) (Kc p)) := by
    rw [IsScalarTower.algebraMap_eq (WW p) (K0 p) (Kc p)]
    exact (algebraMap (K0 p) (Kc p)).injective.comp (IsFractionRing.injective (WW p) (K0 p))
  exact h1.comp (WittVector.map_injective _ (gF p n).injective)

theorem gW_mem (a : W2 p n) : gW p n a ∈ Oc p := by
  rw [gW, RingHom.comp_apply, IsScalarTower.algebraMap_apply (WW p) (K0 p) (Kc p)]
  exact witt_mem_integers_Cp p _

def rtP : Kc p := (IsAlgClosed.exists_pow_nat_eq (p : Kc p) (n := 2) (by norm_num)).choose

theorem sqrtPrime_sq : rtP p ^ 2 = (p : Kc p) := by
  unfold rtP
  exact (IsAlgClosed.exists_pow_nat_eq (p : Kc p) (n := 2) (by norm_num)).choose_spec

theorem sqrtPrime_mem : rtP p ∈ Oc p := by
  rw [mem_Oc]
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (p : WW p), Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  simp [sqrtPrime_sq]

def gO : OO p n →+* Kc p where
  toFun z := gW p n z.re + gW p n z.im * rtP p
  map_one' := by
    show gW p n (1 : OO p n).re + gW p n (1 : OO p n).im * rtP p = 1
    rw [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, map_one, map_zero, zero_mul, add_zero]
  map_zero' := by
    show gW p n (0 : OO p n).re + gW p n (0 : OO p n).im * rtP p = 0
    rw [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, map_zero, zero_mul, add_zero]
  map_add' x y := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring
  map_mul' x y := by
    have h : rtP p * rtP p = (p : Kc p) := by rw [← sq, sqrtPrime_sq]
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, map_natCast, zero_mul,
      add_zero]
    linear_combination (gW p n x.im * gW p n y.im) * (-h)

theorem gO_apply (z : OO p n) : gO p n z = gW p n z.re + gW p n z.im * rtP p := rfl

theorem gO_mem (z : OO p n) : gO p n z ∈ Oc p := by
  rw [gO_apply]
  exact (Oc p).add_mem (gW_mem p n _) ((Oc p).mul_mem (gW_mem p n _) (sqrtPrime_mem p))

theorem gO_injective : Function.Injective (gO p n) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  rw [gO_apply] at hz
  by_cases hb : z.im = 0
  · have ha : gW p n z.re = 0 := by rw [hb, map_zero, zero_mul, add_zero] at hz; exact hz
    have ha' : z.re = 0 := gW_injective p n (by rw [ha, map_zero])
    ext <;> simp [ha', hb]
  · exfalso
    have hbK : gW p n z.im ≠ 0 := fun h => hb (gW_injective p n (by rw [h, map_zero]))
    have hr : rtP p = -gW p n z.re / gW p n z.im := by
      rw [eq_div_iff hbK]
      linear_combination hz
    have hcr : algebraMap (K0 p) (Kc p) (-(algebraMap (WW p) (K0 p) (WittVector.map (gF p n) z.re)) /
        algebraMap (WW p) (K0 p) (WittVector.map (gF p n) z.im)) = rtP p := by
      rw [hr]
      simp [gW, IsScalarTower.algebraMap_apply (WW p) (K0 p) (Kc p)]
    set c : K0 p := -(algebraMap (WW p) (K0 p) (WittVector.map (gF p n) z.re)) /
        algebraMap (WW p) (K0 p) (WittVector.map (gF p n) z.im) with hc
    have hc2 : c ^ 2 = (p : K0 p) := by
      apply (algebraMap (K0 p) (Kc p)).injective
      rw [map_pow, hcr, sqrtPrime_sq, map_natCast]
    have hci : IsIntegral (WW p) c :=
      ⟨Polynomial.X ^ 2 - Polynomial.C (p : WW p), Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp [hc2]⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hci
    have hy2 : y * y = (p : WW p) :=
      IsFractionRing.injective (WW p) (K0 p) (by rw [map_mul, hy, ← sq, hc2, map_natCast])
    rcases (WittVector.irreducible p).isUnit_or_isUnit hy2.symm with h | h
    · have hpu : IsUnit (p : WW p) := by rw [← hy2]; exact h.mul h
      exact (WittVector.irreducible p).not_isUnit hpu
    · have hpu : IsUnit (p : WW p) := by rw [← hy2]; exact h.mul h
      exact (WittVector.irreducible p).not_isUnit hpu

def gK : KO p n →+* Kc p := IsFractionRing.lift (gO_injective p n)

theorem gK_alg (z : OO p n) : gK p n (algebraMap (OO p n) (KO p n) z) = gO p n z := by
  unfold gK
  exact IsFractionRing.lift_algebraMap _ _

variable {p n}

def gL (L : IntermediateField (KO p n) (Om p n)) : L →+* Kc p :=
  letI : Algebra (KO p n) (Kc p) := (gK p n).toAlgebra
  (IsAlgClosed.lift : L →ₐ[KO p n] Kc p).toRingHom

theorem gL_alg (L : IntermediateField (KO p n) (Om p n)) (y : KO p n) :
    gL L (algebraMap (KO p n) L y) = gK p n y := by
  unfold gL
  letI : Algebra (KO p n) (Kc p) := (gK p n).toAlgebra
  exact (IsAlgClosed.lift : L →ₐ[KO p n] Kc p).commutes y

theorem gL_algO (L : IntermediateField (KO p n) (Om p n)) (z : OO p n) :
    gL L (algebraMap (OO p n) L z) = gO p n z := by
  rw [IsScalarTower.algebraMap_apply (OO p n) (KO p n) L, gL_alg, gK_alg]

theorem gL_mem (L : IntermediateField (KO p n) (Om p n)) {x : L} (hx : IsIntegral (OO p n) x) : gL L x ∈ Oc p := by
  obtain ⟨f, hfm, hf⟩ := hx
  rw [mem_Oc]
  have hcomp : (gL L).comp (algebraMap (OO p n) L) = gO p n := RingHom.ext fun z => gL_algO L z
  have hroot : Polynomial.eval₂ (gO p n) (gL L x) f = 0 := by
    rw [← hcomp, ← Polynomial.hom_eval₂, hf, map_zero]
  let g : OO p n →+* integralClosure (WW p) (Kc p) :=
    (gO p n).codRestrict (integralClosure (WW p) (Kc p)) fun z => (mem_integralClosure_iff _ _).2 ((mem_Oc p _).1 (gO_mem p n z))
  have hA : IsIntegral (integralClosure (WW p) (Kc p)) (gL L x) := by
    refine ⟨f.map g, hfm.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    have hg : (algebraMap (integralClosure (WW p) (Kc p)) (Kc p)).comp g = gO p n := RingHom.ext fun z => rfl
    rw [hg, hroot]
  exact isIntegral_trans _ hA

theorem Oc_K (L : IntermediateField (KO p n) (Om p n)) [FiniteDimensional (KO p n) L] (x : L) :
    gL L x ∈ Oc p ↔ x ∈ Set.range (algebraMap (OL p n L) L) := by
  constructor
  · intro hx
    by_contra hnot
    have hF : IsFractionRing (OL p n L) L := IntCl.frac (OO p n) (KO p n) L
    rcases ValuationRing.isInteger_or_isInteger (OL p n L) x with h | ⟨b, hb⟩
    · exact hnot h
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hnot ⟨0, map_zero _⟩

    have hbm : b ∈ maximalIdeal (OL p n L) := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, rfl⟩
      refine hnot ⟨((u⁻¹ : (OL p n L)ˣ) : OL p n L), ?_⟩
      have h1 : algebraMap (OL p n L) L (u : OL p n L) * algebraMap (OL p n L) L ((u⁻¹ : (OL p n L)ˣ) : OL p n L) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [hb] at h1
      exact (eq_inv_of_mul_eq_one_right h1).trans (inv_inv x)
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OL p n L)
    have hp0 : (p : OL p n L) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hbm
    obtain ⟨c, rfl⟩ := hbm

    have h2 : (ϖ * c) ^ e = (p : OL p n L) * ((u : OL p n L) * c ^ e) := by
      rw [mul_pow, ← hu]; ring
    have h3 : (x⁻¹) ^ e = (p : L) * algebraMap (OL p n L) L ((u : OL p n L) * c ^ e) := by
      rw [← hb, ← map_pow, h2, map_mul, map_natCast]
    have h4 : gL L (algebraMap (OL p n L) L ((u : OL p n L) * c ^ e)) ∈ Oc p :=
      gL_mem L ((u : OL p n L) * c ^ e).2
    have h5 : (p : Kc p)⁻¹ = (gL L x) ^ e * gL L (algebraMap (OL p n L) L ((u : OL p n L) * c ^ e)) := by
      have h6 := congrArg (gL L) h3
      rw [map_pow, map_inv₀, map_mul, map_natCast] at h6
      have hg : gL L x ≠ 0 := (_root_.map_ne_zero _).2 hx0
      have h7 : (gL L x) ^ e * ((gL L x)⁻¹) ^ e = 1 := by rw [← mul_pow, mul_inv_cancel₀ hg, one_pow]
      rw [h6] at h7
      have h8 : (p : Kc p) * ((gL L x) ^ e * gL L (algebraMap (OL p n L) L ((u : OL p n L) * c ^ e))) = 1 := by
        rw [← h7]; ring
      exact (eq_inv_of_mul_eq_one_right h8).symm
    exact p_inv_notMem_Oc p (h5 ▸ (Oc p).mul_mem ((Oc p).pow_mem hx e) h4)
  · rintro ⟨b, rfl⟩
    exact gL_mem L b.2

def gWW (p : ℕ) [Fact p.Prime] (n : ℕ) : W2 p n →+* WW p := WittVector.map (gF p n)

theorem intermediate_map_witt_quadratic (L : IntermediateField (KO p n) (Om p n)) (a : W2 p n) :
    gL L (algebraMap (OO p n) L (algebraMap (W2 p n) (OO p n) a)) =
      algebraMap (K0 p) (Kc p) (algebraMap (WW p) (K0 p) (gWW p n a)) := by
  rw [gL_algO, gO_apply]
  simp [gW, gWW, IsScalarTower.algebraMap_apply (WW p) (K0 p) (Kc p)]

theorem gL_jO (L : IntermediateField (KO p n) (Om p n)) (a : WQ p n) :
    gL L (algebraMap (OO p n) L (jO p n a)) =
      algebraMap (K0 p) (Kc p) (algebraMap (WW p) (K0 p) (gWW p n (jW p n a))) := by
  rw [jO, RingHom.comp_apply]
  exact intermediate_map_witt_quadratic L (jW p n a)

theorem exists_inv_pow {B L : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field L] [Algebra B L]
    [IsFractionRing B L] {π : B} (hπ : π ≠ 0) {x : L} (hx : x ∉ Set.range (algebraMap B L)) :
    ∃ (e : ℕ) (d : B), x⁻¹ ^ e = algebraMap B L (π * d) := by
  have hx0 : x ≠ 0 := fun h => hx ⟨0, by rw [h, map_zero]⟩
  obtain ⟨y, hy⟩ : ∃ y : B, algebraMap B L y = x⁻¹ := by
    rcases ValuationRing.isInteger_or_isInteger B x with h | h
    · obtain ⟨z, hz⟩ := RingHom.mem_rangeS.1 h
      exact absurd ⟨z, hz⟩ hx
    · exact RingHom.mem_rangeS.1 h
  have hyu : ¬ IsUnit y := by
    rintro ⟨u, rfl⟩
    apply hx
    refine ⟨↑u⁻¹, ?_⟩
    rw [← inv_inv x, ← hy]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact inv_ne_zero hx0 hy.symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  obtain ⟨m, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ hϖ
  have hk : k ≠ 0 := by
    rintro rfl
    apply hyu
    rw [hu, pow_zero, mul_one]
    exact u.isUnit
  have hdvd : π ∣ y ^ m := by
    rw [hu', hu, mul_pow]
    refine (Units.mul_left_dvd).2 (Dvd.dvd.mul_left ?_ _)
    rw [← pow_mul]
    exact pow_dvd_pow ϖ (by nlinarith [Nat.pos_of_ne_zero hk])
  obtain ⟨d, hd⟩ := hdvd
  exact ⟨m, d, by rw [← hd, map_pow, hy]⟩

theorem exists_pow_of_notMem_Oc {x : Kc p} (hx : x ∉ Oc p) :
    ∃ (e : ℕ) (d : Kc p), d ∈ Oc p ∧ x⁻¹ ^ e = (p : Kc p) * d := by
  have hxi : IsIntegral (K0 p) x := Algebra.IsIntegral.isIntegral x
  have : FiniteDimensional (K0 p) (K0 p)⟮x⟯ := adjoin.finiteDimensional hxi
  have hD : IsDiscreteValuationRing (integralClosure (WW p) (K0 p)⟮x⟯) :=
    IntCl.isDVR (WW p) (K0 p) (K0 p)⟮x⟯ (completeWW p)
  have hF : IsFractionRing (integralClosure (WW p) (K0 p)⟮x⟯) (K0 p)⟮x⟯ := IntCl.frac (WW p) (K0 p) (K0 p)⟮x⟯
  have : IsScalarTower (WW p) (K0 p)⟮x⟯ (Kc p) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let x' : (K0 p)⟮x⟯ := ⟨x, mem_adjoin_simple_self _ _⟩
  have key : ∀ b : integralClosure (WW p) (K0 p)⟮x⟯, ((b : (K0 p)⟮x⟯) : Kc p) ∈ Oc p := fun b =>
    (b.2 : IsIntegral (WW p) (b : (K0 p)⟮x⟯)).map (IsScalarTower.toAlgHom (WW p) (K0 p)⟮x⟯ (Kc p))
  have hx' : x' ∉ Set.range (algebraMap (integralClosure (WW p) (K0 p)⟮x⟯) (K0 p)⟮x⟯) := by
    rintro ⟨b, hb⟩
    exact hx (by have := key b; rwa [show ((b : (K0 p)⟮x⟯) : Kc p) = x from congrArg Subtype.val hb] at this)
  have hp0 : (p : integralClosure (WW p) (K0 p)⟮x⟯) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨e, d, hd⟩ := exists_inv_pow hp0 hx'
  refine ⟨e, ((d : (K0 p)⟮x⟯) : Kc p), key d, ?_⟩
  have := congrArg (fun z : (K0 p)⟮x⟯ => (z : Kc p)) hd
  simpa using this

end Formalism.L2.G
