import Mathlib
import GroundTheory.PAdicHodge.WACommon
import GroundTheory.PAdicHodge.UnramifiedFrob
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WittTilt

open _root_.WittVector PhiGamma EigenWitt ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "W̄" => WittVector p (Fpbar p)
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)

section Embeddings

theorem isUnit_of_isUnit_p {S : Type*} [CommRing S] (f : W̄ →+* S) (hf : IsUnit (f p))
    (y : nonZeroDivisors W̄) : IsUnit (f y) := by
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' (y : W̄) (nonZeroDivisors.coe_ne_zero y)
  rw [hu, map_mul, map_pow]
  exact (hf.pow _).mul (u.isUnit.map _)

theorem isUnit_wittFpbar_to_BCrisPlus (y : nonZeroDivisors W̄) :
    IsUnit (((algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)).comp
      ((algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p)).comp wittToAInf)) (y : W̄)) :=
  isUnit_of_isUnit_p _ (by rw [map_natCast]; exact isUnit_p_bCrisPlus) y

variable (p) in

def wittFpbarToBCrisPlus : WFrac p →+* BCrisPlus ℂ_[p] p :=
  IsLocalization.lift (M := nonZeroDivisors W̄) (isUnit_wittFpbar_to_BCrisPlus (p := p))

theorem wittFpbarToBCrisPlus_algebraMap (w : W̄) :
    wittFpbarToBCrisPlus p (algebraMap W̄ (WFrac p) w) =
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)
        (algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (wittToAInf w)) :=
  IsLocalization.lift_eq _ w

theorem iotaPlus_wittFpbarToBCrisPlus_algebraMap (w : W̄) :
    iotaPlus ℂ_[p] p (wittFpbarToBCrisPlus p (algebraMap W̄ (WFrac p) w)) =
      wittToBDeRhamPlus (normInteger ℂ_[p]) p (wittToAInf w) := by
  rw [wittFpbarToBCrisPlus_algebraMap, iotaPlus_algebraMap, iota_algebraMap]

theorem wittFpbarToBCrisPlus_injective : Function.Injective (wittFpbarToBCrisPlus p) := by
  have := (iotaPlus ℂ_[p] p).domain_nontrivial
  exact (wittFpbarToBCrisPlus p).injective

set_option maxHeartbeats 1600000 in
theorem wittFpbarToBCrisPlus_frobFrac (x : WFrac p) :
    wittFpbarToBCrisPlus p (frobFrac p x) = phiPlus ℂ_[p] p (wittFpbarToBCrisPlus p x) := by
  have : (wittFpbarToBCrisPlus p).comp (frobFrac p) =
      (phiPlus ℂ_[p] p).comp (wittFpbarToBCrisPlus p) :=
    IsLocalization.ringHom_ext (nonZeroDivisors W̄) (RingHom.ext fun w => by
      show wittFpbarToBCrisPlus p (frobFrac p (algebraMap W̄ (WFrac p) w)) =
        phiPlus ℂ_[p] p (wittFpbarToBCrisPlus p (algebraMap W̄ (WFrac p) w))
      rw [frobFrac_algebraMap, wittFpbarToBCrisPlus_algebraMap, wittFpbarToBCrisPlus_algebraMap,
        phiPlus_algebraMap, phi_algebraMap, WittVector.frobeniusEquiv_apply, wittToAInf,
        map_frobenius_comm])
  exact RingHom.congr_fun this x

set_option maxHeartbeats 1600000 in
theorem wittFpbarToBCrisPlus_padicToWFrac (q : ℚ_[p]) :
    wittFpbarToBCrisPlus p (padicToWFrac p q) = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q := by
  have : (wittFpbarToBCrisPlus p).comp (padicToWFrac p) = padicToBCrisPlus :=
    IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun z => by
      show wittFpbarToBCrisPlus p (padicToWFrac p (algebraMap ℤ_[p] ℚ_[p] z)) =
        padicToBCrisPlus (algebraMap ℤ_[p] ℚ_[p] z)
      rw [padicToWFrac_padicInt, wittFpbarToBCrisPlus_algebraMap, wittToAInf_padicIntToWittFpbar,
        padicToBCrisPlus, IsLocalization.lift_eq]
      rfl)
  exact RingHom.congr_fun this q

theorem isUnit_wittFpbar_to_away_p (y : nonZeroDivisors W̄) :
    IsUnit ((algebraMap (AInf ℂ_[p] p) 𝔸).comp wittToAInf (y : W̄)) :=
  isUnit_of_isUnit_p _ (by
    rw [RingHom.comp_apply, map_natCast]
    simpa using IsLocalization.Away.algebraMap_isUnit (S := 𝔸) (p : AInf ℂ_[p] p)) y

variable (p) in

def wittFpbarToAway : WFrac p →+* 𝔸 :=
  IsLocalization.lift (M := nonZeroDivisors W̄) (isUnit_wittFpbar_to_away_p (p := p))

theorem wittFpbarToAway_algebraMap (w : W̄) :
    wittFpbarToAway p (algebraMap W̄ (WFrac p) w) = algebraMap (AInf ℂ_[p] p) 𝔸 (wittToAInf w) :=
  IsLocalization.lift_eq _ w

theorem toB_wittFpbarToAway (x : WFrac p) : toB ℂ_[p] p (wittFpbarToAway p x) = wittFpbarToB p x := by
  have : (toB ℂ_[p] p).comp (wittFpbarToAway p) = wittFpbarToB p :=
    IsLocalization.ringHom_ext (nonZeroDivisors W̄) (RingHom.ext fun w => by
      simp only [RingHom.comp_apply]
      rw [wittFpbarToAway_algebraMap, toB_algebraMap, wittFpbarToB_algebraMap]
      rfl)
  exact RingHom.congr_fun this x

theorem toBDeRhamPlus_wittFpbarToAway (x : WFrac p) :
    toBDeRhamPlus (normInteger ℂ_[p]) p (wittFpbarToAway p x) =
      iotaPlus ℂ_[p] p (wittFpbarToBCrisPlus p x) := by
  have : (toBDeRhamPlus (normInteger ℂ_[p]) p).comp (wittFpbarToAway p) =
      (iotaPlus ℂ_[p] p).comp (wittFpbarToBCrisPlus p) :=
    IsLocalization.ringHom_ext (nonZeroDivisors W̄) (RingHom.ext fun w => by
      simp only [RingHom.comp_apply]
      rw [wittFpbarToAway_algebraMap, iotaPlus_wittFpbarToBCrisPlus_algebraMap]
      rfl)
  exact RingHom.congr_fun this x

end Embeddings

section Unramified

theorem exists_fpbar_rootOfUnity {ζ : PadicAlgCl p} {m : ℕ} (hm : 0 < m) (hc : m.Coprime p)
    (hζ : ζ ^ m = 1) :
    ∃ a : Fpbar p, a ^ m = 1 ∧ ((fontaineTheta (normInteger ℂ_[p]) p
      (teichmuller p (fpbarToPreTilt a)) : normInteger ℂ_[p]) : ℂ_[p]) = (ζ : ℂ_[p]) := by
  set z : ℕ → PadicAlgCl p := fun n => ζ ^ p ^ (n * (m.totient - 1))
  have hzm' : ∀ n, z n ^ m = 1 := fun n => by
    simp only [z]
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hzm : ∀ n, (z n : ℂ_[p]) ^ m = 1 := fun n => by
    rw [PadicComplex.coe_eq, ← map_pow, hzm' n, map_one]
  have hmem : ∀ n, (z n : ℂ_[p]) ∈ normInteger ℂ_[p] := fun n =>
    mem_normInteger.2 (ACris.norm_eq_one_of_pow_eq_one hm (hzm n)).le
  set y : ℕ → normInteger ℂ_[p] := fun n => ⟨(z n : ℂ_[p]), hmem n⟩
  have hy : ∀ n, y (n + 1) ^ p = y n := fun n => Subtype.ext (by
    simp only [y, SubmonoidClass.coe_pow]
    rw [PadicComplex.coe_eq, PadicComplex.coe_eq, ← map_pow]
    exact congrArg _ (rootOfUnity_compatible hm hc hζ n))
  set ζf : 𝒪♭ := IsPerfectoidField.ofCompatible p y hy
  have hζf : ζf ^ m = 1 := IsPerfectoidField.preTilt_ext p fun n => by
    rw [map_pow, IsPerfectoidField.coeff_ofCompatible, ← map_pow, map_one]
    have : y n ^ m = 1 := Subtype.ext (by
      simp only [y, SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hzm n)
    rw [this, map_one]
  have hfix : ζf ^ p ^ m.totient = ζf := by
    have hmod : p ^ m.totient % m = 1 % m := Nat.ModEq.pow_totient (Nat.Coprime.symm hc)
    rw [pow_eq_pow_mod_of_pow_eq_one hζf, hmod, ← pow_eq_pow_mod_of_pow_eq_one hζf, pow_one]
  obtain ⟨a, ha⟩ := exists_fpbarToPreTilt_eq (Nat.totient_pos.2 hm) hfix
  refine ⟨a, fpbarToPreTilt_injective (by rw [map_pow, ha, hζf, map_one]), ?_⟩
  rw [ha, fontaineTheta_teichmuller, IsPerfectoidField.untilt_ofCompatible]
  simp [y, z]

theorem iota_teichmuller_fpbar {ζ : PadicAlgCl p} {m : ℕ} (hm : 0 < m) {a : Fpbar p}
    (ha : a ^ m = 1) (hθ : ((fontaineTheta (normInteger ℂ_[p]) p
      (teichmuller p (fpbarToPreTilt a)) : normInteger ℂ_[p]) : ℂ_[p]) = (ζ : ℂ_[p]))
    (hζ : ζ ^ m = 1) :
    iota ℂ_[p] p (algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (teichmuller p (fpbarToPreTilt a))) =
      algClToBdR p ζ := by
  have hT : (teichmuller p (fpbarToPreTilt a) : AInf ℂ_[p] p) ^ m = 1 := by
    rw [← map_pow, ← map_pow, ha, map_one, map_one]
  have hζ0 : (ζ : ℂ_[p]) ≠ 0 := by
    intro h
    have := ACris.norm_eq_one_of_pow_eq_one hm (show (ζ : ℂ_[p]) ^ m = 1 by
      rw [PadicComplex.coe_eq, ← map_pow, hζ, map_one])
    rw [h, norm_zero] at this
    exact zero_ne_one this
  apply eq_of_pow_eq_one_of_theta_eq hm
  · rw [← map_pow, ← map_pow, hT, map_one, map_one]
  · rw [← map_pow, hζ, map_one]
  · rw [thetaAlgHom_apply, thetaField_iota, theta_algebraMap, hθ, thetaAlgHom_algClToBdR]
  · rw [thetaAlgHom_algClToBdR]; exact hζ0

variable (p) in

def wittFpbarRangeBdR : Subalgebra ℚ_[p] 𝔹 :=
  { ((iotaPlus ℂ_[p] p).comp (wittFpbarToBCrisPlus p)).range with
    algebraMap_mem' := fun q => ⟨padicToWFrac p q, by
      rw [RingHom.comp_apply, wittFpbarToBCrisPlus_padicToWFrac, iotaPlus_algebraMap_padic]⟩ }

theorem unramifiedClosure_le_wittFpbarRange :
    (unramifiedClosure p).toSubalgebra ≤ (wittFpbarRangeBdR p).comap (algClToBdR p) := by
  rw [unramifiedClosure, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    fun x _ => Algebra.IsAlgebraic.isAlgebraic x]
  refine Algebra.adjoin_le fun ζ hζ => ?_
  obtain ⟨m, hm, hc, hζm⟩ := hζ
  obtain ⟨a, ha, hθ⟩ := exists_fpbar_rootOfUnity hm hc hζm
  refine ⟨algebraMap W̄ (WFrac p) (teichmuller p a), ?_⟩
  show iotaPlus ℂ_[p] p (wittFpbarToBCrisPlus p (algebraMap W̄ (WFrac p) (teichmuller p a))) =
    algClToBdR p ζ
  rw [iotaPlus_wittFpbarToBCrisPlus_algebraMap, wittToAInf, WittVector.map_teichmuller,
    ← iota_teichmuller_fpbar hm ha hθ hζm, iota_algebraMap]

theorem unramifiedToBCrisPlus_mem_range (u : unramifiedClosure p) :
    unramifiedToBCrisPlus u ∈ (wittFpbarToBCrisPlus p).range := by
  obtain ⟨w, hw⟩ := unramifiedClosure_le_wittFpbarRange u.2
  refine ⟨w, iotaPlus_injective (K := ℂ_[p]) (p := p) ?_⟩
  rw [iotaPlus_unramifiedToBCrisPlus]
  exact hw

variable (p) in

def wittFpbarRangeEquiv : WFrac p ≃+* (wittFpbarToBCrisPlus p).range :=
  RingEquiv.ofBijective (wittFpbarToBCrisPlus p).rangeRestrict
    ⟨fun _ _ h => wittFpbarToBCrisPlus_injective (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

variable (p) in

def unramifiedToWFrac : unramifiedClosure p →+* WFrac p :=
  (wittFpbarRangeEquiv p).symm.toRingHom.comp
    ((unramifiedToBCrisPlus (p := p)).toRingHom.codRestrict _ unramifiedToBCrisPlus_mem_range)

theorem wittFpbarToBCrisPlus_unramifiedToWFrac (u : unramifiedClosure p) :
    wittFpbarToBCrisPlus p (unramifiedToWFrac p u) = unramifiedToBCrisPlus u :=
  congrArg Subtype.val ((wittFpbarRangeEquiv p).apply_symm_apply
    ((unramifiedToBCrisPlus (p := p)).toRingHom.codRestrict _ unramifiedToBCrisPlus_mem_range u))

theorem unramifiedToWFrac_eq_iff {u : unramifiedClosure p} {x : WFrac p} :
    unramifiedToWFrac p u = x ↔ wittFpbarToBCrisPlus p x = unramifiedToBCrisPlus u :=
  ⟨fun h => h ▸ wittFpbarToBCrisPlus_unramifiedToWFrac u,
    fun h => wittFpbarToBCrisPlus_injective (by rw [h, wittFpbarToBCrisPlus_unramifiedToWFrac])⟩

theorem unramifiedToWFrac_injective : Function.Injective (unramifiedToWFrac p) :=
  (unramifiedToWFrac p).injective

theorem toBDeRhamPlus_unramifiedToWFrac (u : unramifiedClosure p) :
    toBDeRhamPlus (normInteger ℂ_[p]) p (wittFpbarToAway p (unramifiedToWFrac p u)) =
      algClToBdR p u := by
  rw [toBDeRhamPlus_wittFpbarToAway, wittFpbarToBCrisPlus_unramifiedToWFrac,
    iotaPlus_unramifiedToBCrisPlus]

theorem exists_unramifiedToWFrac_rootOfUnity {ζ : unramifiedClosure p} {m : ℕ} (hm : 0 < m)
    (hc : m.Coprime p) (hζ : ζ ^ m = 1) :
    ∃ a : Fpbar p, a ^ m = 1 ∧
      unramifiedToWFrac p ζ = algebraMap W̄ (WFrac p) (teichmuller p a) := by
  have hζ' : (ζ : PadicAlgCl p) ^ m = 1 := by rw [← IntermediateField.coe_pow, hζ]; rfl
  obtain ⟨a, ha, hθ⟩ := exists_fpbar_rootOfUnity hm hc hζ'
  refine ⟨a, ha, unramifiedToWFrac_eq_iff.2 (iotaPlus_injective (K := ℂ_[p]) (p := p) ?_)⟩
  rw [iotaPlus_unramifiedToBCrisPlus, iotaPlus_wittFpbarToBCrisPlus_algebraMap, wittToAInf,
    WittVector.map_teichmuller, ← iota_teichmuller_fpbar hm ha hθ hζ', iota_algebraMap]

end Unramified

end WittTilt

end GroundTheory.PAdicHodge
