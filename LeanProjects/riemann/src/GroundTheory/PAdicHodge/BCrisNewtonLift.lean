import Mathlib
import GroundTheory.PAdicHodge.TiltField
import GroundTheory.PAdicHodge.ExtRobbaBounded
import GroundTheory.PAdicHodge.KerFontaineThetaCompFrobeniusEquivSymmPow
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WittTilt

open _root_.WittVector

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)

variable (K p) in

def incl : AInf K p →+* WittVector p K♭ := WittVector.map (algebraMap 𝒪♭ K♭)

theorem incl_coeff (x : AInf K p) (n : ℕ) :
    (incl K p x).coeff n = algebraMap 𝒪♭ K♭ (x.coeff n) :=
  map_coeff _ _ _

theorem incl_injective : Function.Injective (incl K p) := by
  intro x y h
  ext n
  have := congrArg (fun z => z.coeff n) h
  simp only [incl_coeff] at this
  exact IsFractionRing.injective 𝒪♭ K♭ this

theorem incl_teichmuller (a : 𝒪♭) :
    incl K p (teichmuller p a) = teichmuller p (algebraMap 𝒪♭ K♭ a) :=
  map_teichmuller p _ a

theorem natCast_p_ne_zero : (p : WittVector p K♭) ≠ 0 := by
  intro h
  have := coeff_p_pow (p := p) (R := K♭) 1
  rw [pow_one, h] at this
  simp at this

theorem p_mem_nonZeroDivisors : (p : WittVector p K♭) ∈ nonZeroDivisors (WittVector p K♭) :=
  mem_nonZeroDivisors_of_ne_zero natCast_p_ne_zero

variable (K p) in

def intSubring : Subring (WittVector p K♭) := (incl K p).range

variable (K p) in

def teichLift : TeichLift p K♭ (WittVector p K♭) where
  π := p
  red := WittVector.constantCoeff
  red_surjective := constantCoeff_surjective p
  ker_red := ker_constantCoeff
  π_mem_nonZeroDivisors := p_mem_nonZeroDivisors
  isAdicComplete := inferInstance
  int := intSubring K p
  π_mem_int := ⟨p, map_natCast _ _⟩
  norm_red_le_one := by
    rintro _ ⟨y, rfl⟩
    show ‖(incl K p y).coeff 0‖ ≤ 1
    rw [incl_coeff, norm_algebraMap_preTilt]
    exact preTilt_norm_le_one _
  exists_mem_int := by
    intro a ha
    obtain ⟨b, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 ha
    refine ⟨incl K p (teichmuller p b), ⟨_, rfl⟩, ?_⟩
    show (incl K p (teichmuller p b)).coeff 0 = _
    rw [incl_coeff, teichmuller_coeff_zero]
  exists_eq_π_mul := by
    rintro _ ⟨y, rfl⟩ h0
    have h1 : y.coeff 0 = 0 := by
      have : (incl K p y).coeff 0 = 0 := h0
      rw [incl_coeff] at this
      exact (map_eq_zero_iff _ (IsFractionRing.injective 𝒪♭ K♭)).1 this
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 ((mem_span_p_iff_coeff_zero_eq_zero y).2 h1)
    exact ⟨incl K p z, ⟨z, rfl⟩, by rw [← hz, map_mul, map_natCast, mul_comm]⟩
  mem_int_of_approx := by
    intro x hx
    have hc : ∀ n, ∃ b : 𝒪♭, algebraMap 𝒪♭ K♭ b = x.coeff n := by
      intro n
      obtain ⟨y, ⟨z, rfl⟩, hy⟩ := hx (n + 1)
      have h := (mem_span_p_pow_iff_le_coeff_eq_zero _ _).1 hy
      have := (le_coeff_eq_iff_le_sub_coeff_eq_zero.2 h) n (Nat.lt_succ_self n)
      exact ⟨z.coeff n, by rw [this, incl_coeff]⟩
    choose b hb using hc
    refine ⟨WittVector.mk p b, ?_⟩
    ext n
    rw [incl_coeff, ← hb n]
    rfl

@[simp] theorem teichLift_π : (teichLift K p).π = (p : WittVector p K♭) := rfl

theorem teichLift_red (x : WittVector p K♭) : (teichLift K p).red x = x.coeff 0 := rfl

theorem teich_eq (a : K♭) : (teichLift K p).teich a = teichmuller p a := by
  haveI := (teichLift K p).isAdicComplete
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := (teichLift K p).I) _ fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, (teichLift K p).I_pow]
  have h := (teichLift K p).teich_sub_pow_mem a n
    (teichmuller p ((((frobeniusEquiv K♭ p).symm : K♭ →+* K♭))^[n] a))
    (by rw [teichLift_red, teichmuller_coeff_zero])
  rw [← map_pow, TeichLift.iterate_frobeniusEquiv_symm_pow] at h
  exact (teichLift K p).span_pow_anti (Nat.le_succ n) h

def tcoeff (x : AInf K p) (n : ℕ) : 𝒪♭ := ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (x.coeff n)

theorem tcoeff_zero (x : AInf K p) : tcoeff x 0 = x.coeff 0 := by
  simp [tcoeff]

theorem coeff_incl (x : AInf K p) (n : ℕ) :
    (teichLift K p).coeff (incl K p x) n = algebraMap 𝒪♭ K♭ (tcoeff x n) := by
  refine (teichLift K p).coeff_eq_of_mem (a := fun i => algebraMap 𝒪♭ K♭ (tcoeff x i)) ?_ n le_rfl
  have hx := (WittVector.eq_teichmullerSeries_iff (tcoeff x) x).1
    (WittVector.teichmullerSeries_coeff_eq x).symm n
  have h2 := map_dvd (incl K p) hx
  rw [map_pow, map_natCast, map_sub, map_sum] at h2
  rw [Ideal.mem_span_singleton, teichLift_π]
  convert h2 using 2
  rw [TeichLift.finSum, show Finset.range (n + 1) = Finset.Iic n by ext; simp [Nat.lt_succ_iff]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_natCast, incl_teichmuller, teich_eq, teichLift_π, mul_comm]

theorem incl_mem_int (x : AInf K p) : incl K p x ∈ (teichLift K p).int := ⟨x, rfl⟩

theorem norm_coeff_incl_le_one (x : AInf K p) (n : ℕ) : ‖(teichLift K p).coeff (incl K p x) n‖ ≤ 1 :=
  (teichLift K p).mem_int_iff.1 (incl_mem_int x) n

theorem isUnit_incl_p : IsUnit (algebraMap (WittVector p K♭) (teichLift K p).B
    (incl K p (p : AInf K p))) := by
  rw [map_natCast]
  exact IsLocalization.Away.algebraMap_isUnit (teichLift K p).π

variable (K p) in

def toB : 𝔸 →+* (teichLift K p).B :=
  Localization.awayLift ((algebraMap (WittVector p K♭) (teichLift K p).B).comp (incl K p))
    (p : AInf K p) isUnit_incl_p

theorem toB_algebraMap (x : AInf K p) :
    toB K p (algebraMap (AInf K p) 𝔸 x) = algebraMap (WittVector p K♭) (teichLift K p).B (incl K p x) :=
  IsLocalization.lift_eq _ x

theorem toB_injective : Function.Injective (toB K p) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (p : AInf K p)) z
  simp only at hs
  have h1 := congrArg (toB K p) hs
  rw [map_mul, hz, zero_mul, toB_algebraMap] at h1
  have hy : y = 0 := incl_injective (TeichLift.algebraMap_injective _ (by rw [map_zero, map_zero]; exact h1.symm))
  rw [hy, map_zero] at hs
  exact (IsLocalization.map_units 𝔸 s).mul_left_eq_zero.1 hs

theorem coeffB_toB_algebraMap (x : AInf K p) :
    (teichLift K p).coeffB (toB K p (algebraMap (AInf K p) 𝔸 x)) = (teichLift K p).zcoeff (incl K p x) := by
  rw [toB_algebraMap, TeichLift.coeffB_algebraMap]

end WittTilt

end GroundTheory.PAdicHodge
