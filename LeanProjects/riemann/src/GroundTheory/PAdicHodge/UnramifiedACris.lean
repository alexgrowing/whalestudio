import Mathlib
import GroundTheory.PAdicHodge.LocalBridge
import GroundTheory.PAdicHodge.ACrisGalois
import GroundTheory.LocalFields.Unramified
import GroundTheory.LocalFields.PrincipalUnitsRank
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open ValuativeRel IsLocalRing

namespace UnramifiedACris

variable {p : ℕ} [hp : Fact p.Prime]

variable (p) in

theorem irreducible_p : Irreducible (p : 𝒪[ℚ_[p]]) := by
  have h := (MulEquiv.irreducible_iff
    (f := (GroundTheory.LocalField.PadicRank.padicIntEquivInteger p).toMulEquiv)
    (x := (p : ℤ_[p]))).2 PadicInt.irreducible_p
  simpa using h

variable (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K₀]

omit [FiniteDimensional ℚ_[p] K₀] in

theorem mem_integer_iff (x : K₀) : x ∈ 𝒪[K₀] ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
  rw [integer_eq_normInteger, mem_normInteger]
  rfl

theorem natCast_p_mem_maximalIdeal : (p : 𝒪[K₀]) ∈ 𝓂[K₀] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : ((((p : 𝒪[K₀]) * v : 𝒪[K₀]) : K₀) : PadicAlgCl p) = 1 := by rw [hv]; rfl
  have hv1 : ‖(((v : 𝒪[K₀]) : K₀) : PadicAlgCl p)‖ ≤ 1 := (mem_integer_iff K₀ _).1 v.2
  have h2 : ‖((((p : 𝒪[K₀]) * v : 𝒪[K₀]) : K₀) : PadicAlgCl p)‖ < 1 := by
    have : ((((p : 𝒪[K₀]) * v : 𝒪[K₀]) : K₀) : PadicAlgCl p) =
        (p : PadicAlgCl p) * (((v : 𝒪[K₀]) : K₀) : PadicAlgCl p) := by
      simp
    rw [this, norm_mul]
    calc ‖(p : PadicAlgCl p)‖ * ‖(((v : 𝒪[K₀]) : K₀) : PadicAlgCl p)‖
        ≤ ‖(p : PadicAlgCl p)‖ * 1 := by gcongr
      _ < 1 := by
        rw [mul_one, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends]
        exact Padic.norm_p_lt_one
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

instance charP_residueField : CharP 𝓀[K₀] p :=
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (residue 𝒪[K₀]), residue_eq_zero_iff]
    exact natCast_p_mem_maximalIdeal K₀)

theorem exists_eq_p_mul_of_mem_maximalIdeal
    [GroundTheory.LocalField.IsUnramified ℚ_[p] K₀] {x : 𝒪[K₀]} (hx : x ∈ 𝓂[K₀]) :
    ∃ y : 𝒪[K₀], x = p * y := by
  rw [← (GroundTheory.LocalField.map_maximalIdeal_eq_iff ℚ_[p] K₀).2 inferInstance,
    (irreducible_p p).maximalIdeal_eq, Ideal.map_span, Set.image_singleton, map_natCast,
    Ideal.mem_span_singleton] at hx
  exact hx

def integerToCp : 𝒪[K₀] →+* normInteger ℂ_[p] :=
  RingHom.codRestrict ((algebraMap (PadicAlgCl p) ℂ_[p]).comp
    ((algebraMap K₀ (PadicAlgCl p)).comp (𝒪[K₀]).subtype)) (normInteger ℂ_[p]) fun x => by
    rw [mem_normInteger, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
    exact (mem_integer_iff K₀ x).1 x.2

variable [GroundTheory.LocalField.IsUnramified ℚ_[p] K₀]

def residueToModP : 𝓀[K₀] →+* ModP (normInteger ℂ_[p]) p :=
  Ideal.Quotient.lift (𝓂[K₀]) ((Ideal.Quotient.mk _).comp (integerToCp K₀)) fun x hx => by
    obtain ⟨y, rfl⟩ := exists_eq_p_mul_of_mem_maximalIdeal K₀ hx
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def residueToPreTilt : 𝓀[K₀] →+* PreTilt (normInteger ℂ_[p]) p :=
  Perfection.lift p 𝓀[K₀] (ModP (normInteger ℂ_[p]) p) (residueToModP K₀)

def wittToAInf : WittVector p 𝓀[K₀] →+* AInf ℂ_[p] p :=
  WittVector.map (residueToPreTilt K₀)

def wittToACris : WittVector p 𝓀[K₀] →+* ACris.ACris ℂ_[p] p :=
  (algebraMap (AInf ℂ_[p] p) (ACris.ACris ℂ_[p] p)).comp (wittToAInf K₀)

end UnramifiedACris

end GroundTheory.PAdicHodge
