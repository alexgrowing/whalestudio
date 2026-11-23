import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing

set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb.G3

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem pow_of_alg {k : Type} [Field k] [Algebra (ZMod l) k] (c : k) (h : IsAlgebraic (ZMod l) c) :
    ∃ f : ℕ, 0 < f ∧ c ^ (l ^ f) = c := by
  have hi : IsIntegral (ZMod l) c := h.isIntegral
  haveI : FiniteDimensional (ZMod l) (IntermediateField.adjoin (ZMod l) {c}) :=
    IntermediateField.adjoin.finiteDimensional hi
  haveI : Finite (IntermediateField.adjoin (ZMod l) {c}) := Module.finite_of_finite (ZMod l)
  letI := Fintype.ofFinite (IntermediateField.adjoin (ZMod l) {c})
  haveI : CharP (IntermediateField.adjoin (ZMod l) {c}) l :=
    charP_of_injective_algebraMap (algebraMap (ZMod l) _).injective l
  obtain ⟨n, -, hn⟩ := FiniteField.card (IntermediateField.adjoin (ZMod l) {c}) l
  refine ⟨n, n.pos, ?_⟩
  have := FiniteField.pow_card
    (⟨c, IntermediateField.mem_adjoin_simple_self _ c⟩ : IntermediateField.adjoin (ZMod l) {c})
  rw [hn] at this
  exact congrArg Subtype.val this

variable (K) in

def iZ : ℤ_[l] →+* OK l K :=
  ((algebraMap ℚ_[l] K).comp PadicInt.Coe.ringHom).codRestrict (OK l K) fun a => by
    show K.val.toRingHom (algebraMap ℚ_[l] K a) ∈ normInteger (PadicAlgCl l)
    rw [mem_normInteger]
    change ‖K.val (algebraMap ℚ_[l] K a)‖ ≤ 1
    rw [K.val.commutes, PadicAlgCl.norm_extends]
    exact a.2

theorem rho_iZ (r : Res l K) (a : ℤ_[l]) : r.ρ (iZ K a) = ZMod.castHom (dvd_refl l) r.k (PadicInt.toZMod a) := by
  have h1 : a - ((PadicInt.toZMod a).val : ℤ_[l]) ∈ RingHom.ker PadicInt.toZMod := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
  obtain ⟨b, hb⟩ := h1
  have ha : a = ((PadicInt.toZMod a).val : ℤ_[l]) + b * l := by rw [hb]; ring
  have e : PadicInt.toZMod a = (((PadicInt.toZMod a).val : ℕ) : ZMod l) := (ZMod.natCast_zmod_val _).symm
  rw [e, map_natCast]
  conv_lhs => rw [ha]
  rw [map_add, map_add, map_mul, map_mul, map_natCast, map_natCast, map_natCast, map_natCast,
    CharP.cast_eq_zero r.k l, mul_zero, add_zero]

theorem alg_pow (r : Res l K) [FiniteDimensional ℚ_[l] K] (c : r.k) : ∃ f : ℕ, 0 < f ∧ c ^ (l ^ f) = c := by
  obtain ⟨x, rfl⟩ := r.surj c
  letI : Algebra (ZMod l) r.k := (ZMod.castHom (dvd_refl l) r.k).toAlgebra
  apply pow_of_alg
  have hint : IsIntegral ℚ_[l] (x.1 : K) := Algebra.IsIntegral.isIntegral _
  set q := minpoly ℚ_[l] (x.1 : K) with hqdef
  have hqm : q.Monic := minpoly.monic hint
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (q.natDegree + 1)) (fun i => ‖q.coeff i‖)
    ⟨q.natDegree, by simp⟩
  have hge : 1 ≤ ‖q.coeff j‖ := by
    have := hmax q.natDegree (by simp)
    rwa [hqm.coeff_natDegree, norm_one] at this
  have hj0 : q.coeff j ≠ 0 := by
    intro h; rw [h, norm_zero] at hge; linarith
  set u := (q.coeff j)⁻¹ with hu
  have hle : ∀ i, ‖u * q.coeff i‖ ≤ 1 := by
    intro i
    rw [norm_mul, norm_inv]
    by_cases hi : i ≤ q.natDegree
    · have := hmax i (by simp; omega)
      rw [inv_mul_le_iff₀ (by linarith), mul_one]
      exact this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := q) (n := i) (by omega), norm_zero, mul_zero]
      exact zero_le_one
  have hlift : Polynomial.C u * q ∈ Polynomial.lifts (PadicInt.Coe.ringHom (p := l)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul]
    exact ⟨⟨_, hle n⟩, rfl⟩
  obtain ⟨Q, hQ⟩ := (Polynomial.mem_lifts _).1 hlift
  have hQj : Q.coeff j = 1 := by
    have := congrArg (fun P => P.coeff j) hQ
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at this
    apply Subtype.ext
    rw [PadicInt.coe_one]
    exact this.trans (inv_mul_cancel₀ hj0)
  have hev : Polynomial.eval₂ (iZ K) x Q = 0 := by
    apply Subtype.ext
    have h2 := Polynomial.hom_eval₂ Q (iZ K) (OK l K).subtype x
    change (OK l K).subtype (Polynomial.eval₂ (iZ K) x Q) = 0
    rw [h2]
    change Polynomial.eval₂ ((algebraMap ℚ_[l] K).comp PadicInt.Coe.ringHom) (x.1 : K) Q = 0
    rw [← Polynomial.eval₂_map, hQ, ← Polynomial.aeval_def, map_mul, Polynomial.aeval_C, minpoly.aeval, mul_zero]
  refine ⟨Q.map PadicInt.toZMod, ?_, ?_⟩
  · intro h
    have := congrArg (fun P => P.coeff j) h
    simp only [Polynomial.coeff_map, hQj, map_one, Polynomial.coeff_zero] at this
    exact one_ne_zero this
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap (ZMod l) r.k).comp PadicInt.toZMod = r.ρ.comp (iZ K) :=
      RingHom.ext fun a => (rho_iZ r a).symm
    rw [hcomp, ← Polynomial.hom_eval₂, hev, map_zero]

end CrystallineSemistableComparison.Pb.G3
