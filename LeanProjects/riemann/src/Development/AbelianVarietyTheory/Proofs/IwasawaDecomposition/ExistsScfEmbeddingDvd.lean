import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrier
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Pad.Pull

open Cardinal

theorem exists_scf_embedding_dvd :
    ∀ (p : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], p.Prime → (p : V) ∈ IsLocalRing.maximalIdeal V → Cardinal.mk V ≤ Cardinal.continuum → ∃ (C : SCF p) (φ : V →+* ↥(intO ↥C.S)), Function.Injective φ ∧ ∀ a b : V, ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ ≤ ‖((φ b : ↥(intO ↥C.S)) : ↥C.S)‖ → b ∣ a := by
  intro p V _ _ _ _ hp hpm hV
  let K := FractionRing V
  have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing V K hp0 hpm
      (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
  have hK : #K ≤ 𝔠 :=
    (IsLocalization.cardinalMk_le (nonZeroDivisors V)).trans hV
  have hx : 1 < ‖algebraMap K C (algebraMap V K p)⁻¹‖ := by
    rw [map_inv₀, norm_inv, hCp, inv_inv]; exact h1
  obtain ⟨L, hKL, hcl, hac, hL⟩ := GlobalTheory.SmallClosedField.exists_small_closed_subfield hK hx
  letI : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL _⟩, hx⟩ }
  haveI : CompleteSpace L := hcl.completeSpace_coe
  haveI : CharZero K := charZero_of_injective_ringHom (IsFractionRing.injective V K)
  let i : K →+* L := (algebraMap K C).codRestrict L hKL
  have hi : ∀ y, ‖i y‖ = ‖algebraMap K C y‖ := fun _ => rfl
  haveI : CharZero L := charZero_of_injective_ringHom i.injective
  have hLp : ‖(p : L)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast i, hi, ← map_natCast (algebraMap V K), hCp]
  obtain ⟨D, e, he⟩ := GlobalTheory.SmallClosedField.exists_scf_isometry hLp hL
  let g : V →+* D.S := (e.comp i).comp (algebraMap V K)
  have hg : ∀ a : V, ‖g a‖ = ‖algebraMap K C (algebraMap V K a)‖ := fun a => by
    simp only [g, RingHom.comp_apply, he, hi]
  have hle : ∀ a : V, g a ∈ intO D.S := fun a => by
    change ‖g a‖ ≤ 1
    rw [hg]; exact (hC _).2 ⟨a, rfl⟩
  refine ⟨D, g.codRestrict _ hle, fun a b hab => ?_, fun a b hab => ?_⟩
  · have h := congrArg Subtype.val hab
    exact IsFractionRing.injective V K (i.injective (e.injective h))
  · change ‖g a‖ ≤ ‖g b‖ at hab
    rw [hg, hg] at hab
    by_cases hb : b = 0
    · subst hb
      have : algebraMap K C (algebraMap V K a) = 0 := by
        rw [map_zero, map_zero, norm_zero] at hab
        exact norm_le_zero_iff.1 hab
      rw [(map_eq_zero_iff _ (algebraMap K C).injective).1 this |>
        (map_eq_zero_iff _ (IsFractionRing.injective V K)).1]
    · have hb' : algebraMap V K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hb
      have hbC : 0 < ‖algebraMap K C (algebraMap V K b)‖ :=
        norm_pos_iff.2 ((map_ne_zero_iff _ (algebraMap K C).injective).2 hb')
      obtain ⟨c, hc⟩ := (hC (algebraMap V K a / algebraMap V K b)).1 (by
        rw [map_div₀, norm_div]; exact div_le_one_of_le₀ hab hbC.le)
      refine ⟨c, IsFractionRing.injective V K ?_⟩
      rw [map_mul, hc, mul_div_cancel₀ _ hb']

end GlobalTheory.ShFam.Pad.Pull
