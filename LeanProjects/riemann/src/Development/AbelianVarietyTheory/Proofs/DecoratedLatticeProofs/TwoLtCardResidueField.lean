import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField Filter
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPl

theorem two_lt_card_residueField (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    2 < Nat.card (IsLocalRing.ResidueField 𝒪[Fv F v]) := by
  have h1 : v.valuation F (2 : F) = 1 := by
    have h2 : ¬ v.valuation F (algebraMap (𝓞 F) F 2) < 1 :=
      fun h3 => h ((v.valuation_lt_one_iff_mem (K := F) 2).1 h3)
    have h3 := v.valuation_le_one (K := F) 2
    have h4 := le_antisymm h3 (not_lt.1 h2)
    simpa [map_ofNat] using h4
  have h5 : (algebraMap F (Fv F v) (2 : F)⁻¹) ≤ᵥ algebraMap F (Fv F v) 1 := by
    rw [GlobalTheory.LocalData.complRel_algebraMap v, map_inv₀, h1, map_one, inv_one]
  rw [Valuation.Compatible.vle_iff_le (v := valuation (Fv F v)), map_one, map_one] at h5
  have h6 : IsUnit (2 : 𝒪[Fv F v]) := by
    refine IsUnit.of_mul_eq_one ⟨_, (Valuation.mem_integer_iff _ _).2 h5⟩ (Subtype.ext ?_)
    change (2 : Fv F v) * algebraMap F (Fv F v) (2 : F)⁻¹ = 1
    rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have h7 : (2 : IsLocalRing.ResidueField 𝒪[Fv F v]) ≠ 0 := by
    have := (h6.map (IsLocalRing.residue 𝒪[Fv F v])).ne_zero
    rwa [map_ofNat] at this
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[Fv F v])
  rw [Nat.card_eq_fintype_card]
  by_contra hc
  have h8 : Fintype.card (IsLocalRing.ResidueField 𝒪[Fv F v]) = 2 :=
    le_antisymm (not_lt.1 hc) Fintype.one_lt_card
  have h9 := FiniteField.cast_card_eq_zero (IsLocalRing.ResidueField 𝒪[Fv F v])
  rw [h8] at h9
  exact h7 (by exact_mod_cast h9)

end GlobalTheory.FinPl
