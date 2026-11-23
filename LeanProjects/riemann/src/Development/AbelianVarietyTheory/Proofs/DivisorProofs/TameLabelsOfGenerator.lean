import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.TameLabel

variable {p : ℕ} [Fact p.Prime]

def teichU (L : GlobalTheory.GLq.LabelDatum p) : (ZMod p)ˣ →* ℂˣ :=
  (L.teich.comp (((algebraMap (ZMod p) (Fbar p)).toMonoidHom).comp (Units.coeHom (ZMod p)))).toHomUnits

theorem teichU_val (L : GlobalTheory.GLq.LabelDatum p) (a : (ZMod p)ˣ) :
    ((teichU L a : ℂˣ) : ℂ) = L.teich (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := rfl

theorem theta_gen_pow (L : GlobalTheory.GLq.LabelDatum p) {x : Fbar p} (hx : x ^ (p ^ 1 - 1) = 1) (n : ℕ) :
    GlobalTheory.GLq.thetaOf L 1 x (L.gen 1 ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen 1 ^ n = L.gen 1 ^ m := ⟨n, rfl⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dif_pos h]
  have hpos : 0 < p ^ 1 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow one_ne_zero (Fact.out : p.Prime).one_lt)
  have hfin : IsOfFinOrder (L.gen 1) := by
    rw [← orderOf_pos_iff, L.gen_order 1 one_pos]; exact hpos
  have hm : n ≡ h.choose [MOD p ^ 1 - 1] := by
    rw [← L.gen_order 1 one_pos]; exact hfin.pow_eq_pow_iff_modEq.1 h.choose_spec
  have h1 : L.teich x ^ (p ^ 1 - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [pow_eq_pow_mod h.choose h1, pow_eq_pow_mod n h1, hm]

theorem zpowers_top_iff (γ : (ZMod p)ˣ) : Subgroup.zpowers γ = ⊤ ↔ orderOf γ = p - 1 := by
  rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, Nat.card_eq_fintype_card, ZMod.card_units]

theorem exists_gen (L : GlobalTheory.GLq.LabelDatum p) : ∃ g : (ZMod p)ˣ, orderOf g = p - 1 ∧
    ∀ (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ), LabelsTame L χ a ↔ χ g = teichU L a := by
  have ho := L.gen_order 1 one_pos
  obtain ⟨g, hg⟩ := GlobalTheory.GoodCharsCompare.exists_unit_of_pow (g := p) (y := L.gen 1)
    (by rw [← ho, pow_orderOf_eq_one])
  have hog : orderOf g = p - 1 := by
    rw [← hg, pow_one] at ho
    rw [← ho, ← orderOf_units]
    exact (orderOf_injective (algebraMap (ZMod p) (Fbar p)).toMonoidHom
      (algebraMap (ZMod p) (Fbar p)).injective _).symm
  have hval : ∀ (a : (ZMod p)ˣ) (n : ℕ), GlobalTheory.GLq.thetaOf L 1 (algebraMap (ZMod p) (Fbar p) (a : ZMod p))
      (algebraMap (ZMod p) (Fbar p) ((g ^ n : (ZMod p)ˣ) : ZMod p)) = ((teichU L a : ℂˣ) : ℂ) ^ n := by
    intro a n
    rw [Units.val_pow_eq_pow_val, map_pow, teichU_val]
    have := theta_gen_pow L (GlobalTheory.GoodCharsCompare.unit_pow a) n
    rw [← hg] at this
    exact this
  refine ⟨g, hog, fun χ a => ⟨fun h => ?_, fun h u => ?_⟩⟩
  · have := hval a 1
    rw [pow_one, pow_one, h g] at this
    exact Units.ext this
  · have hu : u ∈ Subgroup.zpowers g := by rw [(zpowers_top_iff g).2 hog]; trivial
    obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers).2 hu
    rw [hval, map_pow, h, Units.val_pow_eq_pow_val]

end GlobalTheory.TameLabel

end
