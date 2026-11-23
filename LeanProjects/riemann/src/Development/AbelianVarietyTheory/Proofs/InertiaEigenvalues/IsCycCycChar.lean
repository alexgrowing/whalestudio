import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

noncomputable def cycChar (l : ℕ) [Fact l.Prime] : GQ l →* ℚ_[l]ˣ :=
  (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
    ((cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l)))

theorem _root_.GlobalTheory.Cyc.isCyc_cycChar (l : ℕ) [Fact l.Prime] :
    _root_.GlobalTheory.Cyc.IsCyc (_root_.GlobalTheory.Cyc.cycChar l) := by
  intro g m ζ h
  set x : ℤ_[l] := (cyclotomicCharacter (_root_.Formalism.BasicNotions.Loc.Om l) l (MulSemiringAction.toRingAut _ _ g) : ℤ_[l])
    with hx
  refine ⟨(PadicInt.toZModPow m x).val, ?_, ?_⟩
  · have hmem : x - ((PadicInt.toZModPow m x).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ m} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
        sub_self]
    have h2 : ‖((x - ((PadicInt.toZModPow m x).val : ℤ_[l]) : ℤ_[l]) : ℚ_[l])‖ ≤
        (l : ℝ) ^ (-(m : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 hmem
    have h3 : ((_root_.GlobalTheory.Cyc.cycChar l g : ℚ_[l]ˣ) : ℚ_[l]) = (x : ℚ_[l]) := rfl
    rw [h3]
    rw [PadicInt.coe_sub, PadicInt.coe_natCast] at h2
    exact h2
  · exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ _ g) ζ h

theorem _root_.GlobalTheory.Cyc.exists_isCyc :
    ∀ (l : ℕ) [Fact l.Prime], ∃ χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ, _root_.GlobalTheory.Cyc.IsCyc χ :=
  fun l _ => ⟨_root_.GlobalTheory.Cyc.cycChar l, _root_.GlobalTheory.Cyc.isCyc_cycChar l⟩

end GlobalTheory.Cyc
