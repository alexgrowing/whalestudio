import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem isLift_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    IsLevelLift V β L (g * g') (κ * κ') := by
  refine ⟨(GfC V).mul_mem hκ.1 hκ'.1, ?_, ?_⟩
  · rw [map_mul]; exact Subgroup.mul_mem _ hκ.2.1 hκ'.2.1
  · rw [map_mul, Formalism.L2.DIV.rTup_mul hκ.2.1 hκ'.2.1, hκ.2.2, hκ'.2.2]

theorem levChi_flag_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    levChi V β (flagL L) (κ * κ') = levChi V β (flagL L) κ * levChi V β (flagL L) κ' := by
  unfold levChi
  rw [map_mul, levFn_flag_mul hκ.2.1 hκ'.2.1, Units.val_mul]

theorem levChi_flag1 (κ : GA D V) : levChi V β (flag1L L) κ = levChi V β (flagL L) κ := by
  unfold levChi
  rw [levFn_flag1]

theorem isLift_one_of_mem {κ : GA D V} (hκ : κ ∈ levG V β (flag1L L)) : IsLevelLift V β L 1 κ := by
  refine ⟨hκ.1, hκ.2.1, ?_⟩
  have h : Formalism.L2.DIV.rTup β L (finE V κ) ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 L.Pg L.r)) := hκ.2.2
  exact Subgroup.mem_bot.mp h

theorem act_one {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) : actG0 V β L 1 F = F := by
  have h1 : (1 : GA D V) ∈ levG V β (flag1L L) := Subgroup.one_mem _
  have hl := isLift_one_of_mem h1
  funext h
  rw [level_action_spec hF ⟨1, hl⟩ 1 hl h, hF 1 h1 h, levChi_flag1]
  have := levChi_ne_zero (V := V) (β := β) (flagL L) 1
  field_simp

theorem act_hasType {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {g : G0 L.Pg L.r}
    (hex : ∃ κ, IsLevelLift V β L g κ) : HasType V β (flag1L L) (actG0 V β L g F) := by
  intro k hk h
  obtain ⟨κ, hκ⟩ := hex
  have hl := isLift_one_of_mem hk
  have hkκ : IsLevelLift V β L g (k * κ) := by simpa using isLift_mul hl hκ
  rw [level_action_spec hF ⟨κ, hκ⟩ κ hκ (h * k), level_action_spec hF ⟨κ, hκ⟩ (k * κ) hkκ h, levChi_flag_mul hl hκ,
    levChi_flag1, mul_assoc h k κ]
  have := levChi_ne_zero (V := V) (β := β) (flagL L) k
  have := levChi_ne_zero (V := V) (β := β) (flagL L) κ
  field_simp

theorem act_mul {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {g g' : G0 L.Pg L.r}
    (hex : ∃ κ, IsLevelLift V β L g κ) (hex' : ∃ κ, IsLevelLift V β L g' κ) :
    actG0 V β L (g * g') F = actG0 V β L g (actG0 V β L g' F) := by
  obtain ⟨κ, hκ⟩ := hex
  obtain ⟨κ', hκ'⟩ := hex'
  have hm := isLift_mul hκ hκ'
  funext h
  rw [level_action_spec hF ⟨_, hm⟩ _ hm h, level_action_spec (act_hasType hF ⟨κ', hκ'⟩) ⟨κ, hκ⟩ κ hκ h,
    level_action_spec hF ⟨κ', hκ'⟩ κ' hκ' (h * κ), levChi_flag_mul hκ hκ', mul_assoc h κ κ', mul_inv, mul_assoc]

theorem levelGroupAction_isAction : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), LiftsExist V β L → ∀ F : GA D V → ℂ, HasType V β (flag1L L) F → (actG0 V β L 1 F = F ∧ ∀ g, HasType V β (flag1L L) (actG0 V β L g F)) ∧ ∀ g g', actG0 V β L (g * g') F = actG0 V β L g (actG0 V β L g' F) := by
  intro D V β L hL F hF
  exact ⟨⟨act_one hF, fun g => act_hasType hF (hL g)⟩, fun g g' => act_mul hF (hL g) (hL g')⟩

end GlobalTheory.FlagAction
