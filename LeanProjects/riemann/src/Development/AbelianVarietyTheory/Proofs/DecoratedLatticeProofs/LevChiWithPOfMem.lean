import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.LevelWithP

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levelCharacter_withLevel_of_mem {P : LevelP L.Pg L.r ℂ} {κ : GA D V} (hp : rTup β L (Lev.finE V κ) ∈ P.H) :
    Lev.levChi V β (Lev.withP L P) κ = ((P.chi ⟨_, hp⟩ : ℂˣ) : ℂ) * Lev.levChi V β (Lev.flagL L) κ := by
  unfold Lev.levChi
  rw [Lev.levFn_withP, extendOne_of_mem _ hp, Units.val_mul]

theorem hasType_withCharacter_iff (P : LevelP L.Pg L.r ℂ) (F : GA D V → ℂ) :
    Lev.HasType V β (Lev.withP L P) F ↔ Lev.HasType V β (Lev.flag1L L) F ∧
      ∀ (p : P.H) κ, Lev.IsLevelLift V β L p.1 κ → ∀ g,
        (Lev.levChi V β (Lev.flagL L) κ)⁻¹ * F (g * κ) = ((P.chi p : ℂˣ) : ℂ) * F g := by
  constructor
  · intro h
    refine ⟨fun κ hκ g => ?_, fun p κ hκ g => ?_⟩
    · have h1 : rTup β L (Lev.finE V κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
      have hp : rTup β L (Lev.finE V κ) ∈ P.H := by rw [h1]; exact P.H.one_mem
      have hw : κ ∈ Lev.levG V β (Lev.withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
      rw [h κ hw g]
      congr 1
      rw [levelCharacter_withLevel_of_mem hp]
      have e : (⟨_, hp⟩ : P.H) = 1 := Subtype.ext h1
      rw [e, map_one, Units.val_one, one_mul]
      unfold Lev.levChi
      rw [Lev.levFn_flag1]
    · have hp : rTup β L (Lev.finE V κ) ∈ P.H := by rw [hκ.2.2]; exact p.2
      have hw : κ ∈ Lev.levG V β (Lev.withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
      have hne := Lev.levChi_ne_zero (β := β) (Lev.flagL L) κ
      rw [h κ hw g, levelCharacter_withLevel_of_mem hp]
      have e : (⟨_, hp⟩ : P.H) = p := Subtype.ext hκ.2.2
      rw [e, inv_mul_eq_iff_eq_mul₀ hne]
      ring
  · rintro ⟨-, h⟩ κ hκ g
    have hp : rTup β L (Lev.finE V κ) ∈ P.H := hκ.2.2
    have hl : Lev.IsLevelLift V β L (⟨_, hp⟩ : P.H).1 κ := ⟨hκ.1, hκ.2.1, rfl⟩
    have key := h ⟨_, hp⟩ κ hl g
    have hne := Lev.levChi_ne_zero (β := β) (Lev.flagL L) κ
    rw [inv_mul_eq_iff_eq_mul₀ hne] at key
    rw [key, levelCharacter_withLevel_of_mem hp]
    ring

end GlobalTheory.ChainOnto.LevelWithP

open GlobalTheory.ChainOnto.LevelWithP in

theorem GlobalTheory.ChainOnto.LevelWithP.mem_multT_withP_iff : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ) (T : SmT M →ₗ[ℂ] (GA D V → ℂ)), T ∈ MultT θ M (levS V β (Lev.withP L P)) (Lev.levChi V β (Lev.withP L P)) ↔ T ∈ MultT θ M (levS V β (Lev.flag1L L)) (Lev.levChi V β (Lev.flag1L L)) ∧ ∀ (p : P.H) κ, Lev.IsLevelLift V β L p.1 κ → ∀ w g, (Lev.levChi V β (Lev.flagL L) κ)⁻¹ * T w (g * κ) = ((P.chi p : ℂˣ) : ℂ) * T w g := by
  intro D θ V S M β L P T
  rw [mem_multT, mem_multT, GlobalTheory.MultMem.mem_mult_iff, GlobalTheory.MultMem.mem_mult_iff]
  constructor
  · intro h
    have hT : ∀ v, Lev.HasType V β (Lev.withP L P) (PiTensorProduct.lift.symm T v) := fun v κ hκ g => h.lev v κ hκ g
    refine ⟨⟨h.aut, h.cusp, fun v κ hκ g => ((hasType_withCharacter_iff P _).1 (hT v)).1 κ hκ g, h.equiv, h.cont⟩, ?_⟩
    intro p κ hκ w g
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have key : (Lev.levChi V β (Lev.flagL L) κ)⁻¹ * T (PiTensorProduct.tprod ℂ v) (g * κ) =
          ((P.chi p : ℂˣ) : ℂ) * T (PiTensorProduct.tprod ℂ v) g := ((hasType_withCharacter_iff P _).1 (hT v)).2 p κ hκ g
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      linear_combination r * key
    | add x y hx hy =>
      simp only [map_add, Pi.add_apply]
      linear_combination hx + hy
  · rintro ⟨h, hP⟩
    refine ⟨h.aut, h.cusp, fun v κ hκ g => ?_, h.equiv, h.cont⟩
    refine (hasType_withCharacter_iff P _).2 ⟨fun κ hκ g => h.lev v κ hκ g, fun p κ' hκ' g' => ?_⟩ κ hκ g
    exact hP p κ' hκ' _ g'

end
