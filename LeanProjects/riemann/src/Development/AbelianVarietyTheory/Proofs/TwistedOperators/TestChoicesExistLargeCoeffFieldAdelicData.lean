import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedDataOffBaseLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

noncomputable section

theorem GlobalTheory.RowEx.dat_choice_exists : GlobalTheory.RowEx.ExField → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLg fun K B f T => ∀ (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (L : SizeData₂ (w.st Z).toD7), L.sc = K.s → GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 → ∃ ch : GlobalTheory.RowTest.Choice z.R.toRealDat, ch.Is ∧ ch.AtScale CF L.sc.b ∧ ch.FieldOK := by
  classical
  intro hE
  obtain ⟨CF0, hE⟩ := hE
  refine ⟨CF0, fun CF hCF => ⟨1, one_pos, fun eps C8 _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ?_⟩⟩⟩⟩⟩
  obtain ⟨x₀, hx⟩ := hE eps CF hCF
  refine ⟨x₀, fun K _ _ _ hK hxK => ?_⟩
  have hF := hx K.s hK hxK
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f _ _ Ξ => if h : Ξ.Finite then Classical.choose (hF P f Ξ h) else ∅, by simp, ?_, ?_⟩
  · intro P f _ _ Ξ z hz
    by_cases h : Ξ.Finite
    · dsimp only at hz
      rw [dif_pos h] at hz
      exact (Classical.choose_spec (hF P f Ξ h)).1 z hz
    · dsimp only at hz
      rw [dif_neg h] at hz
      simp at hz
  · intro B f T _ hH _ _ w Z hX Wt z L hL hS
    obtain ⟨hq, hC, hfin, hmem⟩ := GlobalTheory.RowEx.twisted_data_off_base_level B f T w Z hX Wt z
    have hS2 := hH.2
    dsimp only at hS2
    rw [dif_pos hfin] at hS2
    rw [hL]
    exact (Classical.choose_spec (hF B.toPre f (T.set f) hfin)).2 (w.st Z) f rfl HEq.rfl L hL _ _ _ _ _ _ _ hS hC hq
      (fun t => ⟨_, hmem t, HEq.rfl⟩) (fun y hy => hS2 y hy)

end
