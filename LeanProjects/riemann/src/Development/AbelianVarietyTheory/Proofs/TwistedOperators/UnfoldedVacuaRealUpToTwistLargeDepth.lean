import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRealSSmulTwoSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaAreRealDatumLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaDifferByTwistValuesLargeDepthStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal.OneVac

theorem isBiVac_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (LA : Set (Fin A.rank → D.host.E))
    (LS : Set (Fin S.rank → D.host.E)) (LA' : Set (Fin A'.rank → D.host.E)) :
    IsBiVac ψ A S A' LA LS LA' 0 ∧ IsBiSmooth (0 : WO A S → WO S A' → ℂ) := by
  have hz : ∀ (X Y : HSp D) (u : WO X Y), heisO ψ X Y u (0 : WO X Y → ℂ) = 0 := fun X Y u => by
    simpa using GlobalTheory.SeeSaw.Scale.heisO_smul ψ X Y u 0 0
  have h : ∀ (X Y : HSp D) (Λ : AddSubgroup (WO X Y)),
      IsThetaFunO ψ X Y (0 : WO X Y → ℂ) ∧ IsLatVac (heisO ψ X Y) Λ (0 : WO X Y → ℂ) := fun X Y Λ =>
    ⟨⟨fun γ w => by simp, ⟨⊤, isOpen_univ, fun u _ _ => hz X Y u⟩, continuous_const, fun k L hL hf w => contDiff_const⟩,
      fun u _ => hz X Y _, fun e _ u _ _ => hz X Y u⟩
  exact ⟨⟨continuous_const, fun v => h A S _, fun u => h S A' _⟩, fun n L L' _ _ _ _ u v => contDiff_const⟩

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem vacAt_of (h₁ : VacReal ch) (h₂ : VacTw ch) : VacAt ch := by
  obtain ⟨hb, z, hz, htw⟩ := h₂
  refine ⟨hb, z, hz, fun P p hp => ?_⟩
  by_cases hex : ∃ (t : T) (M : Vol ch.G), M.Is t
  · obtain ⟨t₀, M₀, hM₀⟩ := hex
    obtain ⟨b₀, hb₀⟩ := hb t₀
    refine ⟨fun j => ((z t₀ j : ℂ)⁻¹) • conAt ch.W hM₀ (fockD ch.W t₀ (fun j => ch.rm.vT D.R.m j) P) (p * b₀) j,
      fun j hj hj' => ?_, fun t M hM b hbt j hj hj' => ?_⟩
    · obtain ⟨hv, hs⟩ := h₁ t₀ M₀ hM₀ b₀ hb₀ P p hp j hj hj'
      exact ⟨GlobalTheory.SeeSaw.Scale.isBiVac_smul _ hv, GlobalTheory.SeeSaw.Scale.isBiSmooth_smul _ hs⟩
    · have e := htw t t₀ M M₀ hM hM₀ b b₀ hbt hb₀ P p hp j hj hj'
      rw [smul_comm, ← e, smul_smul, inv_mul_cancel₀ (z t₀ j).ne_zero, one_smul]
  · exact ⟨0, fun j _ _ => isBiVac_zero _ _ _ _ _ _ _, fun t M hM => absurd ⟨t, M, hM⟩ hex⟩

theorem big_vacAt : Big fun ch => VacAt ch :=
  GlobalTheory.RowReal.big_mono (Q := fun ch => VacReal ch ∧ VacTw ch) (fun ch h => vacAt_of ch h.1 h.2)
    (Big.and GlobalTheory.T.unfoldedVacuaAreRealDatum_largeDepth GlobalTheory.T.unfoldedVacua_differ_by_twist_values_largeDepth)

end GlobalTheory.RowVal.OneVac

end
