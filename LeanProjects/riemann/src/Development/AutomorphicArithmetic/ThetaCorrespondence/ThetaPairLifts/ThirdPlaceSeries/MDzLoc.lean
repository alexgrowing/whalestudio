import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.IsQgOfOver
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroLoc
open GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil in
theorem main_m_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (w : PlE D.host) (n : ℕ) (π : Irr (w.adicCompletion D.host.E) n), (∃ v ∈ GlobalTheory.PRep.fixed π.π (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin n)), v ≠ 0) → UpperTheory.One.M.IsQg (w.adicCompletion D.host.E) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w n π).inePol σ = (X - 1) ^ n := by
  intro _ _ hL D w n π ⟨v, hv, hv0⟩ hq σ hσ
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, _, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)
  have h0 : fixed π.toIrrRep.ρ (KOne (w.adicCompletion D.host.E) (Fin n)) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  have h1 := fixed_ne_bot_of_equiv (equivRep π.toIrrRep) h0
  obtain ⟨m, b, hb, hb'⟩ := haveI := UpperTheory.One.M.charZero_compl w; _root_.UpperTheory.One.M.LawsM.depth H (cls π.toIrrRep) (UpperTheory.One.M.good_of_fixed hq _ h1) h1
  have hd := H.dim (cls π.toIrrRep)
  have hI : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := GlobalTheory.TameGenPowers.wild_mem_Ine hσ
  have hW : Formalism.MainNotions.BlochKatoReduction.IsWild (D.nd.plOm.1 w)
      ((ineIncl (D.nd.plOm.2 w) ⟨σ, hI⟩ : Weil (D.nd.plOm.2 w)) : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) := by
    refine ⟨hI, fun y hy => ?_⟩
    have h2 := hσ y hy
    have h3 : (D.nd.plOm.1 w).valuation y ≠ 0 := by simpa using hy
    have e2 : σ y / y - 1 = (σ y - y) / y := by field_simp
    rw [e2, map_div₀, div_lt_one₀ (zero_lt_iff.mpr h3)] at h2
    exact h2
  show (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (cls π.toIrrRep)).inePol σ = (X - 1) ^ n
  rw [← hb] at hd ⊢
  rw [WD.lpDim_mk] at hd
  rw [WD.inePol_of_mem_Ine _ hI, WD.charPol_mk, hb' _ hW, LinearMap.charpoly_one, hd]
end GlobalTheory.DepthZeroLoc
end
end
section
namespace GlobalTheory.DepthZeroTame
end GlobalTheory.DepthZeroTame
end
section
namespace GlobalTheory.DepthZeroType
end GlobalTheory.DepthZeroType
end
end
