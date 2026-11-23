import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DepthZeroLoc

open GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil in

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (w : PlE D.host) (n : ℕ) (π : Irr (w.adicCompletion D.host.E) n), (∃ v ∈ GlobalTheory.PRep.fixed π.π (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin n)), v ≠ 0) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), (rcAt hL D w n π).inePol σ = (X - 1) ^ n := by
  intro _ _ _ hL D w n π ⟨v, hv, hv0⟩ σ hσ
  obtain ⟨a, ha, ε, _, H⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)
  have h0 : fixed π.toIrrRep.ρ (KOne (w.adicCompletion D.host.E) (Fin n)) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  have h1 := fixed_ne_bot_of_equiv (equivRep π.toIrrRep) h0
  obtain ⟨m, b, hb, hb'⟩ := (H.depth (cls π.toIrrRep)).1 h1
  have hd := H.dim (cls π.toIrrRep)
  have hI : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := GlobalTheory.TameGenPowers.wild_mem_Ine hσ
  have hW : Formalism.MainNotions.BlochKatoReduction.IsWild (D.nd.plOm.1 w)
      ((ineIncl (D.nd.plOm.2 w) ⟨σ, hI⟩ : Weil (D.nd.plOm.2 w)) : G D.host.E D.nd.Om) := by
    refine ⟨hI, fun y hy => ?_⟩
    have h2 := hσ y hy
    have h3 : (D.nd.plOm.1 w).valuation y ≠ 0 := by simpa using hy
    have e2 : σ y / y - 1 = (σ y - y) / y := by field_simp
    rw [e2, map_div₀, div_lt_one₀ (zero_lt_iff.mpr h3)] at h2
    exact h2
  show (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (cls π.toIrrRep)).inePol σ = (X - 1) ^ n
  rw [← hb] at hd ⊢
  rw [WD.lpDim_mk] at hd
  rw [WD.inePol_of_mem_Ine _ hI, WD.charPol_mk, hb' _ hW, LinearMap.charpoly_one, hd]

end GlobalTheory.DepthZeroLoc

end
