import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameGaloisExtensionStateStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedStateLiftListingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

theorem mvB_of_classicalTheorems : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, MvB hL := by
  intro hP hS hL
  refine StepW.trans (StepW.and (GlobalTheory.T.same_galois_extension_state hP hS hL) (GlobalTheory.T.carried_state_lift_listing hP hS hL)) (StepW.of_all fun K B' f' T' w' _ _ h => ?_)
  obtain ⟨h, h'⟩ := h
  intro B f T w hE hf hSt hpx hsel hJ hδ P x l P' hExt x' l' hG
  obtain ⟨x₁, ⟨l₁⟩, hC₁, hL₁⟩ := h B f T w hE hf hSt hpx hsel hJ hδ P x l P' hExt x' l' hG
  obtain ⟨x₂, hl₂, hC₂, hL₂⟩ := h' P' x₁ (Dof x) l₁ hC₁
  exact ⟨x₂, hl₂, hC₂, fun c hc => hL₂ c (hL₁ c hc)⟩

end GlobalTheory.HeightCounting.Up
