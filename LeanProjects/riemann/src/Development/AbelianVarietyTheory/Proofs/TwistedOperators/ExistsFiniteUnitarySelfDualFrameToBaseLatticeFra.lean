import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SelfDualFrameConj

section SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open GlobalTheory.StdFrames GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.IdemSupport Formalism.IndefR.Datum Formalism.L2.NTheta GlobalTheory.NormSum.AdLattice Formalism.L2.Herm

variable {D : D7}

set_option maxHeartbeats 800000 in

theorem exists_gfc (V : HSp D) (γ : GL (Fin V.rank) (Ef D)) (hγ : Unimod (OA D) (gramOf V γ)) :
    ∃ k ∈ Formalism.L2.Theta.GfC V, crdLat V V.L0 = lat ((Formalism.IndefR.Lev.finE V k)⁻¹ * γ) := by
  let L : Submodule (𝓞 D.host.E) V.V :=
    (lat γ).comap ((crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E))
  have hL : crdLat V L = lat γ := Submodule.map_comap_eq_of_surjective
    (f := (crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) (crd V).surjective _
  have hm : ∀ x, x ∈ L ↔ crd V x ∈ lat γ := fun _ => Iff.rfl
  have h1 : Submodule.IsLattice D.host.E L := by
    refine ⟨Submodule.fg_of_fg_map_injective
      ((crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) (crd V).injective
      (hL ▸ (lat_isLattice γ).fg : (crdLat V L).FG), ?_⟩
    apply Submodule.map_injective_of_injective (f := (crd V).toLinearMap) (crd V).injective
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← (lat_isLattice γ).span_eq_top, ← hL]
    rfl
  have h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L := by
    ext x
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      Submodule.mem_one]
    rw [hm, mem_lat_iff_dual hγ]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := (crd V).surjective y
      have := h y hy
      rw [hT_crd D.sp.cm] at this
      exact this
    · intro h y hy
      rw [hT_crd D.sp.cm]
      exact h _ hy
  obtain ⟨k, hkG, hk⟩ := GlobalTheory.VolumeRatioTypings.exists_conj V L h1 h2
  refine ⟨k, hkG, eq_lat (fun x => ?_) (isLattice_crdLat V V.standardTuple_isLattice)⟩
  have hk' : ∀ y, y ∈ GlobalTheory.AdLat.hat D.host.F (crdLat V V.L0 : Set (Fin V.rank → D.host.E)) ↔
      finMat D.sp.cm.sig V.gram k *ᵥ y ∈ GlobalTheory.AdLat.hat D.host.F (lat γ : Set (Fin V.rank → D.host.E)) := by
    rw [← hL, GlobalTheory.LevelChoices.coe_crdLat]
    have := GlobalTheory.LevelChoices.coe_crdLat (GlobalTheory.VolRatioCompare.reLat V L h1 h2)
    rw [← this] at hk
    exact hk
  refine (hatL_of_hat _ _ _ hk' x).trans ((isFrame_lat γ _).trans ?_)
  rw [mulVec_mulVec, _root_.mul_inv_rev, inv_inv, Units.val_mul]
  rfl

end SlopeTestRemainingChoices

end GlobalTheory.SelfDualFrameConj

theorem GlobalTheory.SelfDualFrameConj.frame_conj : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∃ t ∈ GfC V, IsFrame (finE V t * β) (Formalism.L2.Herm.crdLat V V.L0) := by
  intro D V β Λ N h
  obtain ⟨k, hk, hL⟩ := GlobalTheory.SelfDualFrameConj.exists_gfc V β (GlobalTheory.StdFrames.unimod_of_isSD h)
  refine ⟨k⁻¹, inv_mem hk, ?_⟩
  rw [map_inv, hL]
  exact GlobalTheory.StdFrames.isFrame_lat _
