import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsJunkLiftNotVanishing
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsAddHaarMeasureIsAddFundamentalDomainPrei

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilSwap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.WeilTieCheck

variable {D : D7}

def trEquiv (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D} (hne : V.rank ≠ W.rank) : ThS ψ V W ≃ₗ[ℂ] ThS ψ W V where
  toFun Φ := ⟨fun y => Φ.1 y.transpose, mem_ThS.2 (isThetaFun_transpose ψ V W hne _ (mem_ThS.1 Φ.2))⟩
  invFun Φ := ⟨fun x => Φ.1 x.transpose, mem_ThS.2 (isThetaFun_transpose ψ W V hne.symm _ (mem_ThS.1 Φ.2))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem heis_transpose (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D} (hne : V.rank ≠ W.rank) (u : WA V W)
    (f : WA W V → ℂ) :
    (fun x : WA V W => Heisenberg₂ ψ W V u.transpose f x.transpose) = Heisenberg₂ ψ V W u (fun x => f x.transpose) := by
  funext x
  simp only [Heisenberg₂, symplH_transpose V W hne, Matrix.transpose_add]

def swapRep {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (hne : V.rank ≠ W.rank)
    (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)) : GA D W × GA D V →* Module.End ℂ (ThS ψ W V) :=
  ((trEquiv ψ hne).conjRingEquiv.toMonoidHom.comp om).comp (MulEquiv.prodComm (M := GA D W) (N := GA D V)).toMonoidHom

theorem swapRep_apply {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (hne : V.rank ≠ W.rank)
    (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)) (h : GA D W) (g : GA D V) (Φ : ThS ψ W V) :
    swapRep hne om (h, g) Φ = trEquiv ψ hne (om (g, h) ((trEquiv ψ hne).symm Φ)) := rfl

theorem exists_isWeilOn_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), V.rank ≠ W.rank → IsWeilOn ψ V W χ χ' om → ∃ om' : GA D W × GA D V →* Module.End ℂ (ThS ψ W V), IsWeilOn ψ W V χ' χ om' ∧ ∀ (g : GA D V) (h : GA D W) (Φ : ThS ψ V W) (Φ' : ThS ψ W V), (∀ x : WA V W, Φ'.1 x.transpose = Φ.1 x) → ∀ x : WA V W, (om' (h, g) Φ').1 x.transpose = (om (g, h) Φ).1 x := by
  intro D ψ _ V W χ χ' om hne H
  refine ⟨swapRep hne om, ⟨fun h g w₀ Φ Φ' e => ?_, fun γ hγ γ' hγ' Φ => ?_, fun Φ w => ?_,
    fun μ 𝓕 hμ h𝓕 p Φ => ?_, fun e he h g hh hg y x hy hx => ?_⟩, fun g h Φ Φ' e x => ?_⟩
  · have k := H.Heisenberg₂ g h w₀.transpose ((trEquiv ψ hne).symm Φ) ((trEquiv ψ hne).symm Φ') (by
      show (fun x : WA V W => Φ'.1 x.transpose) = _
      rw [e]
      exact heis_transpose ψ hne w₀.transpose Φ.1)
    rw [swapRep_apply, swapRep_apply]
    show (fun y : WA W V => (om (g, h) _).1 y.transpose) = _
    rw [k, actHom_swap W V hne.symm]
    exact heis_transpose ψ hne.symm _ _
  · exact H.aut γ' hγ' γ hγ ((trEquiv ψ hne).symm Φ)
  · exact (H.cont ((trEquiv ψ hne).symm Φ) w.transpose).comp continuous_swap
  · haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
    haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
    haveI : IsTopologicalAddGroup (WA W V) := Pi.topologicalAddGroup
    haveI : BorelSpace (WA V W) := ⟨rfl⟩
    haveI : BorelSpace (WA W V) := ⟨rfl⟩
    obtain ⟨ν, h1, h2, h3⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage (WA V W) (WA W V)
      (Matrix.transposeAddEquiv _ _ _) continuous_id.matrix_transpose continuous_id.matrix_transpose
      (ratL V W) (ratL W V) (fun x => ⟨fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩,
        fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩⟩) μ 𝓕 hμ h𝓕
    rw [← h3 fun w => ‖(swapRep hne om p Φ).1 w‖ ^ 2, ← h3 fun w => ‖Φ.1 w‖ ^ 2]
    exact H.unit ν _ h1 h2 (p.2, p.1) ((trEquiv ψ hne).symm Φ)
  · obtain ⟨r, hr, k⟩ := H.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ Φ => ?_⟩
    rw [splitFac_swap V W hne]
    exact k (ℓ.comp (trEquiv ψ hne).toLinearMap) (fun u hu Ψ Ψ' e' =>
      hℓ u.transpose (fun i j => hu j i) (trEquiv ψ hne Ψ) (trEquiv ψ hne Ψ') (by
        show (fun y : WA W V => Ψ'.1 y.transpose) = _
        rw [e']
        exact heis_transpose ψ hne.symm u.transpose Ψ.1)) ((trEquiv ψ hne).symm Φ)
  · have : (trEquiv ψ hne).symm Φ' = Φ := Subtype.ext (funext e)
    rw [swapRep_apply, this]
    rfl

end GlobalTheory.Mem.WeilSwap

end
