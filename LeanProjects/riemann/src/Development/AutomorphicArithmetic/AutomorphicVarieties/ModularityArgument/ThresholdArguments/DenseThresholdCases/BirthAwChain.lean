import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TUpQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistConjugateSelfDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcUpCyc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd GlobalTheory.CuspRep GlobalTheory.GalOfCusp Formalism.ConjugateSelfDual ReciprocityTheory.Gal
private theorem contTwist {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] {n : ℕ} {r : Γ →* GL (Fin n) k} {χ : Γ →* kˣ} (hr : Continuous r) (hχ : Continuous χ) :
    Continuous (tw r χ) := by
  have h : Continuous fun s => ((tw r χ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    simp only [tw_val]
    exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hr)
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  have e : (fun s => (((tw r χ s)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      (fun s => ((tw r χ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) ∘ fun s => s⁻¹ := by
    funext s
    simp only [Function.comp_apply, map_inv]
  rw [e]
  exact h.comp continuous_inv
theorem UpperTheory.V.Z.Win.Birth.awChain_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Win.Birth.AwChain := by
  intro hH F E M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE l _ ι r κ hr hPR hκ hirr
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) E⟩
  haveI : Fact ((2 : ℕ) = 2) := ⟨rfl⟩
  have hirrE : IsIrr (r.comp (galEmb F E Ω)) :=
    ⟨hirr.1, fun _ _ _ => Submodule.mem_top, fun W hW hI => hirr.2.2 W hW fun g v hv => hI (galEmb E M Ω g) v hv⟩
  have hW := UpperTheory.V.Z.Win.Birth.awReal F E Ω hE l ι r hr hirrE hPR
  have hcE : Continuous (r.comp (galEmb F E Ω)) := hr.comp (continuous_restrictScalarsHom F E Ω)
  obtain ⟨π, hreg, hatt, -⟩ := hPR
  have hAut : IsAutC ι (r.comp (galEmb F E Ω)) :=
    _root_.UpperTheory.V.Sd.up_quad_of_printed_results hH.toClassicalTheorems F E Ω l ι hE 2 one_le_two r hr ⟨π, hreg, hatt⟩ hirrE
  have hTw := UpperTheory.V.Z.Win.Birth.awTw E Ω l 2 le_rfl ι _ κ hκ hAut hW
  have hAutT := _root_.UpperTheory.V.Sd.twist_conjugate_selfDual hH.toClassicalTheorems E Ω l ι 2 _ κ hκ hAut
  have e2 : (tw (r.comp (galEmb F E Ω)) κ).comp (galEmb E M Ω) =
      tw ((r.comp (galEmb F E Ω)).comp (galEmb E M Ω)) (κ.comp (galEmb E M Ω)) := rfl
  have hirrT : IsIrr ((tw (r.comp (galEmb F E Ω)) κ).comp (galEmb E M Ω)) :=
    e2 ▸ (shapeFacts l _ 2 _ _).2.2.2.2.2 hirr
  exact UpperTheory.V.Z.Win.Birth.awUp (_root_.UpperTheory.V.Z.Bc.upCyc_of_alt hH.toClassicalTheorems hH.cyc) E M Ω l ι 2 le_rfl _
    (contTwist hcE hκ.1) hAutT hirrT hTw
end
