import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdCharIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SphUntw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPsIrr

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Desc.W.principal_series_full_statement : _root_.UpperTheory.V.Z.Desc.W.PsFullAlt := by
  intro P L Ω _ _ _ _ _ l _ ι n w A h a ha τ ω hh ψ ph hs hω hp hinj
  have hv := fun i => ((Loc.ordCharIff P.aut.art h ι a ha (hh i) (ψ i)).2 (ω i) (hω i) (ph i)).1 (hp i)
  have key : ∀ i j, (∀ σ : Ine (F := L) A, ω i (a (ineIncl h σ)) = ω j (a (ineIncl h σ))) → i = j := fun i j e =>
    hinj (MonoidHom.ext fun σ => Units.ext (ι.injective (by rw [hv, hv, e])))
  refine (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient P _ n ω (fun i => (hω i).smooth) fun i j hij => ⟨fun e => hij (key i j fun σ => by rw [e]),
    fun e => hij (key i j fun σ => ?_)⟩).2 _ τ.ρ τ.irred hs
  have h1 := DFunLike.congr_fun (ha.absPow_comp 1) (ineIncl h σ)
  rw [Complex.ofReal_one, MonoidHom.comp_apply, GlobalTheory.WeilDeligne.unrChar_apply, deg_ineIncl] at h1
  rw [e, MonoidHom.mul_apply, h1]
  simp
end
