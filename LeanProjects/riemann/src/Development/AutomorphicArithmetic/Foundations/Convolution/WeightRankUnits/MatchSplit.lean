import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.StableBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTwistedConstantTermMatchesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockLevelsTwistedConstantTermSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import GroundTheory.GlobalFields.TateThesis.LocalConductor

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.matchSplit : UpperTheory.V.Z.Tf.GlobalTraceComparison.MatchSplit := by
  intro E _ _ _ w hw n a b h μ f ⟨K', hKo, hKl, hf⟩
  obtain rfl : b = n - a := by omega
  have ha : a ≤ n := by omega
  have hL : IsLevel (MonoidHom.id _) (KL n w) K' := ⟨hKo, hKl, fun k hk => hk⟩
  have hμ : IsOpen {x | μ.loc w x = 1} :=
    GroundTheory.Global.isOpen_ker_of_continuous w GroundTheory.Global.Complex.units_noSmallSubgroups (μ.loc w)
      (μ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele w))
  obtain ⟨K₁, K₂, -, h₁, h₂, -, -, -, -, -, -, hH⟩ := GlobalTheory.T.exists_block_levels_twistedConstantTerm_split_place E n a ha w hw (μ.loc w) hμ K' hL
  exact ⟨⟨K₁.prod K₂, h₁.1.prod h₂.1, Subgroup.prod_mono h₁.2.1 h₂.2.1, hH f hf⟩, GlobalTheory.T.splitPlace_twistedConstantTerm_matches E n a ha w hw (μ.loc w) K' hL f hf⟩
