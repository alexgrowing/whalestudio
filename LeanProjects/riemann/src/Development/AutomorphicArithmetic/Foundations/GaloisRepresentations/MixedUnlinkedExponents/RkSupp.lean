import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamMixedOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClTwistEqSelfOfEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem chs_single {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ξ : kˣ →* ℂˣ) (hξ : IsSmoothChar ξ) : chs ({IrrGL.ofChar ξ hξ} : Multiset (IrrGL k)) = {ξ} := by
  have hex : ∃ ζ : kˣ →* ℂˣ, ∃ hζ, IrrGL.ofChar ξ hξ = IrrGL.ofChar ζ hζ := ⟨ξ, hξ, rfl⟩
  have hc : hex.choose = ξ := by
    obtain ⟨hζ, e⟩ := hex.choose_spec
    exact (IrrGL.ofChar_inj.1 e).symm
  unfold chs
  rw [← Multiset.cons_zero (IrrGL.ofChar ξ hξ), Multiset.filterMap_cons_some _ _ _ (b := ξ) (by rw [dif_pos hex, hc])]
  simp

theorem UpperTheory.Gal.GamX.rkSupp :
    UpperTheory.Gal.GamX.RkSupp := by
  unfold RkSupp
  intro K _ _ _ π ψ hπ v s hs
  obtain ⟨σ, hσ, h⟩ := id hs
  have h1 := GlobalTheory.rankOne_algNorm_locComp K π ψ hπ v σ hσ
  have h2 : IrrGL.of σ.ρ σ.smooth σ.irred = IrrGL.ofChar (ψ.loc v) (ParLaws.isSmoothChar_loc ψ v) := by
    rw [← h1]
    simp [GlobalTheory.GalOfCusp.algNorm]
  have hc : (IrrGL.of σ.ρ σ.smooth σ.irred).IsCusp := h2 ▸ IrrGL.isCusp_ofChar _ _
  have h3 : SuppAt π v {IrrGL.of σ.ρ σ.smooth σ.irred} :=
    ⟨σ, hσ, (hasSupport_self hc).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm⟩
  have h4 := (UpperTheory.V.Z.Gam.suppFacts K 1 le_rfl π v).2.1 _ _ hs h3
  rw [h4, h2, chs_single]
