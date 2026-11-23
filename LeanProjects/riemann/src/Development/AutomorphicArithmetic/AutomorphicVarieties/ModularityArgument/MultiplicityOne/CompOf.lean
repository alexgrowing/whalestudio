import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.NoData
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.ArchBaseChangeOfHyp
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSatakeOfIsSatVecGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSubquotientIff

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.G UpperTheory.V.Z.Tf.GOne UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Mult

theorem compOf (hBC : Desc.BCOut) (hW : GalWeak 4) : CompOf := by
  intro E _ _ _ hunr n hn hn4 π hreg hd σ hσ _ hae w hw τ hτ
  obtain ⟨D₀, hone, -⟩ := onePre E n hn π hreg (csdDisc E n hn π hd)
  obtain ⟨hs₀, hex, hsub₀⟩ := GlobalTheory.CompanionTheory.OnePart.oneRead E n hn π _ hone
  obtain ⟨D, h1, h2, h3⟩ := hBC E hunr n hn σ hσ
  have hD₀ : {w | IsSplitAt w ∧ ¬ D₀.SplitAt σ w}.Finite := by
    refine Set.Finite.subset (Filter.eventually_cofinite.1 hae) fun w hw hx => hw.2 ?_
    obtain ⟨τ, B, a, c', d⟩ := hx hw.1
    obtain ⟨τ', hτ'⟩ := hex w
    exact ⟨τ, (hsub₀ w τ' hτ' τ).2 (GlobalTheory.CompanionTheory.SatComp.satComp E n π w τ τ' B c'.1 c' d hτ'), a⟩
  have hD : One D π := onlyPre hW hunr hn hn4 π hreg hd D h1 h2
    ((Rig.splitSatPre E n σ hσ D D₀ (Set.Finite.subset Set.finite_empty fun w hw => hw.2 (h3 w hw.1)) hD₀).mono
      fun w hw hs => (hw hs).imp fun B hB => ⟨hB.1, (hs₀ w B).2 hB.2⟩)
  obtain ⟨P, a, b⟩ := h3 w hw
  exact Desc.Comp.congr b (((GlobalTheory.CompanionTheory.OnePart.oneRead E n hn π _ hD).2.2 w τ hτ P).1 a)

end UpperTheory.V.Z.Mult
