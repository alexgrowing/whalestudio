import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTameStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatePlaceCompletionIsoTameStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeBlockPf

theorem splitAt : ∀ (D : D7) (w : PlE D.host), IsSplitPl D.host w → ∃ s : SplitPlace D.host.E, s.w = w := by
  intro D w hw
  have hc : ∀ x : 𝓞 D.host.E, ((GlobalTheory.SumWCompare.cj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    intro x; rw [GlobalTheory.SumWCompare.cj_coe, GlobalTheory.DimPartsCompare.star_conj]
  have hcc : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z := by
    intro z; rw [← GlobalTheory.DimPartsCompare.star_conj, ← GlobalTheory.DimPartsCompare.star_conj, star_star]
  obtain ⟨x, hx, hy⟩ := hw
  have hsp : IsSplitPl D.host (GlobalTheory.DimPartsCompare.cPl w) := by
    refine ⟨GlobalTheory.SumWCompare.cj D.host.E x, ?_, fun y e hy' => ?_⟩
    · rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj]; exact hx
    · rw [GlobalTheory.DimPartsCompare.mem_cPl] at hy'
      refine hy _ ?_ hy'
      rw [hc, show y = x from RingOfIntegers.ext (by rw [e, hc, hcc])]
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ hsp
  refine ⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  have := hs (GlobalTheory.SumWCompare.cj D.host.E y) y (by rw [hc, hcc])
  rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj] at this
  exact this.symm

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ S : Reading P.T, IsTrue P S → ∀ i w hw, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → TypeBlock S i w hw := by
  intro hL D P S hT i w hw ⟨k, hk⟩ htame
  refine ⟨htame, fun Q => ?_⟩
  obtain ⟨s, rfl⟩ := splitAt D w hw
  obtain ⟨c, T, hc, hcs, -, -, -⟩ := hT.rep i s hw Q
  have hf : ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧
      ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x →
        Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t →
        NG.rt D.host.E D.R.nV x f =
          blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
    obtain ⟨v, e | e⟩ := GlobalTheory.DimPartsCompare.cover k s.w hk
    · exact GlobalTheory.T.split_place_completion_iso_tame hL D P S hT i k v s hw e htame c hc hcs Q
    · exact GlobalTheory.T.conjugate_place_completion_iso_tame hL D P S hT i k v s hw e htame c hc hcs Q
  obtain ⟨f, hfS, hf0, hfe⟩ := hf
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.T.local_irreducible_fixed_vectors D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _
    (hT.rep i s hw Q) c hc hcs (blockGrp _ D.R.r D.R.t) (blockChar (S i s.w hw).mu) (fun h hh => hh.1)
    (fun h hh => ⟨kOne_le_blockGrp _ _ hh, blockChar_kOne _ htame hh⟩) f hfS hf0 hfe
  exact ⟨y, hy0, isBlockVec_of _ _ _ hy⟩

end GlobalTheory.TypeBlockPf
