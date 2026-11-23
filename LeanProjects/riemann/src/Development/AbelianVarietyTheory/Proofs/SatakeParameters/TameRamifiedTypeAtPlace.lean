import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRamifiedOfRamifiedLocalComponentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldPlaceInRamifiedSetStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceParahoricSubgroupCharacterStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsotyStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfUpperParahoricEigenStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlaceStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeTame

theorem typeTame_of_ramified : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ S : Reading P.T, IsTrue P S → ∀ i w hw, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → ¬ GlobalTheory.SplitWeil.IsUnram (S i w hw).mu → TypeTame S i w hw := by
  intro hL D P S hT i w hw hg htame hram
  refine ⟨htame, hram, fun Q => ?_⟩
  obtain ⟨h1, h2⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hcomp := hT.mu i w hw j hj
  obtain ⟨v, hov, hvq⟩ := GlobalTheory.T.exists_realSubfield_place_in_ramified_set D _ w hg (GlobalTheory.T.heckeChar_ramified_of_ramified_localComponent _ _ w _ hcomp hram)
  obtain ⟨s, ξ, hsv, hcs, hlp⟩ := P.H.level.para i j hj v hvq

  obtain ⟨f, hfI, hfT, hf0⟩ : ∃ f, f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) ∧
      f ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ ∧ f ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
    rw [P.H.av.typeV] at hy
    refine ⟨(P.M.loc i).real y, hy, ?_, ?_⟩
    · rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
    · intro h; exact hy0 ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  obtain ⟨K, θ, hKm, hθ, hKi, hθo, hχθ⟩ := GlobalTheory.T.exists_splitPlaceParahoric_subgroup_character _ _ s D.R.r _ _ ξ hlp hcs.1
  have hfK : ∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc D.R.nV κ ∈ K,
      NG.rt D.host.E D.R.nV κ f = ((θ ⟨s.loc D.R.nV κ, h⟩ : ℂˣ) : ℂ) • f := by
    intro κ hκ h
    have hJ : κ ∈ (P.M.loc i).J := (hlp.mem κ hκ).2 ((hKm _).1 h)
    rw [← hχθ κ hκ hJ h]
    exact hfT.2 ⟨κ, hJ⟩
  have hmu_eq : ∀ g (hg : NG.ParaRT s D.R.r g) (d : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ),
      (d : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r g →
      θ ⟨g, (hKm g).2 hg⟩ = ξ d := fun g hg d hd => hθ g _ d hd
  rcases GlobalTheory.T.eq_or_isConjPlace_of_over_splitPlace D s w (hsv ▸ hov) with hsw | hconj
  · subst hsw
    obtain ⟨c, T, hc, hci, -⟩ := hT.rep i s hw Q
    obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_localComponent_eigenvector_at_splitPlace_isotypic _ _ (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _ (hT.rep i s hw Q) c hc hci
      K θ hKi hθo f hfI hf0 hfK
    refine ⟨u, hu0, GlobalTheory.T.isParahoricTypeVector_of_upperParahoric_eigen _ s D.R.r D.R.t _ ξ _ c hc hci hcomp.1 hcs.1 (fun k => (hcs.2 k).trans (hcomp.2 k).symm) u ?_⟩
    intro g hg d hd
    rw [← hmu_eq g hg d hd]
    exact hu g _
  · obtain ⟨hw', hci'⟩ := GlobalTheory.T.conjugateSplitPlace_eq_conjugatePlace_and_embedding D s w hconj
    subst hw'
    obtain ⟨c, T, hc, hci, -⟩ := hT.rep i (GlobalTheory.TypeTame.conjSP s) hw Q
    obtain ⟨K', θ', hK'i, hθ'o, hK'iff, hθ'eq, hK'of⟩ := GlobalTheory.T.exists_level_character_at_conjugateSplitPlace _ _ s K θ hKi hθo
    have hfK' : ∀ κ, TrivOutside {(GlobalTheory.TypeTame.conjSP s).v} κ → ∀ h' : (GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ ∈ K',
        NG.rt D.host.E D.R.nV κ f = ((θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ, h'⟩ : ℂˣ) : ℂ) • f := by
      intro κ hκ h'
      have h := (hK'iff κ).1 h'
      rw [hθ'eq κ h h']
      exact hfK κ hκ h
    obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_localComponent_eigenvector_at_splitPlace_isotypic _ _ (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) (GlobalTheory.TypeTame.conjSP s) _
      (hT.rep i (GlobalTheory.TypeTame.conjSP s) hw Q) c hc hci K' θ' hK'i hθ'o f hfI hf0 hfK'
    have hcsd : IsCSD D.host (P.tp.tup (D.nd.mu i) j) := by
      rw [← P.chr.muC i j hj]; exact (P.chr.csd _).1 (D.naut.muC_csd i)
    refine GlobalTheory.T.exists_parahoricType_vector_at_conjugate_place _ (GlobalTheory.TypeTame.conjSP s) D.R.r D.R.t _ ξ _ c hc hci hcomp.1 htame hcs.1 ?_ u hu0 ?_
    · intro k
      have e : Units.map ((GlobalTheory.TypeTame.conjSP s).i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k =
          Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E))
            (Units.map (MonoidHomClass.toMonoidHom D.host.conj) k) := by
        ext; simp [hci']
      have e2 := hcs.2 (Units.map (MonoidHomClass.toMonoidHom D.host.conj) k)
      have e3 := hcsd.1 _ _ hconj k
      have e4 := hcomp.2 k
      rw [e, e2, e3, e4]
    · intro g h hg hh d hd
      obtain ⟨h', e⟩ := hK'of g ((hKm g).2 hg) h hh
      rw [← hmu_eq g hg d hd, ← e]
      exact hu h h'

end GlobalTheory.TypeTame
