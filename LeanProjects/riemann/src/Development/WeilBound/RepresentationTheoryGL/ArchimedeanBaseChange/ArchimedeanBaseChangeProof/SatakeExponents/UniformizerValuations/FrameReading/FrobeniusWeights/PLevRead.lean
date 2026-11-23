import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FRGood
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.IwahoriPairLeMaximal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlotEmbeddingsExistStatement

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem levReadOf_holds : LevReadOf := by
  intro hLI E _ _ _ n S d a ha hS hd hPS
  refine ⟨⟨fun w => ⟨(Rd.LevOC.locLev_oc d hd a ha w).1, (Rd.LevOC.locLev_oc d hd a ha w).2.2⟩, ?_⟩,
    ⟨fun w => ⟨(Rd.LevOC.locLev₂_oc d hd a ha w).1, (Rd.LevOC.locLev₂_oc d hd a ha w).2.2⟩, ?_⟩, ?_⟩
  · filter_upwards [Rd.levCof d a] with w hw using hw.1
  · filter_upwards [Rd.levCof d a] with w hw using hw.2
  intro W₁ W₂ G hT
  obtain ⟨⟨h1o, -⟩, ⟨h2o, -⟩, hset, -⟩ := hLI E n S d a ha hS hd hPS
  have hTU : ∀ u ∈ (lev₁ S d a).prod (lev₂ S d a), ∀ x, G (x * finH u) = G x := fun u hu x =>
    hT.1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x
  obtain ⟨e, -, hcp, hcp', he₁, he₂⟩ := GlobalTheory.T.position_embeddings_exist (E := E) a (n - a) hS
  have hlev : ∀ (i : Slot S) m, m ∈ Rd.LevOC.C d a i → e i m ∈ (lev₁ S d a).prod (lev₂ S d a) := by
    intro i m hm
    have h : e i m ∈ Rd.LevOC.gSet S d a := by
      rw [Rd.LevOC.gSet_eq]
      intro j
      by_cases hij : i = j
      · subst hij
        rw [hcp]
        exact hm
      · rw [hcp' i j m hij]
        rcases j with w | w
        · exact (d.lev a w.1).one_mem
        · exact (d.lev₂ a w.1).one_mem
    have h' : e i m ∈ (((lev₁ S d a).prod (lev₂ S d a) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) := by
      rw [hset]
      exact h
    exact h'
  refine ⟨⟨_, by rw [Subgroup.coe_prod]; exact h1o.prod h2o, hTU⟩, fun w hw => ⟨?_, fun hs => ?_⟩⟩
  · rintro ⟨m, hm⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    funext x
    have h := hTU _ (hlev (.inl ⟨w, hw⟩) m hm) x
    rw [he₁] at h
    exact h
  · rintro ⟨m, hm⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    funext x
    have h := hTU _ (hlev (.inr ⟨w, hw, hs⟩) m hm) x
    rw [he₂] at h
    exact h

end PositivityTheory.Rg.BcB.F.FG

end
