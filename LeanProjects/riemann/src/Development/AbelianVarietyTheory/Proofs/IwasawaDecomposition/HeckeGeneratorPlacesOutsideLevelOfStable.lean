import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompactOpenMembership
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.GenHypOut

theorem not_mem_bad (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (hQ : QOver C)
    (w : D.what₂.places.Pl) (j : Fin D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (hv : GenAt D (D.what₂.places.resChar w) (C.Q w) v k) (hc : IsConjPl D.host v s.w) :
    s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w) j) := by
  have hov : NG.OverPl v s.v := GlobalTheory.LocLevel.overPl_of_isConjPl hc
  obtain ⟨_, hl, hS, hvQ, _, _⟩ := hv
  have hp : v ∉ placesOver D.host.E
      (if D.what₂.places.resChar w = D.host.pde then D.host.pde' else D.host.pde) :=
    fun h => hS ⟨Or.inr (Or.inr h), hl⟩
  rintro (⟨w', hov', kk, hk⟩ | hq)
  · apply hS
    refine ⟨?_, hl⟩
    have hvk := GlobalTheory.LocLevel.mem_placesOver_of_overPl' hov hov' hk
    fin_cases kk
    · exact Or.inl hvk
    · exact Or.inr (Or.inl hvk)
  · by_cases htw : D.what₂.muAt w ≠ D.what₂.mu0
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp w htw j hq
      rcases hw' with hQ' | hp'
      · exact hvQ (hQ w w' v hQ' ⟨s.v, hov', hov⟩)
      · exact hp (GlobalTheory.LocLevel.mem_placesOver_of_overPl' hov hov' hp')
    · rw [not_not] at htw
      obtain ⟨hg, w', hov', hu⟩ := hq
      apply hu
      unfold TupTied.tup
      rw [tp.xi_tw, tp.psi_un w htw]
      refine HChar.UnrAt.mul ((cf.isMu0 j).unr w' fun kk hk => hg ⟨w', hov', kk, hk⟩)
        (HChar.UnrAt.mul ?_ (((isPsi_one (D.what₂.places.resChar w)).ram w').2 (Finset.notMem_empty _)))
      have hnp : w' ∉ placesOver D.host.E
          (if D.what₂.places.resChar w = D.host.pde then D.host.pde' else D.host.pde) :=
        fun h => hp (GlobalTheory.LocLevel.mem_placesOver_of_overPl' hov hov' h)
      unfold CharFrame.delAt
      split_ifs with h
      · exact cf.isDel'.unr w' fun h' => hnp (by rw [if_pos h]; exact h')
      · exact cf.isDel.unr w' fun h' => hnp (by rw [if_neg h]; exact h')

theorem genHyp : ∀ (D : D7) (cf : CharFrame D) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C),
    MtInput D M tp.tup C.Q → QOver C → GenHyp M C.Q := by
  intro D cf M C tp hM hQ w j h1 h2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  refine ⟨gPl D ∪ qPl D (tp.tup (D.what₂.muTw w) ⟨j', by omega⟩), hM.hyp w ⟨j', by omega⟩, ?_⟩
  intro v k s hv hc
  exact not_mem_bad D cf C tp hQ w _ v k s hv hc

end GlobalTheory.GenHypOut
