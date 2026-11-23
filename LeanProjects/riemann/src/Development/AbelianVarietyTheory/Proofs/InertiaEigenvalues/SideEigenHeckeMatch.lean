import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMonoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContainsAfterLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteChosenSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleResidualPointDescendsCoefficientExtenStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefRingTakenOfLocalisationCoefficientExteStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty.TakenLarge

set_option maxHeartbeats 4000000 in

theorem evO_takenAll : GlobalTheory.TwSys.Cheb → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → BuiltEx A M C tp.tup → EvO A M C tp.tup (fun D' => SumRepresentations.Conclusion41 D' ∧ GlobalTheory.SplitCoef.OSplit D' ∧ ∀ i, ZDecomp D'.nd i) → EvO A M C tp.tup TakenAll := by
  intro hCh hHS D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hE hsplit hCS2 hB hQ
  classical
  obtain ⟨bigA, hA⟩ := hQ
  obtain ⟨L₀, hL₀⟩ := hB bigA
  have hQ₀ := hA L₀ hL₀
  obtain ⟨big₁, h₁⟩ :=
    GlobalTheory.T.side_eigen_integrality hHS D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hE hsplit hCS2 bigA L₀ hL₀
  have hc₀ := GlobalTheory.T.contains_after_localization D cf jE A M C tp.tup bigA L₀ hL₀
  let S0 : L₀.X.nd.Loc → Finset ℂ := fun i =>
    if h : ∃ S : Finset ℂ, Chosen (withLoc L₀).nd (withLoc L₀).naut i ↑S then h.choose else ∅
  let big : D.what₂.places.Pl → Finset ℂ := fun w =>
    big₁ w ∪ (Finset.range (D.R.m + 1)).biUnion (fun j => (L₀.X.nd.locs j w).biUnion S0)
  refine ⟨big, fun L₁ hL₁ => ?_⟩
  have hL₁' : Built A M C tp.tup big₁ L₁ :=
    (GlobalTheory.T.eventually_conjunction_mono D cf jE A M C tp.tup (fun _ => True) (fun _ => True)).2.2.2 big₁ big L₁
      (fun w => Finset.subset_union_left) hL₁
  have hc₁ := GlobalTheory.T.contains_after_localization D cf jE A M C tp.tup big L₁ hL₁
  intro i₁ hlive₁
  obtain ⟨i₀, hw, ⟨e⟩⟩ := h₁ L₁ hL₁' i₁
  have hc₀i := hc₀ i₀
  have hc₁i := hc₁ i₁
  have hgood₀ : ∃ r, GoodR L₀.lay.fixZ.nd i₀ r := hc₀i.2.2.2.2.2.1.1 (hQ₀.1 i₀).1.2
  have hZ₀ : ZDecomp L₀.lay.fixZ.nd i₀ := hc₀i.2.2.2.1.1 (hQ₀.2.2 i₀)
  have hlive₀ : Live L₀.lay.fixZ.nd i₀ :=
    GlobalTheory.T.irreducibleResidualPoint_descends_coefficientExtension hCh _ _ _ _ i₀ i₁ e hgood₀ hZ₀ (hc₁i.2.2.1.1 hlive₁)
  have hex : ∃ S : Finset ℂ, Chosen (withLoc L₀).nd (withLoc L₀).naut i₀ ↑S :=
    GlobalTheory.T.exists_finite_chosen_set hCh (withLoc L₀) hQ₀.1 hQ₀.2.1 i₀ (hQ₀.2.2 i₀) (hc₀i.2.2.1.2 hlive₀)
  have hch : Chosen (withLoc L₀).nd (withLoc L₀).naut i₀ ↑(S0 i₀) := by
    simp only [S0, dif_pos hex]
    exact hex.choose_spec
  have hch' := (hc₀i.2.2.2.2.1 _).1 hch
  have hsub : S0 i₀ ⊆ big (L₁.X.nd.w i₁) := by
    intro z hz
    refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨L₀.X.nd.j i₀, ?_, Finset.mem_biUnion.2 ⟨i₀, ?_, hz⟩⟩)
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le (L₀.X.nd.j_range i₀).2)
    · exact (L₀.X.nd.locs_mem _ _ _).2 ⟨rfl, hw⟩
  have hcont : Contains L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ↑(S0 i₀) := fun z hz => hc₁i.2.1 z (hsub hz)
  exact (hc₁i.2.2.2.2.2.2).2 (GlobalTheory.T.exists_coefRingTaken_of_localisationCoefficientExtension _ _ _ _ i₀ i₁ e _ hch' hcont)

end GlobalTheory.CoefDuty.TakenLarge

end
