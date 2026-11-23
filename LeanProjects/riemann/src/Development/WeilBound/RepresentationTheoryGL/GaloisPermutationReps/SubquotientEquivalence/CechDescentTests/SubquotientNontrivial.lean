import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.CechDescentTests.A6
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOfSegRep2
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductRepresentationReorderEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharactersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing Ysupp.Exp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzT

namespace SubquotientNontrivial

theorem nonempty_equiv_of_subquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : IsSubquotient σ ρ) [Nontrivial W] (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf w
  rcases eq_bot_or_eq_top S with rfl | rfl
  · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hw
  let j : ρ.IntertwiningMap (⊤ : Subrepresentation ρ).toRepresentation :=
    ⟨LinearMap.codRestrict _ LinearMap.id (fun _ => trivial), fun _ => rfl⟩
  have hs : Function.Surjective (f.comp j) := fun w => by
    obtain ⟨u, rfl⟩ := hf w
    exact ⟨u.1, rfl⟩
  have hi : Function.Injective (f.comp j) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    rcases eq_bot_or_eq_top (f.comp j).ker with h | h
    · have : x ∈ (f.comp j).ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ (f.comp j).ker := by rw [h]; trivial
      exact absurd this hw
  exact ⟨.mk (LinearEquiv.ofBijective (f.comp j).toLinearMap ⟨hi, hs⟩) (f.comp j).isIntertwining'⟩

theorem nontrivial_of_subquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : IsSubquotient σ ρ) [Nontrivial W] : Nontrivial V := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf w
  refine ⟨⟨v.1, 0, fun h0 => hw ?_⟩⟩
  rw [show v = 0 from Subtype.ext h0, map_zero]

theorem main (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) :
    (prinSeries fun _ : Fin m => unrChar k 1).IsIrreducible ∧
    ∃ hd : ∑ j : Fin m, ((fun _ : Fin m => zc k 1) j).1 = m,
      Nonempty ((prinSeries fun _ : Fin m => unrChar k 1).Equiv (prodIrr (fun _ : Fin m => zc k 1) hd)) := by
  have hχ : IsSmoothChar (unrChar k 1) := isSmoothChar_of_isUnram (isUnram_unrChar k 1)
  have hd : ∑ j : Fin m, ((fun _ : Fin m => zc k 1) j).1 = m := by simp [zc, IrrGL.ofChar]
  have hP : (prodIrr (fun _ : Fin m => zc k 1) hd).IsIrreducible :=
    GlobalTheory.RgGu.Unl.lUnlinkedIrr_nu k (GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
      PositivityTheory.RgGu.segmentRepresentation) PositivityTheory.Geo.geometricLemmaFiltration (GlobalTheory.RgGu.Nup2.nuPair k) m m
      (fun _ => Segment.single _ (IrrGL.isCusp_ofChar _ hχ)) _ hd (fun _ _ => Segment.not_linked_self _)
      (fun _ => (single_spec (IrrGL.isCusp_ofChar _ hχ)).2.1)
  have hPs : IsSubquotient (prodIrr (fun _ : Fin m => zc k 1) hd) (prinSeries fun _ : Fin m => unrChar k 1) :=
    GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries _ hd _ (fun _ => hχ) (fun _ => rfl)
  have hQs := GlobalTheory.T.principal_series_subquotient_of_characters k m (fun _ : Fin m => unrChar k 1)
  let φ := multiProdEquiv (Equiv.sigmaUnique (Fin m) fun _ => Fin 1)
    (fun _ : Fin m => GlobalTheory.LocGL.equivRep (IrrRep.det (Fin 1) (unrChar k 1) hχ))
  obtain ⟨θ⟩ := GlobalTheory.T.product_representation_reorder_equiv k m m (fun _ => 1) (Equiv.sigmaUnique (Fin m) fun _ => Fin 1)
    (stdBlocks (fun _ : Fin m => 1) hd) _ (fun _ : Fin m => (zc k 1).rep)
  have hQ := (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv φ).2
    ((GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv θ).2 hP)
  have := GlobalTheory.SmGL.nontrivial_of_irreducible hP
  have := nontrivial_of_subquotient hPs
  obtain ⟨ψ⟩ := nonempty_equiv_of_subquotient hQs hQ
  have hI : (prinSeries fun _ : Fin m => unrChar k 1).IsIrreducible :=
    (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv ψ).1 hQ
  exact ⟨hI, hd, hPs.nonempty_equiv hP hI⟩

end SubquotientNontrivial

end PositivityTheory.Rg.DzT

end
