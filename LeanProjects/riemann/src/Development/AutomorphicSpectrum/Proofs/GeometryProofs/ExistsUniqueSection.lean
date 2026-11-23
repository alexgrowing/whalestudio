import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.RegSection

theorem section_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    (U : X.Opens) (hU : ∀ q ∈ U, genPt ξ ⤳ q) (s t : Γ(X, U))
    (e : ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq s) =
      genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq t)) : s = t :=
  TopCat.Presheaf.section_ext X.sheaf U s t fun q hq => h.inj ⟨q, hU q hq⟩ (e q hq)

theorem existsUnique_section : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → ∀ (U : X.Opens) (hU : ∀ q ∈ U, genPt ξ ⤳ q) (a : Ω), (U : Set X).Nonempty → (∀ q (hq : q ∈ U), a ∈ regAt ξ ⟨q, hU q hq⟩) → ∃! g : Γ(X, U), ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq g) = a := by
  intro X Ω _ ξ _ h U hU a _ ha
  have loc : ∀ x : U, ∃ (W : X.Opens) (_ : W ≤ U) (hx : x.1 ∈ W) (t : Γ(X, W)),
      genMap ξ ⟨x.1, hU x.1 x.2⟩ (X.presheaf.germ W x.1 hx t) = a := by
    intro x
    obtain ⟨g, hg⟩ := ha x.1 x.2
    obtain ⟨W, hx, t, rfl⟩ := X.presheaf.exists_germ_eq g
    refine ⟨W ⊓ U, inf_le_right, ⟨hx, x.2⟩, X.presheaf.map (homOfLE inf_le_left).op t, ?_⟩
    exact (congrArg (genMap ξ ⟨x.1, hU x.1 x.2⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE inf_le_left : W ⊓ U ⟶ W) x.1 ⟨hx, x.2⟩ t)).trans hg
  choose W hWU hx t ht using loc
  have val : ∀ (x : U) (y : X) (hy : y ∈ W x),
      genMap ξ ⟨y, hU y (hWU x hy)⟩ (X.presheaf.germ (W x) y hy (t x)) = a := fun x y hy =>
    (genMap_germ_eq_genMap_germ ξ (W x) ⟨y, hU y (hWU x hy)⟩ ⟨x.1, hU x.1 x.2⟩ hy (hx x) (t x)).trans (ht x)
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.obj W t := by
    intro i j
    apply TopCat.Presheaf.section_ext X.sheaf (W i ⊓ W j)
    rintro y ⟨hi, hj⟩
    apply h.inj ⟨y, hU y (hWU i hi)⟩
    exact (congrArg (genMap ξ ⟨y, hU y (hWU i hi)⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
      (TopologicalSpace.Opens.infLELeft (W i) (W j)) y ⟨hi, hj⟩ (t i))).trans
      ((val i y hi).trans ((val j y hj).symm.trans
        (congrArg (genMap ξ ⟨y, hU y (hWU i hi)⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
          (TopologicalSpace.Opens.infLERight (W i) (W j)) y ⟨hi, hj⟩ (t j))).symm))
  have hcov : U ≤ iSup W := fun y hy =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hx ⟨y, hy⟩⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W U (fun i => homOfLE (hWU i)) hcov t compat
  have spec : ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq s) = a := by
    intro q hq
    have e := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hWU ⟨q, hq⟩)) q (hx ⟨q, hq⟩) s
    have e2 : (X.presheaf.map (homOfLE (hWU ⟨q, hq⟩)).op).hom s = t ⟨q, hq⟩ := hs ⟨q, hq⟩
    exact (congrArg (genMap ξ ⟨q, hU q hq⟩) e).symm.trans
      ((congrArg (fun z => genMap ξ ⟨q, hU q hq⟩ ((X.presheaf.germ (W ⟨q, hq⟩) q (hx ⟨q, hq⟩)).hom z)) e2).trans
        (ht ⟨q, hq⟩))
  exact ⟨s, spec, fun s' hs' => section_eq h U hU s' s fun q hq => (hs' q hq).trans (spec q hq).symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat.RegSection
