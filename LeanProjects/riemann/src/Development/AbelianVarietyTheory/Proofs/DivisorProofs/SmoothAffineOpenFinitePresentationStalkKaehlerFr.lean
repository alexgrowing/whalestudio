import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.SmoothStalk

theorem finitePresentation_algX {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [LocallyOfFinitePresentation p]
    (U : X.affineOpens) : (algX p U.1).FinitePresentation := by
  have h := HasRingHomProperty.appLE @LocallyOfFinitePresentation p inferInstance ⟨⊤, isAffineOpen_top _⟩ U le_top
  refine RingHom.FinitePresentation.comp h ?_
  refine RingHom.FinitePresentation.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective ?_
  have : RingHom.ker (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.injective
  rw [this]; exact Submodule.fg_bot

theorem smooth_stalk : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x : X) (hx : x ∈ U.1), letI := (algX p U.1).toAlgebra; letI := ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)).toAlgebra; Algebra.FinitePresentation k Γ(X, U.1) ∧ Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = n := by
  intro k _ X p n _ U x hx
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  refine ⟨?_, ?_⟩
  · exact finitePresentation_algX p U
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) p ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(X, U.1)), x ∈ X.basicOpen (t : Γ(X, U.1)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff U.2).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen U.2 (t : Γ(X, U.1))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(X, X.basicOpen (t : Γ(X, U.1))))
  set V := X.basicOpen (t : Γ(X, U.1))
  have hVU : V ≤ U.1 := X.basicOpen_le _
  have h₂ : (algX p V).IsStandardSmoothOfRelativeDimension n := by
    rw [← GlobalTheory.TopForm.resG_comp_algX p hVU]
    exact h₁
  have hV : IsAffineOpen V := U.2.basicOpen _
  letI iA : Algebra k Γ(X, V) := (algX p V).toAlgebra
  letI iS : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hxt).hom.toAlgebra
  letI iK : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)).toAlgebra
  have hcomp : ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)) = (X.presheaf.germ V x hxt).hom.comp (algX p V) := by
    rw [← GlobalTheory.TopForm.resG_comp_algX p hVU, ← RingHom.comp_assoc]
    congr 1
    rw [← X.presheaf.germ_res (homOfLE hVU) x hxt]
    rfl
  haveI : IsScalarTower k Γ(X, V) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' hcomp
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V) := h₂
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxt⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxt⟩
  haveI : Algebra.FormallyEtale Γ(X, V) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (hV.primeIdealOf ⟨x, hxt⟩).asIdeal.primeCompl
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, V) (X.presheaf.stalk x)
  haveI : Nontrivial Γ(X, V) := (X.presheaf.germ V x hxt).hom.domain_nontrivial
  haveI : Module.Free Γ(X, V) Ω[Γ(X, V)⁄k] := by
    obtain ⟨ι, σ, _, _, P, -⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V)›.out
    exact P.free_kaehlerDifferential
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := Γ(X, V)) n
  haveI : Module.Finite Γ(X, V) Ω[Γ(X, V)⁄k] := Module.finite_of_rank_eq_nat hr
  have hfr : Module.finrank Γ(X, V) Ω[Γ(X, V)⁄k] = n := Module.finrank_eq_of_rank_eq hr
  let b := Module.Free.chooseBasis Γ(X, V) Ω[Γ(X, V)⁄k]
  let b' := IsBaseChange.basis b hbc
  refine ⟨Module.Free.of_basis b', Module.Finite.of_basis b', ?_⟩
  rw [Module.finrank_eq_card_basis b', ← hfr, Module.finrank_eq_card_basis b]

end GlobalTheory.SmoothStalk
