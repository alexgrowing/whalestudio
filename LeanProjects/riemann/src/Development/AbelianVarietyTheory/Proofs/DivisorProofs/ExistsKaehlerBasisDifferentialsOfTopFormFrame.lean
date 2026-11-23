import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace TopForm

namespace FrameBasis

theorem bijective_of_isFreeGen {k A : Type*} [CommRing k] [CommRing A] (α : k →+* A) {m : ℕ}
    (hA : α.IsStandardSmoothOfRelativeDimension m) (x : Fin m → A)
    (hx : IsFreeGen A (dForm α x)) :
    Function.Bijective (Fintype.linearCombination A fun i => dFun α (x i)) := by
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension m k A := hA
  cases subsingleton_or_nontrivial A with
  | inl _ =>
    haveI := Module.subsingleton A (Omega α)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  | inr _ =>
    haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth m (R := k) (S := A)
    haveI : Module.Free A (Omega α) := inferInstanceAs (Module.Free A Ω[A⁄k])
    haveI : Module.Finite A (Omega α) := inferInstanceAs (Module.Finite A Ω[A⁄k])
    have hr : Module.finrank A (Omega α) = m := Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := A) m)
    let b := Module.finBasisOfFinrankEq A (Omega α) hr
    let v : Fin m → Omega α := fun i => dFun α (x i)
    obtain ⟨a, ha⟩ := hx.2 (exteriorPower.ιMulti A m b)
    have e := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) ha
    simp only [map_smul, dForm_eq, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      Module.Basis.det_self, smul_eq_mul] at e
    have hu : IsUnit (b.det v) := IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact e)
    obtain ⟨hli, hsp⟩ := (b.is_basis_iff_det).2 hu
    let b' := Module.Basis.mk hli hsp.ge
    have : (Fintype.linearCombination A fun i => dFun α (x i)) = b'.equivFun.symm.toLinearMap := by
      ext c
      simp [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply, b', v]
    rw [this]
    exact b'.equivFun.symm.bijective

end FrameBasis

end TopForm

end GlobalTheory

namespace GlobalTheory.TopForm.FrameBasis

theorem bijective_of_isLocalization_span {k A : Type*} [CommRing k] [CommRing A] (α : k →+* A)
    {m : ℕ} (x : Fin m → A) (s : Set A) (hs : Ideal.span s = ⊤) (B : s → Type*)
    [∀ t, CommRing (B t)] [∀ t, Algebra A (B t)] [∀ t : s, IsLocalization.Away t.1 (B t)]
    (H : ∀ t : s, Function.Bijective (Fintype.linearCombination (B t)
      fun i => dFun ((algebraMap A (B t)).comp α) (algebraMap A (B t) (x i)))) :
    Function.Bijective (Fintype.linearCombination A fun i => dFun α (x i)) := by
  letI := α.toAlgebra
  letI (t : s) : Algebra k (B t) := ((algebraMap A (B t)).comp α).toAlgebra
  haveI (t : s) : IsScalarTower k A (B t) := IsScalarTower.of_algebraMap_eq' rfl
  haveI (t : s) : Algebra.FormallyEtale A (B t) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t.1)
  let g : ∀ t : s, Ω[A⁄k] →ₗ[A] Ω[B t⁄k] := fun t => KaehlerDifferential.map k k A (B t)
  haveI H₁ (t : s) : IsLocalizedModule.Away t.1 (g t) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers t.1) (B t) (g t)).2
      (KaehlerDifferential.isBaseChange_of_formallyEtale k A (B t))
  let π : ∀ t : s, (Fin m → A) →ₗ[A] (Fin m → B t) := fun t => (Algebra.linearMap A (B t)).compLeft (Fin m)
  haveI H₂ (t : s) : IsLocalizedModule.Away t.1 (π t) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers t.1) (B t) (π t)).2
      (IsBaseChange.finitePow (Fin m) (IsBaseChange.linearMap A (B t)))
  let e : ∀ t : s, (Fin m → B t) ≃ₗ[A] Ω[B t⁄k] := fun t =>
    (LinearEquiv.ofBijective _ (H t)).restrictScalars A
  haveI H₃ (t : s) : IsLocalizedModule.Away t.1 ((e t).toLinearMap ∘ₗ π t) :=
    IsLocalizedModule.of_linearEquiv _ _ _
  have hcomp (t : s) : g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i)) =
      (e t).toLinearMap ∘ₗ π t := by
    ext c
    simp [g, e, π, Fintype.linearCombination_apply, algebraMap_smul]
  haveI H₄ (t : s) : IsLocalizedModule.Away t.1
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) := by
    rw [hcomp t]; exact H₃ t
  refine bijective_of_isLocalized_span s hs (fun t => Ω[B t⁄k])
    (fun t => g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (fun t => Ω[B t⁄k]) g
    (Fintype.linearCombination A fun i => dFun α (x i)) fun t => ?_
  have : IsLocalizedModule.map (.powers t.1)
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (g t)
      (Fintype.linearCombination A fun i => dFun α (x i)) = LinearMap.id := by
    refine IsLocalizedModule.linearMap_ext (.powers t.1)
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (g t) ?_
    rw [IsLocalizedModule.map_comp]
    rfl
  rw [this]
  exact Function.bijective_id

end GlobalTheory.TopForm.FrameBasis

namespace GlobalTheory.TopForm.FrameBasis

theorem exists_basis_of_isFrame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (m : ℕ),
    SmoothOfRelativeDimension m p → ∀ (U : X.Opens) (x : Fin m → Γ(X, U)),
    GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p x) →
    ∃ b : Module.Basis (Fin m) Γ(X, U) (GlobalTheory.TopForm.Omega (algX p U)),
      ∀ i, b i = GlobalTheory.TopForm.dFun (algX p U) (x i) := by
  intro k _ X p m hp U x hx
  have hU := hx.affine
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension m) p hp
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  haveI (t : (s : Set Γ(X, U))) := hU.isLocalization_basicOpen t.1
  have hbij : Function.Bijective
      (Fintype.linearCombination Γ(X, U) fun i => dFun (algX p U) (x i)) := by
    refine bijective_of_isLocalization_span (algX p U) x (s : Set Γ(X, U)) hs
      (fun t => Γ(X, X.basicOpen t.1)) fun t => ?_
    have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
      (h t t.2 Γ(X, X.basicOpen t.1))
    have e : (algebraMap Γ(X, U) Γ(X, X.basicOpen t.1)).comp (algX p U) =
        algX p (X.basicOpen t.1) := resG_comp_algX p (X.basicOpen_le t.1)
    have h₂ : (algX p (X.basicOpen t.1)).IsStandardSmoothOfRelativeDimension m := by
      rw [← resG_comp_algX p (X.basicOpen_le t.1)]
      exact h₁
    have hfr := (hx.res (hU.basicOpen t.1) (X.basicOpen_le t.1)).gen
    rw [resForm_dOn] at hfr
    have := bijective_of_isFreeGen _ h₂ _ hfr
    rw [e]
    exact this
  let eq := LinearEquiv.ofBijective _ hbij
  refine ⟨Module.Basis.ofEquivFun eq.symm, fun i => ?_⟩
  simp [eq, Module.Basis.coe_ofEquivFun, Fintype.linearCombination_apply, Pi.single_apply]

end GlobalTheory.TopForm.FrameBasis
