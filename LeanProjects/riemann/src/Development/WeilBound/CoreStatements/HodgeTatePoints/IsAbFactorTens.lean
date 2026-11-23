import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.RgProd
import Development.WeilBound.CoreStatements.HodgeTatePoints.RgAmple

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace PositivityTheory.HtPt.Rg

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem tens_map {X Y X' Y' : Type} (M : Submodule R (X' → C)) (M' : Submodule R (Y' → C))
    (i : X → X') (j : Y → Y') :
    (tens M M').map (LinearMap.funLeft R C (Prod.map i j)) =
      tens (M.map (LinearMap.funLeft R C i)) (M'.map (LinearMap.funLeft R C j)) := by
  unfold tens
  rw [Submodule.map_span]
  congr 1
  ext F
  simp only [Set.mem_image, Set.mem_setOf_eq, Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨g, hg, k, hk, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, _, ⟨k, hk, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, _, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, k, hk, rfl⟩, rfl⟩

theorem tens_mono {X Y : Type} {M M₁ : Submodule R (X → C)} {M' M₁' : Submodule R (Y → C)}
    (h : M ≤ M₁) (h' : M' ≤ M₁') : tens M M' ≤ tens M₁ M₁' := by
  refine Submodule.span_mono ?_
  rintro _ ⟨g, hg, k, hk, rfl⟩
  exact ⟨g, h hg, k, h' hk, rfl⟩

theorem isAbFactor_tens {p : ℕ} {N₁ N₂ : Type} [AddCommGroup N₁] [AddCommGroup N₂]
    {M₁ : Submodule R (N₁ → C)} {M₂ : Submodule R (N₂ → C)} (h₁ : IsAbFactor p M₁)
    (h₂ : IsAbFactor p M₂) : IsAbFactor p (tens M₁ M₂) := by
  obtain ⟨A, x, L, hA, hL, hAmp, T, N, inst, pt, hpt, i, π, hπ, hs, hM⟩ := h₁
  obtain ⟨A', x', L', hA', hL', hAmp', T', N', inst', pt', hpt', i', π', hπ', hs', hM'⟩ := h₂
  obtain ⟨hAA, L₂, hL₂, hAmp₂⟩ := ample_prod R A A' L L' hA hL hAmp hA' hL' hAmp'
  have key : (tens (torsFun C T pt) (torsFun C T' pt')).map
      (LinearMap.funLeft R C (Prod.map (i ∘ π) (i' ∘ π'))) ≤ tens (torsFun C T pt) (torsFun C T' pt') := by
    rw [tens_map]
    apply tens_mono
    · rintro _ ⟨g, hg, rfl⟩
      exact hs g hg
    · rintro _ ⟨g, hg, rfl⟩
      exact hs' g hg
  refine ⟨A ⊗ A', inferInstance, L₂, hAA, hL₂, hAmp₂, prodRep T T', N × N', inferInstance,
    fun z => lift (pt z.1) (pt' z.2), isTorsPts_prod hpt hpt', i.prodMap i', π.prodMap π', ?_, ?_, ?_⟩
  · intro z
    exact Prod.ext (hπ z.1) (hπ' z.2)
  · intro g hg
    rw [torsFun_prod C T T' hpt hpt'] at hg ⊢
    exact key ⟨g, hg, rfl⟩
  · rw [torsFun_prod C T T' hpt hpt', hM, hM']
    exact (tens_map _ _ i i').symm

theorem isAbFactor_map {p : ℕ} {N₁ N₂ : Type} [AddCommGroup N₁] [AddCommGroup N₂]
    {M : Submodule R (N₂ → C)} (i : N₁ →+ N₂) (π : N₂ →+ N₁) (hπ : ∀ x, π (i x) = x)
    (hs : ∀ g ∈ M, (fun x => g (i (π x))) ∈ M) (h : IsAbFactor p M) :
    IsAbFactor p (M.map (LinearMap.funLeft R C (i : N₁ → N₂))) := by
  obtain ⟨A, x, L, hA, hL, hAmp, T, N, inst, pt, hpt, i', π', hπ', hs', hM⟩ := h
  subst hM
  refine ⟨A, x, L, hA, hL, hAmp, T, N, inst, pt, hpt, i'.comp i, π.comp π', ?_, ?_, ?_⟩
  · intro y
    simp [hπ', hπ]
  · intro g hg
    have h1 : (fun y => g (i' y)) ∈ (torsFun C T pt).map (LinearMap.funLeft R C (i' : N₂ → N)) :=
      ⟨g, hg, rfl⟩
    obtain ⟨g2, hg2, e⟩ := hs _ h1
    have h3 := hs' g2 hg2
    convert h3 using 1
    funext y
    have e2 := congrFun e (π' y)
    simpa using e2.symm
  · rw [← Submodule.map_comp]
    rfl

end

theorem abfac_prod : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → (∀ (N₁ N₂ : Type) [AddCommGroup N₁] [AddCommGroup N₂] (M₁ : Submodule R (N₁ → C)) (M₂ : Submodule R (N₂ → C)), IsAbFactor p M₁ → IsAbFactor p M₂ → IsAbFactor p (tens M₁ M₂)) ∧ ∀ (N₁ N₂ : Type) [AddCommGroup N₁] [AddCommGroup N₂] (M : Submodule R (N₂ → C)) (i : N₁ →+ N₂) (π : N₂ →+ N₁), (∀ x, π (i x) = x) → (∀ g ∈ M, (fun x => g (i (π x))) ∈ M) → IsAbFactor p M → IsAbFactor p (M.map (LinearMap.funLeft R C (i : N₁ → N₂))) := by
  intro p _ C _ _ _ v R _ _ _ _
  exact ⟨fun _ _ _ _ _ _ h h' => isAbFactor_tens h h',
    fun _ _ _ _ _ i π h h' h'' => isAbFactor_map i π h h' h''⟩

end PositivityTheory.HtPt.Rg
