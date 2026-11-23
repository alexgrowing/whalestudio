import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory

theorem injective_of_jacquet_surjective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (π : Irr k n) {s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y} (hirr : τ.IsIrreducible)
    (q : (jac e π.π).IntertwiningMap τ) (hq : Function.Surjective q) :
    ∃ φ : π.π.IntertwiningMap (parInd e τ), Function.Injective φ := by
  obtain ⟨φ, hφ⟩ := (Model.evalOne_bijective e π.smooth τ).2 q
  refine ⟨φ, (injective_iff_map_eq_zero _).2 fun v hv => ?_⟩
  have hK : φ.ker ≠ ⊤ := by
    intro hK
    haveI := Model.nontrivial_of_isIrreducible hirr
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    obtain ⟨x, rfl⟩ := hq y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply hy
    have hw : φ w = 0 := (show w ∈ φ.ker from hK ▸ trivial)
    have h1 : q (Submodule.Quotient.mk w) = (φ w).1.1 1 :=
      (congrArg (fun F => F (Submodule.Quotient.mk w)) hφ).symm
    rw [h1, hw]
    rfl
  have hv' : v ∈ φ.ker := hv
  haveI := π.irr
  rw [(eq_bot_or_eq_top φ.ker).resolve_right hK] at hv'
  exact hv'

theorem exists_embedding_parInd_of_jacquet_nontrivial : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ¬ Subsingleton (Jacquet π.π (unipRad k e)) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible ∧ IsSmooth τ ∧ IsSubquotient τ (jac e π.π) ∧ ∃ φ : π.π.IntertwiningMap (parInd e τ), Function.Injective φ := by
  intro hBZ k _ _ _ _ n π s d e hJ
  have hfl : HasFiniteLength (jac e π.π) :=
    (hBZ k).2.1 (Fin s) (Fin n) (fun a => Fin (d a)) e π.V π.π π.smooth
      (hasFiniteLength_of_isIrreducible π.irr)
  haveI : WellFoundedGT (Subrepresentation (jac e π.π)) :=
    ((hasFiniteLength_iff_wellFounded _).1 hfl).1
  have hne : (⊥ : Subrepresentation (jac e π.π)) ≠ ⊤ := by
    intro h
    apply hJ
    constructor
    intro x y
    have hx : x ∈ (⊥ : Subrepresentation (jac e π.π)) := h ▸ trivial
    have hy : y ∈ (⊥ : Subrepresentation (jac e π.π)) := h ▸ trivial
    exact (hx : x = 0).trans (hy : y = 0).symm
  obtain ⟨M, hM, -⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Subrepresentation (jac e π.π))).resolve_left hne
  let q : (jac e π.π).IntertwiningMap (subQuot ⊤ M) :=
    ⟨(Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation (jac e π.π)).toSubmodule
      LinearMap.id (fun v => trivial), fun g => rfl⟩
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨v, rfl⟩
  have hirr : (subQuot ⊤ M).IsIrreducible := isIrreducible_subQuot hM.covBy_top
  have hsq : IsSubquotient (subQuot ⊤ M) (jac e π.π) := .of_surjective q hq
  refine ⟨_, _, _, subQuot ⊤ M, hirr, hsq.isSmooth (isSmooth_jac e π.smooth), hsq, ?_⟩
  exact injective_of_jacquet_surjective π e hirr q hq

end GlobalTheory
