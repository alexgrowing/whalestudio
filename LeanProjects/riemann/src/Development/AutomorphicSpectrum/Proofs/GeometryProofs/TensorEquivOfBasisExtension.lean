import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem exists_tensor_equiv_of_semilinear :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (V V' : Type) [AddCommGroup V]
    [Module Ω₀ V] [AddCommGroup V'] [Module Ω V'] (j : V →+ V'),
    (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω₀ Ω a • j e) →
    (∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) →
    Submodule.span Ω (Set.range j) = ⊤ →
    ∃ Φ : TensorProduct Ω₀ Ω V ≃ₗ[Ω] V', ∀ e, Φ (TensorProduct.mk Ω₀ Ω V 1 e) = j e := by
  intro Ω₀ Ω _ _ _ V V' _ _ _ _ j hsemi hind hspan
  letI : Module Ω₀ V' := Module.compHom V' (algebraMap Ω₀ Ω)
  haveI : IsScalarTower Ω₀ Ω V' := ⟨fun a b x => by
    change (a • b) • x = algebraMap Ω₀ Ω a • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let jl : V →ₗ[Ω₀] V' :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a e => hsemi a e }
  let L : TensorProduct Ω₀ Ω V →ₗ[Ω] V' := jl.liftBaseChange Ω
  have hL : ∀ e, L (TensorProduct.mk Ω₀ Ω V 1 e) = j e := by
    intro e
    change jl.liftBaseChange Ω (1 ⊗ₜ[Ω₀] e) = j e
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    exact ⟨_, hL e⟩
  let B := Module.Basis.ofVectorSpace Ω₀ V
  let C := Algebra.TensorProduct.basis Ω B
  have hC : ∀ i, L (C i) = j (B i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply]
    exact hL (B i)
  have hli : LinearIndependent Ω (fun i => j (B i)) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    let e := s.equivFin
    have h1 : LinearIndependent Ω₀ (fun k : Fin s.card => B (e.symm k).1) :=
      B.linearIndependent.comp _ (Subtype.val_injective.comp e.symm.injective)
    have h2 := (hind _ _ h1).comp e e.injective
    convert h2 using 1
    funext x
    simp
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : Finsupp.linearCombination Ω (fun i => j (B i)) (C.repr x) = 0 := by
      rw [← hx]
      conv_rhs => rw [← C.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
      simp [hC]
    have h1 : C.repr x = 0 := hli (h0.trans (map_zero _).symm)
    simpa using h1
  exact ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun e => hL e⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
