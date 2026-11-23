import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ParIndExact

theorem parInd_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ξ : Representation ℂ (Levi k m) X) (η : Representation ℂ (Levi k m) Y) (i : ξ.IntertwiningMap η), Function.Injective i → Function.Injective (parIndMap e i) ∧ ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (ζ : Representation ℂ (Levi k m) Z) (q : η.IntertwiningMap ζ), (∀ y, q y = 0 → ∃ x, i x = y) → ∀ φ, parIndMap e q φ = 0 → ∃ ψ, parIndMap e i ψ = φ := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e X Y _ _ _ _ ξ η i hi
  have hval : ∀ (φ : IndSp e ξ) (g : GL n k), (parIndMap e i φ).1.1 g = i (φ.1.1 g) := fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · intro φ ψ hφψ
    refine Subtype.ext (Subtype.ext (funext fun g => hi ?_))
    rw [← hval, ← hval, hφψ]
  · intro Z _ _ ζ q hex φ hφ
    have h0 : ∀ g, q (φ.1.1 g) = 0 := fun g =>
      congrFun (congrArg (fun χ : IndSp e ζ => χ.1.1) hφ) g
    choose x hx using fun g => hex _ (h0 g)
    have hlaw : x ∈ indSpace (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e)) := by
      intro p g
      apply hi
      rw [hx]
      have h1 := parInd_law e η φ p g
      rw [h1, ← hx g]
      show _ = i ((deltaHalf k m (leviProj k e p) : ℂ) • ξ (leviProj k e p) (x g))
      rw [map_smul, i.isIntertwining]
    let x' : indSpace (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e)) := ⟨x, hlaw⟩
    have hset : {g : GL n k | ind (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e)) g x' = x'} =
        {g : GL n k | ind (parab k e) ((twist η (deltaHalf k m)).comp (leviProj k e)) g φ.1 = φ.1} := by
      ext g
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        apply Subtype.ext
        funext y
        have hy := congrFun (congrArg Subtype.val h) y
        change x (y * g) = x y at hy
        change φ.1.1 (y * g) = φ.1.1 y
        rw [← hx, ← hx, hy]
      · intro h
        apply Subtype.ext
        funext y
        have hy := congrFun (congrArg Subtype.val h) y
        change φ.1.1 (y * g) = φ.1.1 y at hy
        change x (y * g) = x y
        apply hi
        rw [hx, hx, hy]
    have hsm : x' ∈ smoothPart (ind (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e))) := by
      have ho : IsOpen {g : GL n k | ind (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e)) g x' = x'} := by
        rw [hset]; exact φ.2
      exact ho
    refine ⟨⟨x', hsm⟩, ?_⟩
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    rw [hval]
    exact hx g

end GlobalTheory.ParIndExact
