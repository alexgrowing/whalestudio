import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmIndCoinvariants
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.ParIndSubquot

theorem parInd_isSubquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Levi k m) W) (ρ' : Representation ℂ (Levi k m) W'), IsSmooth ρ' → IsSubquotient ρ ρ' → IsSubquotient (parInd e ρ) (parInd e ρ') := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e W W' _ _ _ _ ρ ρ' hρ' h
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ι : S.toRepresentation.IntertwiningMap ρ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have hS : IsSmooth S.toRepresentation := (IsSubquotient.of_injective ι hι).isSmooth hρ'
  have hinj : Function.Injective (parIndMap e ι) := by
    intro φ ψ hφψ
    refine Subtype.ext (Subtype.ext (funext fun g => hι ?_))
    exact congrFun (congrArg (fun χ : IndSp e ρ' => χ.1.1) hφψ) g
  let σ₀ : Representation ℂ (parab k e) S.toSubmodule := (twist S.toRepresentation (deltaHalf k m)).comp (leviProj k e)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  have hsurj : Function.Surjective (parIndMap e f) := by
    refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL n k) (parab k e) (KO k n) hP SplitFlip.isCompact_KO
      hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k n) _ _ _ _
      (isSmooth_comp (isSmooth_twist hS (isSmoothChar_deltaHalf k)) _ hcont)
      (compMap (twistMap f _) _) Unit (fun _ => z) hf ?_).1
    intro x _
    refine Submodule.subset_span ⟨(), -x, ?_⟩
    show x = (0 : _) - -x
    simp
  exact (IsSubquotient.of_surjective (parIndMap e f) hsurj).trans (IsSubquotient.of_injective (parIndMap e ι) hinj)

end GlobalTheory.ParIndSubquot
