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

namespace GlobalTheory

theorem isSubquotient_of_exact_middle (G : Type) [Group G] (U V A Q : Type) [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup Q] [Module ℂ Q]
    (τ : Representation ℂ G U) (ρ : Representation ℂ G V) (α : Representation ℂ G A)
    (κ : Representation ℂ G Q) (i : α.IntertwiningMap ρ) (q : ρ.IntertwiningMap κ) :
    τ.IsIrreducible → (∀ v, q v = 0 → ∃ a, i a = v) → IsSubquotient τ ρ →
      IsSubquotient τ α ∨ IsSubquotient τ κ := by
  intro hτ hex ⟨T, f, hf⟩

  let W' : Subrepresentation τ :=
    ⟨(LinearMap.ker (q.toLinearMap ∘ₗ T.toSubmodule.subtype)).map f.toLinearMap, by
      rintro g _ ⟨t, ht, rfl⟩
      refine ⟨T.toRepresentation g t, ?_, (f.isIntertwining _ _ g t)⟩
      have ht' : q (t : V) = 0 := ht
      show q (ρ g (t : V)) = 0
      rw [q.isIntertwining, ht', map_zero]⟩
  rcases hτ.eq_bot_or_eq_top W' with h | h
  ·
    right
    have hvan : ∀ t : T.toSubmodule, q (t : V) = 0 → f t = 0 := by
      intro t ht
      have hm : f t ∈ W'.toSubmodule := ⟨t, ht, rfl⟩
      rw [h] at hm
      exact hm
    let S : Subrepresentation κ := ⟨T.toSubmodule.map q.toLinearMap, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨ρ g v, T.apply_mem_toSubmodule g hv, q.isIntertwining _ _ g v⟩⟩
    let q' : T.toSubmodule →ₗ[ℂ] S.toSubmodule :=
      LinearMap.codRestrict S.toSubmodule (q.toLinearMap ∘ₗ T.toSubmodule.subtype)
        (fun t => ⟨t, t.2, rfl⟩)
    have hq' : Function.Surjective q' := by
      rintro ⟨_, v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
    have hker : LinearMap.ker q' ≤ LinearMap.ker f.toLinearMap := by
      intro t ht
      have : q (t : V) = 0 := congrArg Subtype.val (ht : q' t = 0)
      exact hvan t this
    let e := q'.quotKerEquivOfSurjective hq'
    let φ : S.toSubmodule →ₗ[ℂ] U := ((LinearMap.ker q').liftQ f.toLinearMap hker) ∘ₗ e.symm.toLinearMap
    have hφ : ∀ t, φ (q' t) = f t := by
      intro t
      show (LinearMap.ker q').liftQ f.toLinearMap hker (e.symm (q' t)) = f t
      have : e.symm (q' t) = Submodule.Quotient.mk t := by
        rw [LinearEquiv.symm_apply_eq]; rfl
      rw [this]; rfl
    refine ⟨S, ⟨φ, fun g => ?_⟩, fun u => ?_⟩
    · ext s
      obtain ⟨t, rfl⟩ := hq' s
      have h1 : S.toRepresentation g (q' t) = q' (T.toRepresentation g t) :=
        Subtype.ext (q.isIntertwining _ _ g t).symm
      show φ (S.toRepresentation g (q' t)) = τ g (φ (q' t))
      rw [h1, hφ, hφ]
      exact f.isIntertwining _ _ g t
    · obtain ⟨t, rfl⟩ := hf u
      exact ⟨q' t, hφ t⟩
  ·
    left
    let R : Subrepresentation α := ⟨T.toSubmodule.comap i.toLinearMap, by
      intro g a ha
      show i (α g a) ∈ T.toSubmodule
      rw [i.isIntertwining]
      exact T.apply_mem_toSubmodule g ha⟩
    let j : R.toSubmodule →ₗ[ℂ] T.toSubmodule :=
      LinearMap.codRestrict T.toSubmodule (i.toLinearMap ∘ₗ R.toSubmodule.subtype) (fun a => a.2)
    refine ⟨R, ⟨f.toLinearMap ∘ₗ j, fun g => ?_⟩, fun u => ?_⟩
    · ext a
      show f (j (R.toRepresentation g a)) = τ g (f (j a))
      have h1 : j (R.toRepresentation g a) = T.toRepresentation g (j a) :=
        Subtype.ext (i.isIntertwining _ _ g a)
      rw [h1]
      exact f.isIntertwining _ _ g (j a)
    · have hu : u ∈ W'.toSubmodule := by rw [h]; trivial
      obtain ⟨t, ht, rfl⟩ := hu
      obtain ⟨a, ha⟩ := hex t ht
      have haR : a ∈ R.toSubmodule := by
        show i a ∈ T.toSubmodule
        rw [ha]; exact t.2
      refine ⟨⟨a, haR⟩, ?_⟩
      show f (j ⟨a, haR⟩) = f t
      congr 1
      exact Subtype.ext ha

end GlobalTheory
