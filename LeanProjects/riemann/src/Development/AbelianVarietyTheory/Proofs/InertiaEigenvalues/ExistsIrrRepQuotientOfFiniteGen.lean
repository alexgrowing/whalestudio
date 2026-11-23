import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinCuspOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial MeasureTheory Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DZero
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DZero

theorem exists_irrRep_quotient_of_finite_gen : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), GlobalTheory.PRep.IsSmooth π → Nontrivial V → ∀ s : Finset V, Submodule.span ℂ (Set.range fun p : G × s => π p.1 (p.2 : V)) = ⊤ → ∃ (σ : IrrRep G) (p : V →ₗ[ℂ] σ.V), Function.Surjective p ∧ ∀ g v, p (π g v) = σ.ρ g (p v) := by
  intro G V _ _ _ _ _ π hπ hV s hs
  classical

  have htop : ∀ N : Submodule ℂ V, (∀ (g : G), ∀ v ∈ N, π g v ∈ N) →
      Submodule.span ℂ ((s : Set V)) ≤ N → N = ⊤ := by
    intro N hN hsN
    rw [eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact hN g _ (hsN (Submodule.subset_span v.2))
  let S : Set (Submodule ℂ V) := {N | (∀ (g : G), ∀ v ∈ N, π g v ∈ N) ∧ N ≠ ⊤}
  have hbot : (⊥ : Submodule ℂ V) ∈ S := ⟨fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], bot_ne_top⟩
  have hcomp := Submodule.finset_span_isCompactElement (R := ℂ) s
  obtain ⟨N, -, hmax⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hd : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨fun g v hv => ?_, fun htop' => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨M, hM, hvM⟩ := (Submodule.mem_sSup_of_directed hne hd).1 hv
      exact le_sSup hM ((hcS hM).1 g v hvM)
    · obtain ⟨M, hM, hsM⟩ := (CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le _ _).1 hcomp c hne hd
        (by rw [htop']; exact le_top)
      exact (hcS hM).2 (htop M (hcS hM).1 hsM)) ⊥ hbot
  obtain ⟨hNst, hNtop⟩ := hmax.prop
  let T : Subrepresentation π := ⟨N, fun g v hv => hNst g v hv⟩
  have hT : IsCoatom T := by
    refine ⟨fun h => hNtop (congrArg Subrepresentation.toSubmodule h), fun T' hT' => ?_⟩
    by_contra hne
    have hmem : T'.toSubmodule ∈ S := ⟨fun g v hv => T'.apply_mem_toSubmodule g hv,
      fun h => hne (Subrepresentation.toSubmodule_injective h)⟩
    have heq : T'.toSubmodule = N := le_antisymm (hmax.2 hmem hT'.le) hT'.le
    exact hT'.ne (Subrepresentation.toSubmodule_injective heq.symm)
  have hi := isIrreducible_subQuot hT.covBy_top
  let q : (⊤ : Subrepresentation π).toRepresentation.IntertwiningMap (subQuot ⊤ T) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hsm : IsSmooth (subQuot ⊤ T) :=
    IsSubquotient.isSmooth ⟨⊤, q, Submodule.Quotient.mk_surjective _⟩ hπ
  let σ : IrrRep G := ⟨_, subQuot ⊤ T, hsm, hi⟩
  let p : V →ₗ[ℂ] σ.V := (Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
    LinearMap.id (fun _ => trivial)
  refine ⟨σ, p, fun w => ?_, fun g v => rfl⟩
  obtain ⟨⟨v, -⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨v, rfl⟩

end GlobalTheory.DZero
