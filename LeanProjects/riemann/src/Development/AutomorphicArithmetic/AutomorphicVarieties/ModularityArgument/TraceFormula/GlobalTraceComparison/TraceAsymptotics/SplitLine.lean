import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.LFun.SatCompare

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem eq_bot_or_top {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) (S : Submodule ℂ V)
    (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S) : S = ⊥ ∨ S = ⊤ := by
  let P : Subrepresentation ρ := ⟨S, fun g x hx => hS g x hx⟩
  exact (hi.eq_bot_or_eq_top P).imp (fun e => congrArg Subrepresentation.toSubmodule e)
    fun e => congrArg Subrepresentation.toSubmodule e

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem rank_le [SecondCountableTopology G] {ρ : Representation ℂ G V} (hs : IsSmooth ρ)
    (hi : ρ.IsIrreducible) {v : V} (hv : v ≠ 0) : Module.rank ℂ V ≤ Cardinal.aleph0 := by
  rw [← rank_top]
  refine GlobalTheory.CompanionTheory.SatAe.rank_le_of_simple (⊤ : Submodule ℂ V) (fun g : G => ρ g)
    ((Submodule.ne_bot_iff _).2 ⟨v, trivial, hv⟩) (fun W _ hW => eq_bot_or_top hi W hW) fun x _ => ?_
  exact ⟨_, GlobalTheory.CompanionTheory.SatAe.countable_orbit ρ x (hs x), fun _ _ => trivial, fun g => Submodule.subset_span ⟨g, rfl⟩⟩

private theorem fixed_eq_span [SecondCountableTopology G] {ρ : Representation ℂ G V} {K : Subgroup G}
    (hs : IsSmooth ρ) (hi : ρ.IsIrreducible) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K)
    (hcomm : ∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁)
    {v : V} (hv : v ∈ fixed ρ K) (hv0 : v ≠ 0) : fixed ρ K = Submodule.span ℂ {v} := by
  have hr := rank_le hs hi hv0
  have hb : GlobalTheory.CompanionTheory.SatAe.IsBiSimple ρ := fun S h1 _ => eq_bot_or_top hi S h1
  have hle : Submodule.span ℂ {v} ≤ fixed ρ K := (Submodule.span_singleton_le_iff_mem _ _).2 hv
  have hH : ∀ f ∈ Hecke ℂ K, ∀ x ∈ Submodule.span ℂ {v}, heckeVec ρ K f x ∈ Submodule.span ℂ {v} := by
    intro f hf x hx
    obtain ⟨c, hc'⟩ := GlobalTheory.CompanionTheory.SatAe.exists_scalar hs hc hK hcomm hb hr f hf
    rw [hc' x (hle hx)]
    exact Submodule.smul_mem _ _ hx
  have hB : ∀ b : Module.End ℂ V, (∀ g, b * ρ g = ρ g * b) → ∀ x ∈ Submodule.span ℂ {v},
      b x ∈ Submodule.span ℂ {v} := by
    intro b hbc x hx
    obtain ⟨c, hc'⟩ := GlobalTheory.CompanionTheory.SatAe.scalar_of_simple hr (Set.range fun g => ρ g)
      (fun W hW => eq_bot_or_top hi W fun g => hW _ ⟨g, rfl⟩) b (by
        rintro _ ⟨g, rfl⟩
        exact (hbc g).symm)
    rw [hc' x]
    exact Submodule.smul_mem _ _ hx
  refine ((GlobalTheory.CompanionTheory.SatAe.fixed_simple hs hc hK hb _ hle hH hB).resolve_left fun h => hv0 ?_).symm
  have : v ∈ Submodule.span ℂ {v} := Submodule.mem_span_singleton_self v
  rw [h] at this
  exact (Submodule.mem_bot ℂ).1 this

end

theorem splitLine : SplitLine := by
  intro E _ _ _ n w τ hne
  rcases τ with @⟨V, _, _, ρ, hs, hi⟩
  change fixed ρ (KGL w n) ≠ ⊥ at hne
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hc := (isOpen_isCompact_KGL w n).2
  have hK := Final.GLintComm E w n
  have hcomm := Final.HeckeCommGL E w n ℂ
  have hline := fixed_eq_span hs hi hc hK hcomm hv hv0
  refine ⟨?_, GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_of_scalar (fun h hh => ?_) hne⟩
  · change Module.finrank ℂ (fixed ρ (KGL w n)) = 1
    rw [hline]
    exact finrank_span_singleton hv0
  · exact GlobalTheory.CompanionTheory.SatAe.exists_scalar hs hc hK hcomm (fun S h1 _ => eq_bot_or_top hi S h1)
      (rank_le hs hi hv0) h hh

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
