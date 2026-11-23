import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.VecSubquot

theorem exists_irreducible_subquotient_of_ne_zero : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (x : V), x ≠ 0 →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      τ.IsIrreducible ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧
        ∀ (g : G) (c : ℂ), ρ g x = c • x → τ g y = c • y := by
  intro G V _ _ _ ρ x hx

  let s : Set (Submodule ℂ V) := {N | (∀ (g : G), ∀ v ∈ N, ρ g v ∈ N) ∧ x ∉ N}
  have hbot : (⊥ : Submodule ℂ V) ∈ s := ⟨fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], by simpa using hx⟩
  obtain ⟨N, -, hmax⟩ := zorn_le_nonempty₀ s (fun c hcs hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hd : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨fun g v hv => ?_, fun hx' => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨M, hM, hvM⟩ := (Submodule.mem_sSup_of_directed hne hd).1 hv
      exact le_sSup hM ((hcs hM).1 g v hvM)
    · obtain ⟨M, hM, hxM⟩ := (Submodule.mem_sSup_of_directed hne hd).1 hx'
      exact (hcs hM).2 hxM) ⊥ hbot
  obtain ⟨hNst, hxN⟩ := hmax.prop

  let O : Submodule ℂ V := Submodule.span ℂ (Set.range fun g : G => ρ g x)
  have hOst : ∀ (g : G), ∀ v ∈ O, ρ g v ∈ O := by
    intro g v hv
    have : O.map (ρ g) ≤ O := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp only [map_mul, Module.End.mul_apply]⟩
    exact this ⟨v, hv, rfl⟩
  have hxO : x ∈ O := Submodule.subset_span ⟨1, by simp only [map_one, Module.End.one_apply]⟩
  let T : Subrepresentation ρ := ⟨N, fun g v hv => hNst g v hv⟩
  let S : Subrepresentation ρ := ⟨N ⊔ O, fun g v hv => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (hNst g a ha) (hOst g b hb)⟩
  have hxS : x ∈ S.toSubmodule := Submodule.mem_sup_right hxO
  have hcov : T ⋖ S := by
    refine ⟨lt_of_le_of_ne (fun v hv => Submodule.mem_sup_left hv) fun h => hxN ?_, ?_⟩
    · have : x ∈ (S : Set V) := hxS
      rw [← h] at this
      exact this
    · intro T' h1 h2
      have hle : N ≤ T'.toSubmodule := h1.le
      have hxT' : x ∈ T'.toSubmodule := by
        by_contra hn
        have hmem : T'.toSubmodule ∈ s := ⟨fun g v hv => T'.apply_mem_toSubmodule g hv, hn⟩
        have heq : T'.toSubmodule = N := le_antisymm (hmax.2 hmem hle) hle
        exact h1.ne (Subrepresentation.toSubmodule_injective heq.symm)
      have hST' : S.toSubmodule ≤ T'.toSubmodule := by
        refine sup_le hle ?_
        rw [Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        exact T'.apply_mem_toSubmodule g hxT'
      exact h2.not_ge hST'
  refine ⟨_, inferInstance, inferInstance, GlobalTheory.SmGL.subQuot S T,
    Submodule.Quotient.mk (⟨x, hxS⟩ : S.toSubmodule), GlobalTheory.SmGL.isIrreducible_subQuot hcov,
    ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩, ?_, ?_⟩
  · intro h0
    rw [Submodule.Quotient.mk_eq_zero] at h0
    exact hxN h0
  · intro g c hgc
    show Submodule.Quotient.mk (S.toRepresentation g ⟨x, hxS⟩) = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext hgc

end GlobalTheory.VecSubquot
