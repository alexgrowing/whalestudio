import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.TraceSemisimple

def spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) :
    Subalgebra K (Matrix (Fin a) (Fin a) K) :=
  (Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))).toSubalgebra
    (Submodule.subset_span ⟨1, by simp⟩)
    (by
      intro x y hx hy
      have h := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp⟩)

theorem mem_spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K)
    (x : Matrix (Fin a) (Fin a) K) :
    x ∈ spanAlg ρ ↔ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)) := Iff.rfl

theorem isSemisimpleRing_spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ}
    (ρ : Γ →* GL (Fin a) K)
    (h : ∀ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) :
    IsSemisimpleRing (spanAlg ρ) := by
  have : IsArtinianRing (spanAlg ρ) := IsArtinianRing.of_finite K _
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  apply Subtype.ext
  refine h x.1 x.2 fun g => ?_
  let y : spanAlg ρ := ⟨(ρ g : GL (Fin a) K), Submodule.subset_span ⟨g, rfl⟩⟩
  have hxy : x * y ∈ Ring.jacobson (spanAlg ρ) := Ideal.mul_mem_right _ _ hx
  obtain ⟨n, hn⟩ : IsNilpotent (Ring.jacobson (spanAlg ρ)) := IsSemiprimaryRing.isNilpotent
  have h1 : (x * y) ^ n = 0 := by
    have := Ideal.pow_mem_pow hxy n
    rw [hn] at this
    simpa using this
  have h2 : IsNilpotent ((x * y : spanAlg ρ) : Matrix (Fin a) (Fin a) K) :=
    ⟨n, by simpa using congrArg Subtype.val h1⟩
  exact (Matrix.isNilpotent_trace_of_isNilpotent h2).eq_zero

theorem isSSRep_of_trace_nondegenerate :
    ∀ (Γ K : Type) [Group Γ] [Field K] (a : ℕ) (ρ : Γ →* GL (Fin a) K),
    (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) →
    IsSSRep ρ := by
  intro Γ K _ _ a ρ h W hW
  have := isSemisimpleRing_spanAlg ρ h
  let f : spanAlg ρ →+* Module.End K (Fin a → K) :=
    ((Matrix.toLinAlgEquiv' (R := K) (n := Fin a)).toAlgHom.comp (spanAlg ρ).val).toRingHom
  let : Module (spanAlg ρ) (Fin a → K) := Module.compHom _ f
  have hW' : ∀ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      ∀ v ∈ W, x.mulVec v ∈ W := by
    intro x hx v hv
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hW g v hv
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [Matrix.smul_mulVec]; exact W.smul_mem c hx
  let U : Submodule (spanAlg ρ) (Fin a → K) :=
    { toAddSubmonoid := W.toAddSubmonoid
      smul_mem' := fun x v hv => hW' x.1 x.2 v hv }
  obtain ⟨U', hU⟩ := exists_isCompl U
  let W' : Submodule K (Fin a → K) :=
    { toAddSubmonoid := U'.toAddSubmonoid
      smul_mem' := fun c v hv => by
        have : (c • (1 : Matrix (Fin a) (Fin a) K)).mulVec v ∈ U' :=
          U'.smul_mem ⟨c • 1, (spanAlg ρ).smul_mem (spanAlg ρ).one_mem c⟩ hv
        rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at this }
  refine ⟨W', fun g v hv => ?_, ?_, ?_⟩
  · exact U'.smul_mem ⟨(ρ g : GL (Fin a) K), Submodule.subset_span ⟨g, rfl⟩⟩ hv
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    exact (Submodule.disjoint_def.1 hU.disjoint) v hv hv'
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have : v ∈ U ⊔ U' := by rw [hU.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 this
    exact Submodule.add_mem_sup hx hy

end GlobalTheory.TraceSemisimple
