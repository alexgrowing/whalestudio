import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def Char0 (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : Prop := ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p

def Pts (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Set (Subring Ω) :=
  {R | ∃ p : Cpt ξ, Char0 ξ p ∧ R = regAt ξ p}

def IsLocAt [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (q : Ideal A) (R : Subring Ω) : Prop :=
  ∀ a : Ω, a ∈ R ↔ ∃ s : A, s ∉ q ∧ (s : Ω) * a ∈ A

structure IsSncPatch [Algebra ℚ Ω] (Pt Bd : Set (Subring Ω)) (e : ℕ) (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) :
    Prop where
  fg : A.FG
  smooth : Algebra.Smooth ℚ A
  le : n ≤ e
  li : LinearIndependent A fun i => KaehlerDifferential.D ℚ A (z i)
  span : Submodule.span A (Set.range fun i => KaehlerDifferential.D ℚ A (z i)) = ⊤
  pts : ∀ q : Ideal A, q.IsPrime → ∃ R ∈ Pt, IsLocAt A q R ∧ (R ∈ Bd ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)

theorem isSncPatch_rat : IsSncPatch (Ω := ℚ) {⊤} ∅ 0 ⊤ Fin.elim0 0 := by
  have hs : Function.Surjective (algebraMap ℚ (⊤ : Subalgebra ℚ ℚ)) := fun a => ⟨a.1, Subtype.ext (by simp)⟩
  have : Subsingleton (KaehlerDifferential ℚ (⊤ : Subalgebra ℚ ℚ)) :=
    KaehlerDifferential.subsingleton_of_surjective _ _ hs
  refine ⟨(inferInstance : Algebra.FiniteType ℚ ℚ).out, ?_, le_rfl, ?_, ?_, ?_⟩
  · exact Algebra.Smooth.of_equiv Subalgebra.topEquiv.symm
  · exact linearIndependent_empty_type
  · exact Subsingleton.elim _ _
  · intro q hq
    refine ⟨⊤, rfl, fun a => ⟨fun _ => ⟨1, ?_, by simp⟩, fun _ => trivial⟩, ?_⟩
    · exact fun h => hq.ne_top ((Ideal.eq_top_iff_one q).2 h)
    · simp

end GlobalTheory.CompanionTheory.Ar.SncBase
