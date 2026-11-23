import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EvalStalk
import GroundTheory.HeightsAndTheta.Heights.FinrankFibreAtOfIsInvertibleSheaf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ} (X : ProjScheme A N) {ρ : A →+* ℂ}

def point (x : X.complexPoints ρ) : X.X := Classical.choose x.2

lemma ι_point (x : X.complexPoints ρ) : X.ι.base (X.point x) = projPoint ρ x.1 :=
  Classical.choose_spec x.2

lemma isOver_point (x : X.complexPoints ρ) : IsOver ρ x.1.rep (X.ι.base (X.point x)) :=
  (X.ι_point x) ▸ isOver_projPoint ρ x.1

lemma ι_injective : Function.Injective X.ι.base := X.ι.isClosedEmbedding.injective

def evalAtPoint (x : X.complexPoints ρ) : locRing X.X (X.point x) →+* ℂ :=
  X.evalStalk (X.isOver_point x)

abbrev Fibre (L : X.X.Modules) (x : X.complexPoints ρ) : Type u :=
  fibreAt L (X.point x) (X.evalAtPoint x)

def sectionValue {L : X.X.Modules} (x : X.complexPoints ρ) {U : X.X.Opens} (hx : X.point x ∈ U)
    (s : ((preMod X.X).obj L).obj (op U)) : X.Fibre L x :=
  value _ hx s

lemma point_conjPoint (x : X.complexPoints ρ) : X.point (X.conjPoint ρ x) = X.point x := by
  apply X.ι_injective
  rw [ι_point, ι_point]
  exact projPoint_conj ρ x.1

lemma exists_rep_conj (v : CP N) : ∃ c : ℂˣ, (CP.conj v).rep = (c : ℂ) • CP.conjVec v.rep := by
  have h : Projectivization.mk ℂ (CP.conj v).rep (CP.conj v).rep_nonzero =
      Projectivization.mk ℂ (CP.conjVec v.rep) (CP.conjVec_ne_zero v.rep_nonzero) := by
    rw [Projectivization.mk_rep, ← CP.conj_mk v.rep v.rep_nonzero, Projectivization.mk_rep]
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ (CP.conj v).rep_nonzero
    (CP.conjVec_ne_zero v.rep_nonzero)).1 h
  exact ⟨c, hc.symm⟩

lemma evalStalk_eq_conj {p : X.X} {w w' : Fin (N + 1) → ℂ} (c : ℂˣ)
    (hw : w' = (c : ℂ) • CP.conjVec w) (h : IsOver ρ w (X.ι.base p))
    (h' : IsOver ((starRingEnd ℂ).comp ρ) w' (X.ι.base p)) :
    X.evalStalk h' = (starRingEnd ℂ).comp (X.evalStalk h) := by
  subst hw
  have : X.evalStalk h' = X.evalStalk (h.conj.smul c.ne_zero) := rfl
  rw [this, X.evalStalk_smul h.conj c.ne_zero, X.evalStalk_conj h]

lemma evalAtPoint_conjPoint_germ (x : X.complexPoints ρ) {U : X.X.Opens} (hx : X.point x ∈ U)
    (hx' : X.point (X.conjPoint ρ x) ∈ U) (f : ringOn X.X U) :
    X.evalAtPoint (X.conjPoint ρ x) (germR hx' f) = starRingEnd ℂ (X.evalAtPoint x (germR hx f)) := by
  obtain ⟨c, hc⟩ := exists_rep_conj x.1
  have key : ∀ (q : X.X) (e : q = X.point x)
      (h' : IsOver ((starRingEnd ℂ).comp ρ) (CP.conj x.1).rep (X.ι.base q)) (hq : q ∈ U),
      X.evalStalk h' (germR hq f) = starRingEnd ℂ (X.evalAtPoint x (germR hx f)) := by
    intro q e h' hq
    subst e
    rw [X.evalStalk_eq_conj c hc (X.isOver_point x) h']
    rfl
  exact key _ (X.point_conjPoint x) (X.isOver_point _) hx'

end ProjScheme

end

end GroundTheory.Heights₂.Heights
