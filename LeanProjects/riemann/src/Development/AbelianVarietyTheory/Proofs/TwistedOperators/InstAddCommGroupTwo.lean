import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory.SmGL.Exponents

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def leviChar {R β : Type} [CommRing R] [Fintype β] (c : β → Type) [∀ j, Fintype (c j)]
    [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ) : Levi R c →* ℂˣ :=
  ∏ j, (detChar (c j) (χ j)).comp (Pi.evalMonoidHom (fun j => GL (c j) R) j)

theorem leviChar_apply {R β : Type} [CommRing R] [Fintype β] (c : β → Type) [∀ j, Fintype (c j)]
    [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ) (g : Levi R c) :
    leviChar c χ g = ∏ j, χ j (Matrix.GeneralLinearGroup.det (g j)) := by
  simp [leviChar]

def wordMult {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (w : List ℂˣ) : ℕ∞ :=
  if w.length = n then jhMult (ofChar (torusChar fun i : Fin n => unrChar k (w.getD i 1))) (jacB π)
  else 0

theorem wordMult_ofFn {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (z : Fin n → ℂˣ) :
    wordMult π (List.ofFn z) = jhMult (ofChar (torusChar fun i => unrChar k (z i))) (jacB π) := by
  simp [wordMult]

theorem wordMult_of_ne {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) {w : List ℂˣ}
    (h : w.length ≠ n) : wordMult π w = 0 := by
  rw [wordMult, if_neg h]

def jacEquiv {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W} (φ : π.Equiv τ) :
    (jac e π).Equiv (jac e τ) :=
  LocGL.equivOfBijective (jacMap e φ.toIntertwiningMap) (Function.bijective_iff_has_inverse.2
    ⟨jacMap e φ.symm.toIntertwiningMap, fun x => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact congrArg Submodule.Quotient.mk (φ.symm_apply_apply v), fun x => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact congrArg Submodule.Quotient.mk (φ.apply_symm_apply v)⟩)

theorem wordMult_congr {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V}
    {τ : Representation ℂ (GL (Fin n) k) W} (φ : π.Equiv τ) (w : List ℂˣ) :
    wordMult π w = wordMult τ w := by
  unfold wordMult
  split_ifs
  · exact jhMult_congr_right _ (Representation.Equiv.mk (jacEquiv (points (Fin n)) φ).toLinearEquiv
      fun t => (jacEquiv (points (Fin n)) φ).isIntertwining' _)
  · rfl

instance instAddCommGroupTwo : ∀ x, AddCommGroup (Two V W x)
  | false => inferInstanceAs (AddCommGroup V)
  | true => inferInstanceAs (AddCommGroup W)

instance instModuleTwo : ∀ x, Module ℂ (Two V W x)
  | false => inferInstanceAs (Module ℂ V)
  | true => inferInstanceAs (Module ℂ W)

def twoRep {R a b : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (π₁ : Representation ℂ (GL a R) V) (π₂ : Representation ℂ (GL b R) W) :
    ∀ x, Representation ℂ (GL (Two a b x) R) (Two V W x)
  | false => π₁
  | true => π₂

end GlobalTheory.SmGL.Exponents
