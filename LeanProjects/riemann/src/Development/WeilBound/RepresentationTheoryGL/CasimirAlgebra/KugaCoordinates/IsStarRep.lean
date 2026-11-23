import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.ClozelCohomologicalOf
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaSt

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct Classical

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def frU (x : InfinitePlace E × Fin a × Fin a) : Matrix (Fin a) (Fin a) (Cinf E) :=
  Matrix.single x.2.1 x.2.2 (Pi.single x.1 ((1 + Complex.I) / 2) : Cinf E)

def fr (x : InfinitePlace E × Fin a × Fin a) : Herm E a :=
  ⟨frU x + star (frU x), IsSelfAdjoint.add_star_self (frU x)⟩

def iM (X : Matrix (Fin a) (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E) := (fun _ => Complex.I : Cinf E) • X

def bigM {Q : Type} [Fintype Q] [DecidableEq Q] (lab : Q → (E →+* ℂ)) (s : ℤ) (y : GL (Fin a) (Cinf E)) :
    Matrix (Q → Fin a) (Q → Fin a) ℂ :=
  Matrix.of fun I J => (∏ τ : E →+* ℂ, coord τ y.val.det) ^ (-s) * ∏ p, coord (lab p) (y.val (I p) (J p))

def bigD {Q : Type} [Fintype Q] [DecidableEq Q] (lab : Q → (E →+* ℂ)) (s : ℤ) (X : Lie E a) : Matrix (Q → Fin a) (Q → Fin a) ℂ :=
  Matrix.of fun I J => (∑ p, if (∀ r, r ≠ p → I r = J r) then coord (lab p) (X (I p) (J p)) else 0) -
    if I = J then (s : ℂ) * ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) else 0

structure IsStarRep {I : Type} [Fintype I] [DecidableEq I] (R : GL (Fin a) (Cinf E) → Matrix I I ℂ) (dR : Lie E a → Matrix I I ℂ) :
    Prop where
  one : R 1 = 1
  mul : ∀ y z, R (y * z) = R y * R z
  reg : ∀ i j, (fun y => R y i j) ∈ regFun E a
  star : ∀ y, R (star y) = (R y)ᴴ
  der : ∀ (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a), c 0 = 1 → HasDerivAt (fun t => toL (c t).val) X 0 →
    ∀ i j, HasDerivAt (fun t => R (c t) i j) (dR X i j) 0
  dstar : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), dR (toL (Star.star X)) = (dR (toL X))ᴴ

end

def Frame : Prop := ∀ (E : Type) [Field E] [NumberField E] (a : ℕ),
  Submodule.span ℝ (Set.range (fr : _ → Herm E a)) = ⊤ ∧
  ∃ c : InfinitePlace E × Fin a × Fin a → InfinitePlace E × Fin a × Fin a → InfinitePlace E × Fin a × Fin a → ℝ,
    (∀ i j k, c j i k = -c i j k) ∧
    (∀ i j, (fr i).1 * (fr j).1 - (fr j).1 * (fr i).1 = ∑ k, c i j k • iM (fr k).1) ∧
    ∀ k j, iM (fr k).1 * (fr j).1 - (fr j).1 * iM (fr k).1 = ∑ i, c i j k • (fr i).1

def FrameCas : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
  (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (φ : Lie E a →ₗ[ℝ] Module.End ℂ M),
  ∑ k : InfinitePlace E × Fin a × Fin a, φ (toL (fr k).1) * φ (toL (fr k).1) -
      ∑ k : InfinitePlace E × Fin a × Fin a, φ (toL (iM (fr k).1)) * φ (toL (iM (fr k).1)) =
    (2 : ℂ) • ∑ τ : E →+* ℂ, ∑ i, ∑ j, cx τ φ i j * cx τ φ j i

def CxExpand : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
  (N : Type) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (φ : Lie E a →ₗ[ℝ] N) (X : Lie E a),
  φ X = ∑ τ : E →+* ℂ, ∑ i, ∑ j, coord τ (X i j) • cx τ φ i j

def TensForm : Prop := ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
  (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) → (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) →
  ∃ B : (V ⊗[ℂ] (Fin d → ℂ)) →ₗ[ℂ] (V ⊗[ℂ] (Fin d → ℂ)) →ₗ⋆[ℂ] ℂ,
    (∀ x y, B y x = starRingEnd ℂ (B x y)) ∧ (∀ x, x ≠ 0 → 0 < (B x x).re) ∧
    (∀ φ ψ v w, B (φ ⊗ₜ v) (ψ ⊗ₜ w) = H ψ φ * (star w ⬝ᵥ v)) ∧
    ∀ (T : Matrix (Fin d) (Fin d) ℂ) (c : ℝ), Tᴴ = T → (∀ v, (star v ⬝ᵥ (T *ᵥ v)).re ≤ c * (star v ⬝ᵥ v).re) →
      ∀ x, (B ((Matrix.toLin' T).lTensor V x) x).re ≤ c * (B x x).re

def Harmonic : Prop := ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M),
  (∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → dCo L ω = 0) →
  ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → ω ≠ 0 → HasCohomology κ L

def BigRep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Q : Type) [Fintype Q] [DecidableEq Q]
  (lab : Q → (E →+* ℂ)) (s : ℤ), IsStarRep (bigM (a := a) lab s) (bigD lab s)

def BigCx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Q : Type) [Fintype Q] [DecidableEq Q]
  (lab : Q → (E →+* ℂ)) (s : ℤ),
  (∀ (τ : E →+* ℂ) (i j : Fin a) (f : TV a ℂ Q), cx τ (bigD lab s) i j *ᵥ f =
    tE (fib lab τ) (0 : Fin a → Fin a → Module.End ℂ ℂ) i j f - if i = j then (s : ℂ) • f else 0) ∧
  ∀ (y : GL (Fin a) (Cinf E)) (p p' : Q), lab p = lab p' → ∀ f : TV a ℂ Q,
    bigM lab s y *ᵥ pm (Equiv.swap p p') f = pm (Equiv.swap p p') (bigM lab s y *ᵥ f)

def Summand : Prop := ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (I : Type) [Fintype I] [DecidableEq I]
  (R : GL (Fin a) (Cinf E) → Matrix I I ℂ) (dR : Lie E a → Matrix I I ℂ), IsStarRep R dR →
  ∀ D : Submodule ℂ (I → ℂ), (∀ y, ∀ v ∈ D, R y *ᵥ v ∈ D) → ∀ v₀ ∈ D, v₀ ≠ 0 →
  ∃ (Ξ : AlgRep E a) (J : Matrix I (Fin Ξ.d) ℂ), Jᴴ * J = 1 ∧ (∀ w, J *ᵥ w ∈ D) ∧ Jᴴ *ᵥ v₀ ≠ 0 ∧
    (∀ y, R y * J = J * Ξ.mat y) ∧ (∀ y, Jᴴ * R y = Ξ.mat y * Jᴴ) ∧ ∀ X, dR X * J = J * Ξ.dmat X

def Cochain : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
  (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (ρ : Kinf E a → Module.End ℂ M)
  (q N : ℕ) (lab : Fin q → (E →+* ℂ)) (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))),
  (∀ k k', tl k ≠ barE E (tl k')) → (∀ γ, actT (lab3 (barE E) lab tl) (kap E a) ρ γ η = η) → altPair tl η ≠ 0 →
  ∃ ω : Herm E a [⋀^Fin N]→ₗ[ℝ] TV a M (Fin q), ω ≠ 0 ∧ IsCochain (actT lab (kap E a) ρ) ω ∧
    ∀ p p', pm (Equiv.swap (Sum.inl p) (Sum.inl p')) η = -η → ∀ X, pm (Equiv.swap p p') (ω X) = -ω X

def CasVal : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (F : Fin n → Fin n → Module.End ℂ M)
  (l : Fin n → ℂ), GlRel F → HasChar F l →
  (∑ i, F i i = algebraMap ℂ _ (∑ k : Fin n, (l k + (k : ℕ)))) ∧
  ∑ i, ∑ j, F i j * F j i = algebraMap ℂ _ (∑ k : Fin n, ((l k + ((n : ℂ) - 1) / 2) ^ 2 - (((n : ℂ) - 1) / 2 - (k : ℕ)) ^ 2))

def KugaGlue : Prop := KugaAbs → Frame → FrameCas → CxExpand → TensForm → Harmonic → Kuga

def CoefGlue : Prop := CasBound → BigRep → BigCx → Summand → Cochain → CasVal → Coef

end PositivityTheory.Rg.Cz

end
