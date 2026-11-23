import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.Ar.Rec

section Tuple

open ReciprocityTheory.ChartRestriction.G.T0 (TVar OmS sImg)

variable (K : Type) [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  {Ω : Type} [Field Ω] [Algebra K Ω]

def rkL (M : Submodule (𝓞 K) V) : ℕ := Module.finrank K (Submodule.span K (M : Set V))

def IsFull (M : Submodule (𝓞 K) V) (x : Fin (rkL K M) → V) : Prop := (∀ i, x i ∈ M) ∧ LinearIndependent K x

def degAt (M : Submodule (𝓞 K) V) (ip : (K →+* ℂ) → V → V → ℂ) (x : Fin (rkL K M) → V) : ℝ :=
  (Real.log ((Submodule.span (𝓞 K) (Set.range x)).toAddSubgroup.relIndex M.toAddSubgroup : ℕ) -
    ∑ σ : K →+* ℂ, Real.log ‖(Matrix.of fun a b => ip σ (x a) (x b)).det‖ / 2) / (Module.finrank ℚ K : ℝ)

def degL (M : Submodule (𝓞 K) V) (ip : (K →+* ℂ) → V → V → ℂ) : ℝ := degAt K M ip (Classical.epsilon (IsFull K M))

abbrev Gens (V : Type) : Type := Σ n : ℕ, Fin (n + 1) → V

instance : Nonempty (Gens V) := ⟨⟨0, fun _ => 0⟩⟩

def IsGen (W : Submodule (𝓞 K) V) (ev : V → Ω) (g : Gens V) : Prop :=
  Submodule.span (𝓞 K) (Set.range g.2) = W ∧ ev (g.2 0) ≠ 0

def xs (ev : V → Ω) (g : Gens V) (k : Fin g.1) : Ω := ev (g.2 k.succ) / ev (g.2 0)

def delAt (Dn : ℕ) (ev : V → Ω) (g : Gens V) : ℕ :=
  Module.finrank (IntermediateField.adjoin K (Set.range (sImg (D := Dn) (0 : Fin (g.1 + 1)) (xs ev g)))) (OmS Ω Dn g.1)

open Classical in

def delL (Dn : ℕ) (W : Submodule (𝓞 K) V) (ev : V → Ω) : ℕ :=
  if ∃ g, IsGen K W ev g then delAt K Dn ev (Classical.epsilon (IsGen K W ev)) else 0

def cImg {Dn N : ℕ} (x : Fin N → Ω) (p : TVar Dn N) : MvPolynomial (Fin (Dn + 1) × Fin N) Ω :=
  Fin.cases (motive := fun _ => MvPolynomial (Fin (Dn + 1) × Fin N) Ω)
    (-∑ k, MvPolynomial.X (p.1, k) * MvPolynomial.C (x k)) (fun k => MvPolynomial.X (p.1, k)) p.2

def IsChow (Dn : ℕ) {N : ℕ} (x : Fin N → Ω) (f : MvPolynomial (TVar Dn N) K) : Prop :=
  f ≠ 0 ∧ RingHom.ker (MvPolynomial.aeval (R := K) (cImg (Dn := Dn) x)) = Ideal.span {f}

def finHt {σ : Type} (f : MvPolynomial σ K) : ℝ :=
  -Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanFinset (𝓞 K) f.support fun m => f.coeff m) : ℚ) : ℝ) /
    (Module.finrank ℚ K : ℝ)

def sphP (n : ℕ) : Measure (Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1) :=
  ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ)⁻¹ • (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere

def onbMat (n : ℕ) (g : Gens V) (ipσ : V → V → ℂ) : Matrix (Fin (g.1 + 1)) (Fin n) ℂ :=
  Classical.epsilon fun A : Matrix (Fin (g.1 + 1)) (Fin n) ℂ =>
    A.conjTranspose * (Matrix.of fun k l => ipσ (g.2 l) (g.2 k)) * A = 1

def archHt (Dn n : ℕ) (g : Gens V) (σ : K →+* ℂ) (ipσ : V → V → ℂ) (f : MvPolynomial (TVar Dn g.1) K) : ℝ :=
  ∫ t : Fin (Dn + 1) → Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1,
    Real.log ‖MvPolynomial.eval (fun p : TVar Dn g.1 =>
      (onbMat n g ipσ).mulVec (fun a => (t p.1 : EuclideanSpace ℂ (Fin n)) a) p.2) (MvPolynomial.map σ f)‖
    ∂(Measure.pi fun _ => sphP n)

def htAt (Dn n : ℕ) (g : Gens V) (ip : (K →+* ℂ) → V → V → ℂ) (f : MvPolynomial (TVar Dn g.1) K) : ℝ :=
  (finHt K f + (∑ σ : K →+* ℂ, archHt K Dn n g σ (ip σ) f) / (Module.finrank ℚ K : ℝ)) / (f.totalDegree : ℝ) +
    ((harmonic (n - 1) : ℚ) : ℝ) / 2

open Classical in

def htL (Dn : ℕ) (W : Submodule (𝓞 K) V) (ev : V → Ω) (ip : (K →+* ℂ) → V → V → ℂ) : ℝ :=
  if (∃ g, IsGen K W ev g) ∧ ∃ f, IsChow K Dn (xs ev (Classical.epsilon (IsGen K W ev))) f then
    htAt K Dn (rkL K W) (Classical.epsilon (IsGen K W ev)) ip
      (Classical.epsilon (IsChow K Dn (xs ev (Classical.epsilon (IsGen K W ev)))))
  else 0

end Tuple

end GlobalTheory.CompanionTheory.Ar.Rec
