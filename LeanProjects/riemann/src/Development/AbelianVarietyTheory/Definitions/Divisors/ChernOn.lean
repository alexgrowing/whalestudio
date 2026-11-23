import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.Mean4O

section Model

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt

variable {e : ℕ} {M : Man e} {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def Man.pull (M : Man e) (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ)) (u : M.Fun) :
    ∀ σ : k →+* ℂ, CxPts p σ → ℝ := fun σ z => u (ε σ) (π σ z)

variable (K : Calc M) (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ)) (ν : ℝ)
  {ι : Type} [Fintype ι] (L : ι → HermLB p) (v : ι → K.V)

def Calc.ChernOn : Prop := ∀ u, M.Smooth u → ∀ hu hc (n : Option ι → ℤ) (f : M.Fun), M.Smooth f →
  chInt (ArInt.comb (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu hc) L) n) e (M.pull ε π f) =
    ν * M.int (fun _ => K.c1 (∑ i, (n (some i) : ℝ) • v i + (n none : ℝ) • K.ar u)) f

def Calc.NumOn [IsIntegral X] : Prop := ∀ u, M.Smooth u → ∀ hu hc (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
  IsArFun (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu hc) L) e Φ → ∀ a : Option ι → ℝ,
    Φ (lin a ^ (e + 1)) = ν * K.top (∑ i, a (some i) • v i + a none • K.ar u)

def Calc.Reads [IsIntegral X] : Prop :=
  IsArithVar p e ∧ 0 < ν ∧ (∀ σ, Continuous (π σ) ∧ Function.Surjective (π σ)) ∧ Function.Surjective ε ∧
  (∀ u, M.Smooth u → ∀ σ z, CxPts.CInfAt (M.pull ε π u σ) z) ∧ K.ChernOn ε π ν L v ∧ K.NumOn ε π ν L v

omit [Fintype ι] in

example : (∀ σ z, CxPts.CInfAt (M.pull ε π ((2 : ℝ) • 0) σ) z) ∧ ∀ σ σ',
    (Weight.ofFun (M.pull ε π ((2 : ℝ) • 0) σ)).IsConj (Weight.ofFun (M.pull ε π ((2 : ℝ) • 0) σ')) := by
  rw [smul_zero]
  exact ⟨fun _ z => CxPts.cInfAt_const 0 z, fun _ _ _ _ _ _ _ => rfl⟩

end Model

variable {D : D7} {Y : ShimX D.what₂.Tau} {T : Real0 Y} (P : T.Pts)

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt in

def Real0.Pts.OnModel : Prop := ∀ B : ℝ, 2 ≤ B → ∀ c, ∃ (k : Type) (_ : CommRing k) (X : Scheme.{0}) (_ : IsIntegral X)
    (p : X ⟶ Sp k) (ε : (k →+* ℂ) → Fin ((T.M c).n + 1)) (π : ∀ σ, CxPts p σ → (T.M c).X (ε σ)) (ν : ℝ) (m : ℕ)
    (L : Option (D.what₂.Tau × Fin Y.N) → HermLB p) (q : X → Y.Pt → Prop),
  0 < m ∧ (T.K B c).Reads ε π ν L (T.gen B c m) ∧ (∀ x, IsAlgPt x → ∃ y, q x y) ∧ (∀ y, Y.compPt y = c → ∃ x, q x y) ∧
  ∀ x y, q x y → IsAlgPt x ∧ Y.compPt y = c ∧
    (∀ g, P.mean c y g * Nat.card (X.residueField x →+* ℂ) =
      ∑ᶠ σ, ∑ᶠ z ∈ {z : CxPts p σ | z.1 (IsLocalRing.closedPoint ℂ) = x}, (T.M c).pull ε π g σ z) ∧
    ∀ n : Option (D.what₂.Tau × Fin Y.N) → ℤ,
      IsPtHt (ArInt.comb L n) x (P.ht B c y (∑ o, (n o : ℝ) • T.gen B c m o))

end GlobalTheory.Mean4O
