import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalIntersectionSmoothPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numerical_intersection_smooth_pullback : GlobalTheory.Published.ArCalc → ∀ (e : ℕ) (M : Man e) (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (K : Calc M) (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ)) (ν : ℝ) (ι : Type) [Fintype ι] (L : ι → HermLB p) (v : ι → K.V), IsArithVar p e → (∀ u, M.Smooth u → ∀ σ z, CxPts.CInfAt (M.pull ε π u σ) z) → K.NumOn ε π ν L v → ∀ u, M.Smooth u → ∀ hu hc (n : Option ι → ℤ) (f : M.Fun), M.Smooth f → (∀ σ σ', (Weight.ofFun (M.pull ε π f σ)).IsConj (Weight.ofFun (M.pull ε π f σ'))) → chInt (ArInt.comb (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu hc) L) n) e (M.pull ε π f) = ν * M.int (fun _ => K.c1 (∑ i, (n (some i) : ℝ) • v i + (n none : ℝ) • K.ar u)) f := by
  first | exact @GlobalTheory.Mean4O.ChernInv.chernOn_of_numOn | exact GlobalTheory.Mean4O.ChernInv.chernOn_of_numOn | (intros; apply GlobalTheory.Mean4O.ChernInv.chernOn_of_numOn <;> assumption)
