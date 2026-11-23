import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldBasisToroidalModelSnc
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logVectorField_basis_toroidalModel_snc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (x : Y.X), x ∈ U.1 → ∃ (f : Γ(Y.X, U.1)) (W : Y.X.affineOpens) (hW : W.1 ≤ U.1) (m : ℕ) (t : Fin m → Γ(Y.X, W.1)) (b : Module.Basis (Fin Dw.dim) Γ(Y.X, W.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) W)), x ∈ W.1 ∧ W.1 = Y.X.basicOpen f ∧ (∀ g ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal W, g ∈ Ideal.span {∏ i, t i}) ∧ ∏ i, t i ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal W ∧ ∀ (i : Fin m) (k : Fin Dw.dim), ((b k).1 : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (t i) = if (k : ℕ) = i then t i else 0 := by
  first | exact @GlobalTheory.LogBasis.exists_logDer_basis | exact GlobalTheory.LogBasis.exists_logDer_basis | (intros; apply GlobalTheory.LogBasis.exists_logDer_basis <;> assumption)
