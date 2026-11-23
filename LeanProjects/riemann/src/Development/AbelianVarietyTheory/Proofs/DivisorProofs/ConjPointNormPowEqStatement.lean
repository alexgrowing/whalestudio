import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPointNormPowEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_point_norm_pow_eq : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y) (A : Adl C Y) (L : HermLB V.p) (k : ℕ), V.Induces A L k → ∀ (σ σ' : F →+* ℂ) (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → C.pn Y σ' A.D (A.m σ') (C.cx Y σ' (genAt A.D (under y'))) y' ^ k = C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y ^ k := by
  first | exact @GlobalTheory.Mean4O.Cover.pn_pow_conj | exact GlobalTheory.Mean4O.Cover.pn_pow_conj | (intros; apply GlobalTheory.Mean4O.Cover.pn_pow_conj <;> assumption)
