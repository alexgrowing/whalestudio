import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSmoothAtGenerator
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLineBundleInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MSmoothAndSemiPosIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetWeightIsCInfOfPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAdelicMetricDivisorRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtOfDivisorRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedMetricLocalPotentialExists
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_smooth_at_generator : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) (Δ : Y.Dv) (m : (cxSt F).Met Y σ Δ), (cxSt F).mSmooth Y σ Δ m → ∀ (f : Y.Fn) (z0 : Pts Y σ), Δ.GeneratesAt (under z0) f → CInfAt (fun z => lnN m f z) z0 := by
  first | exact @GlobalTheory.Mean4O.LnNSmooth.cInfAt_lnN | exact GlobalTheory.Mean4O.LnNSmooth.cInfAt_lnN | (intros; apply GlobalTheory.Mean4O.LnNSmooth.cInfAt_lnN <;> assumption)
