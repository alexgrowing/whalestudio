import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PlaceAwayRed

theorem redFn_conj_locFin_eq_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (a : GfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) (PP : Pl D.host.E), PP.under (𝓞 D.host.F) ≠ v → ∀ k : Gv V v, finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β → redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = 1 := by
  intro D V β a v PP hPP k hS
  refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {PP.under (𝓞 D.host.F)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
  rw [Finset.mem_singleton] at hu
  subst hu
  have e : proj D.sp.cm.sig V.gram (PP.under (𝓞 D.host.F)) (embV V v k) = 1 := proj_emb_ne _ _ hPP k
  show proj D.sp.cm.sig V.gram (PP.under (𝓞 D.host.F)) ((a : GA D V) * (locFin V v k : GA D V) * ((a⁻¹ : GfC V) : GA D V)) = 1
  rw [coe_locFin, MonoidHom.map_mul, MonoidHom.map_mul, e, mul_one, ← MonoidHom.map_mul, ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, MonoidHom.map_one]

end GlobalTheory.PlaceAwayRed

end
