import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaCharacterUnramified
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

open GlobalTheory.VecInv Formalism.IndefR.Lev

theorem mu_detAt_eq_levChi {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) (t : T0)
    (hQ : L.Q t = ∅) {P : Finset (Pl D.host.E)} {e : AE D} (hee : e * e = e)
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (he : IsIdemSum e P) {κ : GA D (Vc D i)}
    (hκ : IsLevelLift (Vc D i) (L.βV i) (L.datVt i t) 1 κ) :
    ((L.mu t ((i : ℕ) + 1) (detAt e hee _ κ) : Circle) : ℂ) = levChi _ (L.βV i) (flagL (L.datVt i t)) κ := by
  have sV : finE (Vc D i) κ ∈ St (L.βV i) := parLev_St hκ.2.1
  have tg : ∀ PP ∈ L.Pg, redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blkOf D.R.r D.R.t) := fun PP h =>
    parLev_g hκ.2.1 h
  have one : ∀ PP ∈ L.Pg, upperLeftBlock (r_le_V i) (redFn (L.βV i) PP (finE (Vc D i) κ)) = 1 := fun PP h =>
    congrFun hκ.2.2 ⟨PP, h⟩
  obtain ⟨aV, haV, hrV⟩ := exists_det_int sV
  have mV := (mu_val hL t i hP he (detAt e hee _ κ) _ aV _ (isDetAt_detAt e hee _ κ) haV fun PP _ => hrV PP).1
  rw [levChi_flag_V i t tg, mV, hQ, Finset.prod_empty, Finset.prod_empty, one_mul]
  refine congrArg (fun z : ℂˣ => ((z * 1 : ℂˣ) : ℂ)) (Finset.prod_congr rfl fun PP h => ?_)
  rw [(GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ 0 (r_le_V i) _).1 (blockTri_blkOf_le _ _ (tg PP h)), one PP h, map_one, one_mul]

theorem smul_of_splitFac {D : D7} {X ι : Type} {u v : X → ℂ} {c : ι → ℂ} {μ η : (AE D)ˣ →* Circle} {x y : (AE D)ˣ} {z : ℂ}
    (h : (∏ i ∈ (∅ : Finset ι), c i) • u = ((splitFacO μ (μ * η⁻¹) x y : Circle) : ℂ) • v) (hy : y = 1) (hη : η x = 1)
    (hz : ((μ x : Circle) : ℂ) = z) : u = z⁻¹ • v := by
  rwa [Finset.prod_empty, one_smul, splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, hη, inv_one, mul_one, hy, map_one,
    mul_one, Circle.coe_inv, hz] at h

end GlobalTheory.GalOne
