import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmoothStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntAtOfLocTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkThind
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPowClassNumber
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdStdBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuRowSuccEqWt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.LvT.Built.KMap

set_option maxHeartbeats 1000000 in

theorem jetC_th_mem_Qbar : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ)
    (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ColIn.JetsIn I →
    ∀ u μ i, i < B.R.m → ∀ (c : ((I.rec7 l Z).chTw u μ).cls i) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1))
      (m : DVar (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) →₀ ℕ),
      (∀ τ, ∑ β, ∑ α, m (τ, β, α) = ∑ r, nuT (I.rec7 l Z) u i τ r) → jetC (O u μ).dgen ((O u μ).Th i c c') m ∈ Qbar := by
  classical
  intro B X I hOk hPins l Z Qp O hO hJ u μ i hi c c' m hm
  rw [hO.dgen, hO.Th]
  have hdeg : ∀ τ, (monoDeg m τ : ℤ) = nuDeg B u i τ := by
    intro τ
    rw [monoDeg_eq_sum, hm τ, Nat.cast_sum]
    unfold nuDeg
    refine Finset.sum_congr rfl fun r _ => ?_
    have e1 : ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℝ) = DV.nuRow (I.rec7 l Z) u (i + 1) τ r := (nu_t_identity (I.rec7 l Z) u i hi τ r).1
    have e2 := GlobalTheory.ColPeriod.nuRow_succ_eq_wt (I.rec7 l Z) u i hi τ r r.2
    have e3 := B.wts.nuW_eq u hi τ r
    have e4 := lamOf_wtN (B.wts.hc u τ) hi.le r
    have key : (((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) : ℝ) = (((B.wts.nuW u (i + 1) τ).w r : ℤ) : ℝ) := by
      rw [Int.cast_natCast, e1, e2, ← Rat.cast_intCast, e3]
      unfold Wts.lamN at e3 ⊢
      rw [e4]
      rfl
    exact_mod_cast key
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := GlobalTheory.T.trueColumn_periodLattice_vacuumSmooth I hOk hPins l Z μ u i hi
  set p := (I.stp u μ i).rep c
  set p' := (I.stp u μ (i + 1)).rep c'
  have hN : IsSdLat p.1.1.deco.1.N := ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩
  have hN' : IsSdLat p'.1.1.deco.1.N := ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) :=
    pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB : 0 < cBof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) u := GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup μ) (I.cst μ) (I.idx μ) _ _ u i hX hPr
    hOk.sel_ok (hOk.T_mem u) hOk.g_mem (hOk.idx_ok μ) hi ⟨_, _, _, _, hOk.ch_tied⟩ c.1 c'.1 p p'
  set N := p.1.1.deco.1.N
  set N' := p'.1.1.deco.1.N
  set cA := cAof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ)
  set cB := cBof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) u
  set Ξ := xiAt (Pr := B.primes X) I.Ch I.sel (I.tup μ) (I.cst μ) (I.idx μ) u i c.1 c'.1 p p'
  have hth := GlobalTheory.latSum_thInd_eq_thC B.fields I.A _ _ (I.Sb μ u) N N' cA cB (fun x => I.A.σ₀ (Ξ x))
    (indTieD_of_la I.A _ _ _ _ (Nat.mul_pos hA hB) hLa) hN hN' hA hB (volC_pos_of_laHyp I.A _ _ _ hLa hN hN')
    (GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ _ _ _ _ _ hN.1 hN'.1 hA hB) (fun x hx => hbox.1 x ((map_ne_zero _).1 hx))
    (fun x y hy => congrArg I.A.σ₀ (hbox.2 x y hy))
  have hfin := GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ (I.Sb μ u) N N' cA cB hN.1 hN'.1 hA hB
  let _ := @Fintype.ofFinite _ hfin
  rw [show I.th u μ i c.1 c'.1 p p' = fun z => _ from funext fun z => (hth z).symm]
  unfold latSum
  simp only [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((Formalism.L2.Col.mulLat cB (homAt (I.Sb μ u) N N')).comap (divLat cA (homAt (I.Sb μ u) N N')).subtype))
  have hs : ∀ q (k : ℕ), ContDiff ℂ k (I.A.thInd (I.Sb μ u) N N' cB (r q)) := fun q =>
    indSmooth_of I.A _ _ (I.Sb μ u) (cA * cB) hE N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩
  rw [show I.J.cD = I.A.cD from rfl]
  have hsum := jetC_sum I.A.cD (fun q => I.A.σ₀ (Ξ (r q))) (fun q => I.A.thInd (I.Sb μ u) N N' cB (r q)) hs m
  have hchi : ∀ 𝔞, I.chi 𝔞 ≠ 0 := fun 𝔞 => by
    unfold ColIn.chi chiId
    exact Units.ne_zero _
  have hF0 : I.A.chiF _ _ N N' ≠ 0 := by
    show Th.chiFac B.host I.chi _ _ N N' ≠ 0
    unfold Th.chiFac
    exact mul_ne_zero (zpow_ne_zero _ (hchi _)) (zpow_ne_zero _ (hchi _))
  have hF : I.A.chiF _ _ N N' ∈ B.embLL.fieldRange := by
    show Th.chiFac B.host I.chi _ _ N N' ∈ B.embLL.fieldRange
    unfold Th.chiFac
    have hv := (GlobalTheory.Mem.ChiVal.chi_values B X I hOk).2
    exact mul_mem (zpow_mem (hv _) _) (zpow_mem (hv _) _)
  have hmem : (∑ q, I.A.σ₀ (Ξ (r q)) * jetC I.A.cD (I.A.thInd (I.Sb μ u) N N' cB (r q)) m) ∈ B.embLL.fieldRange := by
    refine Subfield.sum_mem _ fun q _ => Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) ?_
    obtain ⟨y, hy⟩ := hJ.exists_eq (a := μ) (u := u) (N := N) (N' := N') (c := cB) (x := (r q).1) (e := m) hi
      ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩ hdeg
    rw [← mul_inv_cancel_left₀ hF0 (jetC I.A.cD (I.A.thInd (I.Sb μ u) N N' cB (r q)) m)]
    exact Subfield.mul_mem _ hF ⟨y, hy⟩
  have hQ : ∀ x ∈ B.embLL.fieldRange, x ∈ Qbar := by
    rintro _ ⟨y, rfl⟩
    exact mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) y).algHom B.embLL.toRatAlgHom)
  show jetC I.A.cD (fun z => ∑ q, I.A.σ₀ (Ξ (r q)) * I.A.thInd (I.Sb μ u) N N' cB (r q) z) m ∈ Qbar
  rw [hsum]
  exact hQ _ hmem

end GlobalTheory.Mem.Col2.TC

end
