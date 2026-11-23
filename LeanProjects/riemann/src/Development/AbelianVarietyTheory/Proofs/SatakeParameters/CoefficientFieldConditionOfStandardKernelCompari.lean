import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueKernelJetsMulDetCharactersMemCoefficientFielStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdStdBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuRowSuccEqWt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Pdv

private theorem nuT_cast_eq_nuW {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : B.fields.Tau) (r : Fin (B.R.N i)) :
    ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) = (B.wts.nuW u (i + 1) τ).w r := by

  have hq : ((B.wts.nuW u (i + 1) τ).w r : ℚ) = Examples₂.wtN (B.hcW u τ) r.1 + wG B.R ((B.hcW u τ).e ⟨i, hi⟩) (i + 1) := by
    rw [Formalism.L2.Col.Wts.nuW_eq _ u hi τ r]
    rw [show B.wts.lamN u i τ = Examples₂.lamOf (B.hcW u τ) i from rfl, Formalism.L2.Col.lamOf_wtN _ hi.le r]

  have hrow : DV.nuRow (I.rec7 l Z) u (i + 1) τ r = (((B.wts.nuW u (i + 1) τ).w r : ℤ) : ℝ) := by
    rw [GlobalTheory.ColPeriod.nuRow_succ_eq_wt (I.rec7 l Z) u i hi τ r r.2]
    have h := congrArg (fun x : ℚ => (x : ℝ)) hq.symm
    simp only [Rat.cast_intCast] at h
    exact h

  have hnn : 0 ≤ (B.wts.nuW u (i + 1) τ).w r := by
    have h1 := Formalism.L2.Ker.natW_cast (B.wts.nuW u (i + 1) τ) r
    have h2 := GlobalTheory.MoveCompare.nuW_detShift_nonneg B.wts u hi τ
    omega
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
  show ((⌊DV.nuRow (I.rec7 l Z) u (i + 1) τ r⌋₊ : ℕ) : ℤ) = _
  rw [hrow, hn, Int.cast_natCast, Nat.floor_natCast]

private theorem monoDeg_eq_nuDeg_of_degAt_eq_sum_nuT {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : B.fields.Tau)
    (m : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ)
    (hm : degAt m τ = ∑ r, nuT (I.rec7 l Z) u i τ r) : (monoDeg m τ : ℤ) = nuDeg B u i τ := by
  have h3 : ((∑ r, nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) = nuDeg B u i τ := by
    push_cast
    exact Finset.sum_congr rfl fun r _ => nuT_cast_eq_nuW I l Z u hi τ r
  exact (congrArg (Nat.cast : ℕ → ℤ) hm).trans h3

set_option maxHeartbeats 800000 in

theorem rk_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → t.RK := by
  intro B X I hok hpins l Z L hT Gi Gl K Y cX ex t hJ hS u μ hμ i hi c c' m hm
  rw [hS.O.dgen u μ, hS.O.Th u μ i c c']
  exact GlobalTheory.T.trueKernelJets_mul_detCharacters_mem_coefficientField I hok hpins l Z hJ u μ i hi c c' m fun τ => monoDeg_eq_nuDeg_of_degAt_eq_sum_nuT I l Z u hi τ m (hm τ)

set_option maxHeartbeats 800000 in

theorem rk_of_stdTie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKerTie l Z t → t.RK := by
  intro B X I hok hpins l Z L hT Gi Gl K Y cX ex t hJ hS u μ hμ i hi c c' m hm
  rw [hS.O.dgen u μ, hS.O.Th u μ i c c']
  exact GlobalTheory.T.trueKernelJets_mul_detCharacters_mem_coefficientField I hok hpins l Z hJ u μ i hi c c' m fun τ => monoDeg_eq_nuDeg_of_degAt_eq_sum_nuT I l Z u hi τ m (hm τ)

end GlobalTheory.Pdv

end
