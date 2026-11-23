import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HalfLatticeTypes
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants Formalism.HN
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
open Formalism.L2.Pj hiding kap
open GlobalTheory.CompHt hiding rhoB

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P) {T : Par D} {j : ℕ} {l : Level T.H}
  {Xo : Moduli (T.Dw j) l} {c : Coeff l} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
  (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r)

abbrev gKap (T : Par D) (j : ℕ) : WTZ D.host.E := thetaExp D (T.Dw j) (kap D j)

abbrev gKapMinus (T : Par D) (j : ℕ) : WTZ D.host.E := thetaExp D (T.Dw j) (kapMinus D j)

abbrev gTw (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (twW D j)

abbrev gMinus (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (uMinus D j)

abbrev gOne (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (uOne Q j)

abbrev gTop (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (uTop Q j)

abbrev nrmAt (G : WTZ D.host.E) : (c.F →+* ℂ) → cuspW Xo c U G → ℝ := normW U (xiR D) (fun _ => D.sp.W j) dict G

abbrev GoodAt (G : WTZ D.host.E) : Prop := GoodW U (xiR D) (fun _ => D.sp.W j) dict G

def refConst : ℝ := 1 / 2500

def ccOf : ℝ := (refSum U refConst (gOne Q T j)).toReal + aSum Q j + cInf Q j

theorem comp_nonempty (h : T.Pins) (hj : InR D j) : Nonempty (Comp Xo c) :=
  (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Xo c (by
    rw [(sig_eq h hj).2.2]
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega)).1

variable [StarRing c.F] (h : T.Pins) (hj : InR D j) (CI C2 : ℝ) (Vs : ValFam Xo c) (Hb : Type) [Fintype Hb]
  (NN : Submodule (𝓞 c.F) (cuspW Xo c U (gKap T j)))
  (Ph : cuspW Xo c U (gKapMinus T j) →ₗ[c.F] (Hb → cuspW Xo c U (gKap T j)))
  (e : cuspW Xo c U (gKap T j) →ₗ[c.F] cuspW Xo c U (gKap T j)) (g : ℕ)

def facWith : SlopeBoundLiftData c.F (pageOf Q) where
  w τ := wAn D j τ
  w0 τ := wj D j τ
  c1 τ := GlobalTheory.FlatLine.c1 U (xiR D) (psiOf h.1 τ)
  ua τ := nrm D (uAn D j τ)
  kap := nKap D j
  q' := qq D j
  pq := (pp D j : ℝ) - qq D j
  ι := Comp Xo c
  fι := haveI := CompFin.finite_comp Xo c; Fintype.ofFinite _
  nι := comp_nonempty h hj
  DY := dY D
  A := cA Q j
  cs := cStarInf U (xiR D) (fun _ => D.sp.W j) dict (gOne Q T j)
  X := CI * placeRankTwoOne.LL0 D L * nPrW Q j
  cc := ccOf Q U
  E0 := eZero D j
  Qcc := (numAt Q j).Qc
  ρ := rhoB Q j
  R1 := rOne Q C2 j
  R2 := rTwo Q j
  Bn := ((tN Q - 1).choose (placeRankTwoOne.dimY D) : ℕ)
  δ' := compMean fun Z => delPrime U Z (toWt (T.Dw j) (uOne Q j))
  h Z := compHeight U (xiR D) (fun _ => D.sp.W j) dict Z (gOne Q T j)
  sl Z := (compVolSlope U (xiR D) 8 Vs Z (toWt (T.Dw j) (uPr Q j))).toReal
  δc Z := compDeg U Z (gOne Q T j)
  dc Z := rankOn U Z (gTop Q T j)
  degc Z := degOn U (xiR D) (fun _ => D.sp.W j) dict Z (gTop Q T j)
  PPf := (numAt Q j).Pfl
  mv := shift D
  muU := slopeW_sq U (xiR D) (fun _ => D.sp.W j) dict (gMinus T j)
  nA := cDim (nrmAt U dict (gKapMinus T j))
  nB := cDim (piNorm Hb (nrmAt U dict (gKap T j)))
  nN := cDim (nrmAt U dict (gKap T j))
  XA := frameCo _
  XB := frameCo _
  XN := frameCo _
  LA := latCo _ (latW U (gKapMinus T j))
  LB := latCo _ (piLat Hb NN)
  NN := latCo _ NN
  Mk := latCo _ (latW U (gKap T j))
  φ := mapCo _ _ Ph
  e := mapCo _ _ e
  g := g
  PPh := 3 / 2 * Real.log (Fintype.card Hb) + (numAt Q j).U0
  abelian₂ := lamKap Q j + Real.log (Fintype.card Hb)
  δ := del D
  o' := GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.ringCost c.F
  n2 := measureMove D L

local notation "𝐅" => facWith Q U dict h hj CI C2 Vs Hb NN Ph e g

theorem facWith_T : (𝐅).T = tR Q := T_eq Q _ rfl

theorem facWith_z : (𝐅).z = zed Q j := by rw [SlopeBoundLiftData.z, facWith_T]; rfl

theorem facWith_eps : (𝐅).ε = epsR Q j := by rw [SlopeBoundLiftData.ε, facWith_T]; rfl

theorem facWith_U : (𝐅).U = nU D j := rfl

theorem facWith_A : (𝐅).A = 26 * (26 * (𝐅).DY ^ 2 + 2 * (𝐅).z * (𝐅).T) := by rw [facWith_z, facWith_T]; rfl

theorem facWith_main : (𝐅).main = ∑ τ, ((pp D j : ℝ) - qq D j) * wj D j τ * L.logOm := rfl

theorem facWith_DY : (𝐅).DY = dimFlag (T.Dw j) := by rw [dimFlag_eq h hj]; rfl

theorem facWith_rho : (𝐅).ρ = GlobalTheory.CompHt.rhoB (T.Dw j) (toWt (T.Dw j) (uOne Q j)) := (rhoB_toWt Q h hj).symm

theorem facWith_delPrime (hv : ∀ Z Z' : Comp Xo c, vZero U Z = vZero U Z') (Z : Comp Xo c) :
    (𝐅).δ' = delPrime U Z (toWt (T.Dw j) (uOne Q j)) :=
  compMean_eq (fun Z Z' => by rw [delPrime, delPrime, topDeg, topDeg, hv Z Z']) Z

theorem facWith_sig : ((𝐅).q' : ℝ) + 1 ≤ (pageOf Q).m ∧
    (𝐅).pq = (pageOf Q).k + (pageOf Q).m - 1 - 2 * ((𝐅).q' : ℝ) := by
  have h1 := hj.1
  have h2 := hj.2
  have h3 := D.R.m_add_three_le_k
  have a : qq D j + 1 ≤ D.R.m := by simp only [qq, Ranks.sigW]; omega
  have b : pp D j + qq D j + 1 = D.R.k + D.R.m := by simp only [pp, qq, Ranks.sigW]; omega
  have b' : (pp D j : ℝ) + qq D j + 1 = D.R.k + D.R.m := by exact_mod_cast b
  refine ⟨by show (qq D j : ℝ) + 1 ≤ (D.R.m : ℝ); exact_mod_cast a, ?_⟩
  show (pp D j : ℝ) - qq D j = (D.R.k : ℝ) + D.R.m - 1 - 2 * (qq D j : ℝ)
  linarith

theorem facWith_q : (𝐅).q' = D.R.m - j := rfl

theorem facWith_cs_nonneg : 0 ≤ (𝐅).cs := cStarInf_nonneg

variable {U dict}

theorem facWith_muA (hG : GoodAt U dict (gKapMinus T j)) :
    (𝐅).muA = slopeW_sq U (xiR D) (fun _ => D.sp.W j) dict (gKapMinus T j) := muDef_latCo hG.1 hG.2.1

theorem facWith_muN (hG : HasGram (nrmAt U dict (gKap T j))) (hN : NN.FG) :
    (𝐅).muN = slope_sq (nrmAt U dict (gKap T j)) NN := muDef_latCo hG hN

theorem facWith_mmax (hG : GoodAt U dict (gKap T j)) (h0 : latW U (gKap T j) ≠ ⊥) :
    (𝐅).mmax = slopeMax_sq (nrmAt U dict (gKap T j)) (latW U (gKap T j)) := muMaxDef_latCo hG.1 hG.2.1 h0

theorem facWith_good (hG : HasGram (nrmAt U dict (gKap T j))) :
    (𝐅).good = latCo (nrmAt U dict (gKap T j)) (NN ⊓ (LinearMap.range e).restrictScalars (𝓞 c.F)) := by
  rw [latCo_inf hG, ← range_mapCo hG]; rfl

theorem facWith_bad (hG : HasGram (nrmAt U dict (gKap T j))) :
    (𝐅).bad = latCo (nrmAt U dict (gKap T j)) (NN ⊓ (LinearMap.ker e).restrictScalars (𝓞 c.F)) := by
  rw [latCo_inf hG, ← ker_mapCo hG]; rfl

theorem facWith_muG (hG : HasGram (nrmAt U dict (gKap T j)))
    (hN : (NN ⊓ (LinearMap.range e).restrictScalars (𝓞 c.F)).FG) :
    (𝐅).muG = slope_sq (nrmAt U dict (gKap T j)) (NN ⊓ (LinearMap.range e).restrictScalars (𝓞 c.F)) := by
  rw [SlopeBoundLiftData.muG, facWith_good Q h hj CI C2 Vs Hb NN Ph e g hG]; exact muDef_latCo hG hN

theorem facWith_rk (hG : HasGram (nrmAt U dict (gKap T j))) : rkK (𝐅).NN = rkK NN ∧
    rkK (𝐅).bad = rkK (NN ⊓ (LinearMap.ker e).restrictScalars (𝓞 c.F)) ∧ rkK (𝐅).LB = rkK (piLat Hb NN) :=
  ⟨rkK_latCo hG _, by rw [facWith_bad Q h hj CI C2 Vs Hb NN Ph e g hG]; exact rkK_latCo hG _, rkK_latCo (hasGram_piNorm Hb hG) _⟩

theorem facWith_rkA (hG : HasGram (nrmAt U dict (gKapMinus T j))) : rkK (𝐅).LA = rankW U (gKapMinus T j) :=
  rkK_latCo hG _

example (hF : GlobalTheory.FlatLine.FlatDegree U (xiR D) L.logOm) (τ : D.what₂.Tau) :
    (𝐅).c1 τ = -GlobalTheory.FlatLine.flatDegVal (T.Dw j) L.logOm :=
  GlobalTheory.FlatLine.FlatExistsAt.c1_eq hF (comp_nonempty h hj) _

end GlobalTheory.SlopeRec
