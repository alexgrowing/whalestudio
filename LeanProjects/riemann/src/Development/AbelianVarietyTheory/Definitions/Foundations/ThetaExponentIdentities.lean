import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DescentConstants
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AMiEqAMinusQ
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

def zetaLogDeriv {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : ℝ :=
  (logDeriv (fun s => riemannZeta s * DirichletCharacter.LFunction χ s) 0).re

def maxLift (D : D7) (g : ℕ → ℝ) : ℝ :=
  (Icc 1 D.R.m).sup' ⟨1, mem_Icc.2 ⟨le_rfl, le_trans one_le_two D.R.two_le_m⟩⟩ g

theorem le_maxLift {D : D7} (g : ℕ → ℝ) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : g j ≤ maxLift D g :=
  le_sup' g (mem_Icc.2 ⟨h1, h2⟩)

theorem maxLift_le_iff {D : D7} {g : ℕ → ℝ} {a : ℝ} : maxLift D g ≤ a ↔ ∀ j, 1 ≤ j → j ≤ D.R.m → g j ≤ a := by
  refine (sup'_le_iff _ _).trans ?_
  simp only [mem_Icc, and_imp]

theorem exists_eq_maxLift (D : D7) (g : ℕ → ℝ) : ∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ maxLift D g = g j := by
  obtain ⟨j, hj, h⟩ := exists_mem_eq_sup' (s := Icc 1 D.R.m)
    ⟨1, mem_Icc.2 ⟨le_rfl, le_trans one_le_two D.R.two_le_m⟩⟩ g
  exact ⟨j, (mem_Icc.1 hj).1, (mem_Icc.1 hj).2, h⟩

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

def pageOf : SlopeBoundParameters where
  Pl := D.what₂.Tau
  fPl := inferInstance
  x := L.sc.x
  eps := L.sc.eps
  rd := D.host.rdE
  v := D.host.v
  dN := D.host.d
  dimNeZero := ⟨D.host.hyp.2.1.ne_zero⟩
  χ := chiK D
  Z := haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩; zetaLogDeriv (chiK D)
  logOmK := eulerConstantTerm D.host.d
  logOm := L.logOm
  f := D.R.f
  m := D.R.m
  k := D.R.k
  S := L.Sc
  η := L.etaSz
  R := (D.R.r : ℝ) / 2
  PPp := maxLift D fun j => (numAt Q j).PPp
  PPpp := maxLift D fun j => (numAt Q j).PPpp
  PP := Q.PP
  PPT := Real.sqrt (ppTsq Q)
  Zpg := zBase L
  nV := D.R.nV
  Nr := D.R.r
  g12 := (D.host.g 0 : ℝ) * D.host.g 1

theorem pageOf_L : (pageOf Q).L = L.sc.L := rfl

theorem pageOf_b : (pageOf Q).b = L.sc.b := rfl

theorem pageOf_lrd : (pageOf Q).lrd = lrd D := rfl

theorem pageOf_Lc : (pageOf Q).Lc = L.logDerivativeAtOne := L.logDerivative_at_one_eq.symm

theorem log_derivative_at_zero : (pageOf Q).L0 = dlogL D 0 := rfl

theorem pageOf_LL0_eq_placeRankTwoOne_LL0 : (pageOf Q).LL0 = placeRankTwoOne.LL0 D L := by
  rw [SlopeBoundParameters.LL0, pageOf_Lc]; rfl

theorem ppTsq_nonneg : 0 ≤ ppTsq Q := le_max_of_le_left (by positivity)

theorem pageOf_PPT_sq : (pageOf Q).PPT ^ 2 = ppTsq Q := Real.sq_sqrt (ppTsq_nonneg Q)

theorem T_eq {K : Type} [Field K] [NumberField K] [StarRing K] (F : SlopeBoundLiftData K (pageOf Q)) (h : F.DY = dY D) :
    F.T = tR Q := by
  rw [SlopeBoundLiftData.T, pageOf_PPT_sq, h, tR, tN, ← Int.cast_natCast, Int.natCast_ceil_eq_ceil]
  · rfl
  · have := ppTsq_nonneg Q
    positivity

theorem PPp_le {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : (numAt Q j).PPp ≤ (pageOf Q).PPp :=
  le_maxLift (fun j => (numAt Q j).PPp) h1 h2

theorem PPpp_le {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : (numAt Q j).PPpp ≤ (pageOf Q).PPpp :=
  le_maxLift (fun j => (numAt Q j).PPpp) h1 h2

theorem leafDiff_pageOf : LeafDiff (pageOf Q) := rfl

example : 2 * (pageOf Q).v = (pageOf Q).rd ∧ (Fintype.card (pageOf Q).Pl : ℝ) = (pageOf Q).f :=
  ⟨by show 2 * (D.host.rdE / 2) = D.host.rdE; ring, congrArg Nat.cast D.what₂.card_Tau⟩

section Weights

variable (D) in

def uMinus (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uAn D j τ i - (cTw D j : ℤ) * deW D j i

variable (D) in

def kapMinus (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := kap D j τ i - (cTw D j : ℤ) * deW D j i

variable (D) in

def twW (j : ℕ) (_ : D.what₂.Tau) (i : ℕ) : ℤ := (cTw D j : ℤ) * deW D j i

def remW (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ :=
  aW D j τ i - aW D j τ (D.R.k - 2) - ((tN Q + placeRankTwoOne.dimY D + 1 : ℕ) : ℤ) * uOne Q j τ i

def uTwo (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uOne Q j τ i + remW Q j τ i

def uCan (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := canW D j i + uTwo Q j τ i + (placeRankTwoOne.dimY D : ℤ) * uOne Q j τ i

def uTop (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uCan Q j τ i + (tN Q : ℤ) * uOne Q j τ i

theorem kapMinus_add_twW (j : ℕ) : kapMinus D j + twW D j = kap D j := by
  funext τ i; simp [kapMinus, twW]

theorem kapMinus_eq (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : kapMinus D j τ i = uMinus D j τ i + wAn D j τ := by
  simp only [kapMinus, uMinus, uAn]; ring

theorem remW_anchor (j : ℕ) (τ : D.what₂.Tau) : remW Q j τ (D.R.k - 2) = 0 := by
  simp [remW, uOne_anchor]

theorem uOne_gap (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : uOne Q j τ i - uOne Q j τ (i + 1) = gapOne Q j τ i := by
  unfold uOne
  rcases lt_or_ge i (D.R.k - 2) with h | h
  · rw [sum_eq_sum_Ico_succ_bot h, Ico_eq_empty_of_le h.le, Ico_eq_empty_of_le (Nat.succ_le_of_lt h)]; simp
  · rw [Ico_eq_empty_of_le h, Ico_eq_empty_of_le (h.trans (Nat.le_succ i)), sum_Ico_succ_top h]; simp

theorem remW_gap (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) :
    0 ≤ remW Q j τ i - remW Q j τ (i + 1) ∧ remW Q j τ i - remW Q j τ (i + 1) ≤ tN Q + placeRankTwoOne.dimY D := by
  have hp : (0 : ℤ) < ((tN Q + placeRankTwoOne.dimY D + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos _
  have e : remW Q j τ i - remW Q j τ (i + 1) =
      (aW D j τ i - aW D j τ (i + 1)) % ((tN Q + placeRankTwoOne.dimY D + 1 : ℕ) : ℤ) := by
    have h := uOne_gap Q j τ i
    rw [gapOne] at h
    rw [Int.emod_def, ← h, remW, remW]; ring
  rw [e]
  have h2 := Int.emod_lt_of_pos (aW D j τ i - aW D j τ (i + 1)) hp
  exact ⟨Int.emod_nonneg _ hp.ne', by push_cast at h2 ⊢; omega⟩

theorem uTop_eq (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : uTop Q j τ i = uMinus D j τ i - aW D j τ (D.R.k - 2) := by
  simp only [uTop, uCan, uTwo, remW, uMinus, aW]; push_cast; ring

theorem aW_anchor {j : ℕ} (h1 : 1 ≤ j) (τ : D.what₂.Tau) : aW D j τ (D.R.k - 2) = -canW D j (D.R.k - 2) := by
  have h : D.R.k - 2 < pp D j := by
    have := D.R.m_add_three_le_k
    simp only [pp, Ranks.sigW]; omega
  simp [aW, uAn_anchor, deW, h]

end Weights

section Numbers

def nOneW (j : ℕ) : ℝ := ∑ τ, nrm D (uOne Q j τ)

def nPrW (j : ℕ) : ℝ := ∑ τ, nrm D (uPr Q j τ)

def supPrW (j : ℕ) : ℕ := univ.sup fun τ : D.what₂.Tau => (range D.R.r).sup fun i => (uPr Q j τ i).natAbs

def bZero (j : ℕ) : ℝ := 4 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (1 + (supPrW Q j : ℝ) / (LevelStarExponents.h0 L / (4 * tR Q)))

variable (D L) in

def badPrimes (B : ℝ) : Finset ℕ :=
  (range (⌊B⌋₊ + 1)).filter Nat.Prime ∪ (2 * (discr D.host.E).natAbs * levDeep D L).primeFactors

variable (D) in

def diff_vp (p : ℕ) : ℝ := (padicValNat p (discr D.host.E).natAbs : ℝ) / (Module.finrank ℚ D.host.E : ℝ)

def aSum (j : ℕ) : ℝ :=
  ∑ p ∈ badPrimes D L (bZero Q j), (1 / ((p : ℝ) - 1) + 40 * diff_vp D p) * (nPrW Q j + (numAt Q j).Pa) * Real.log p

def cInf (j : ℕ) : ℝ := (nOneW Q j + 6 * (numAt Q j).Pinf) / 2

def cA (j : ℕ) : ℝ := 26 * (26 * dY D ^ 2 + 2 * zed Q j * tR Q)

def lZero (j : ℕ) : ℝ := (numAt Q j).PPp * (nKap D j / tR Q + 1) + (numAt Q j).al

def cJ (C2 : ℝ) (j : ℕ) : ℝ :=
  dY D * (numAt Q j).PPp * (nKap D j / tR Q + 1) + tR Q * ((numAt Q j).QJ + (numAt Q j).PPp) +
    (dY D + 3) * addY C2 (pageOf Q) / tR Q

def cG (j : ℕ) : ℝ := (dY D + 1) * ((numAt Q j).o + (numAt Q j).B7 + 1) / 2 + 1

def rOne (C2 : ℝ) (j : ℕ) : ℝ :=
  cJ Q C2 j + 26 * dY D ^ 2 * (lZero Q j + Real.log (tR Q)) + (tR Q + dY D + 1) * (numAt Q j).Bt +
    (tR Q + dY D ^ 2) * (cG Q j + 2)

def rTwo (j : ℕ) : ℝ :=
  tR Q * (Real.log 2 + lZero Q j + (numAt Q j).Bt / 2) + 2 * ((numAt Q j).PPp * nKap D j)

def lamKap (j : ℕ) : ℝ := (numAt Q j).G * (nKap D j - (D.R.f : ℝ) * D.R.r * D.R.nV / 2 + D.R.nV)

variable (D L) in

def measureMove : ℝ := 61 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L

example (B : ℝ) (h : levDeep D L ≠ 0) : 2 ∈ badPrimes D L B :=
  mem_union_right _ (Nat.mem_primeFactors.2 ⟨Nat.prime_two, Dvd.intro _ (mul_assoc _ _ _).symm,
    mul_ne_zero (mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.2 (discr_ne_zero _))) h⟩)

end Numbers

section Transport

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt
open Formalism.L2.Pj hiding kap

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

open Classical in

def toWt (Dw : Datum H) (v : D.what₂.Tau → ℕ → ℤ) : Weight Dw :=
  fun τ i => ∑ t, if τ.1 = DV.tauEmb D t then v t i else 0

variable {Dw : Datum H}

theorem toWt_apply (v : D.what₂.Tau → ℕ → ℤ) {τ : Psi H} {t : D.what₂.Tau} (h : τ.1 = DV.tauEmb D t)
    (i : Fin (Dw.p + Dw.q)) : toWt Dw v τ i = v t i := by
  rw [toWt, sum_eq_single t (fun s _ hs => if_neg fun e => hs ?_) (by simp), if_pos h]
  exact GlobalTheory.WeightExponents.tauEmb_injective D (e.symm.trans h)

theorem toWt_add (v v' : D.what₂.Tau → ℕ → ℤ) : toWt Dw (v + v') = toWt Dw v + toWt Dw v' := by
  funext τ i
  simp only [toWt, Pi.add_apply, ← sum_add_distrib]
  exact sum_congr rfl fun t _ => by split_ifs <;> simp

theorem toWt_smul (n : ℤ) (v : D.what₂.Tau → ℕ → ℤ) : toWt Dw (n • v) = n • toWt Dw v := by
  funext τ i
  simp only [toWt, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun t _ => by split_ifs <;> simp

def psiOf {T : Par D} (h : T.PinHost) (t : D.what₂.Tau) : Psi T.H := ⟨DV.tauEmb D t, h.2.2.2 t⟩

theorem psiOf_bijective {T : Par D} (h : T.Pins) : Function.Bijective (psiOf h.1) := by
  have hj : InR D 1 := ⟨le_rfl, le_trans one_le_two D.R.two_le_m⟩
  refine ⟨fun s t e => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val e), fun τ => ?_⟩
  obtain ⟨t, ht⟩ := ((GlobalTheory.WeightExponents.weight_exponents D T h 1 hj
    (WeightAlgebra.wscalar D 1 0 Even.zero)).2.2.1 τ.1).1 τ.2
  exact ⟨t, Subtype.ext ht.symm⟩

theorem toWt_psiOf {T : Par D} (h : T.PinHost) {Dw : Datum T.H} (v : D.what₂.Tau → ℕ → ℤ) (t : D.what₂.Tau)
    (i : Fin (Dw.p + Dw.q)) : toWt Dw v (psiOf h t) i = v t i := toWt_apply v rfl i

variable {T : Par D} {j : ℕ}

theorem sig_eq (h : T.Pins) (hj : InR D j) :
    (T.Dw j).p = pp D j ∧ (T.Dw j).q = qq D j ∧ (T.Dw j).p + (T.Dw j).q = D.R.r := by
  obtain ⟨h1, h2, -⟩ := h.2.2.2 j hj
  refine ⟨h1, h2, ?_⟩
  have := D.R.m_add_three_le_k
  have := hj.1
  have := hj.2
  rw [h1, h2]
  simp only [Ranks.sigW, Ranks.r]; omega

theorem dimFlag_eq (h : T.Pins) (hj : InR D j) : dimFlag (T.Dw j) = placeRankTwoOne.dimY D := by
  rw [dimFlag, Formalism.DegreeFormula.dimFl, (sig_eq h hj).2.2, ← Fintype.card_of_bijective (psiOf_bijective h), D.what₂.card_Tau,
    placeRankTwoOne.dimY, Nat.choose_two_right]

theorem toWt_deW (h : T.Pins) (hj : InR D j) : toWt (T.Dw j) (fun _ => deW D j) = hodgeWt (T.Dw j) := by
  funext τ i
  obtain ⟨t, rfl⟩ := (psiOf_bijective h).2 τ
  rw [toWt_psiOf, hodgeWt, barWt, deW, ← (sig_eq h hj).1]

theorem toWt_uPr (h : T.Pins) (hj : InR D j) : toWt (T.Dw j) (uPr Q j) = uPrime (T.Dw j) (toWt (T.Dw j) (uOne Q j)) := by
  funext τ i
  rw [uPrime, ← toWt_deW h hj]
  obtain ⟨t, rfl⟩ := (psiOf_bijective h).2 τ
  simp only [Pi.sub_apply, Pi.smul_apply, toWt_psiOf, uPr, smul_eq_mul, (sig_eq h hj).2.2]

theorem vdm_toWt (h : T.Pins) (hj : InR D j) (v : D.what₂.Tau → ℕ → ℤ) : ((vdm (toWt (T.Dw j) v) : ℤ) : ℝ) = GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants.degW D v := by
  rw [vdm, GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants.degW, ← (psiOf_bijective h).prod_comp, Int.cast_prod]
  refine prod_congr rfl fun t _ => ?_
  simp only [toWt_psiOf]
  rw [← (sig_eq h hj).2.2]
  generalize (T.Dw j).p + (T.Dw j).q = N
  rw [prod_comm' (t' := univ) (s' := fun l => Iio l) (by simp), ← Fin.prod_univ_eq_prod_range
    (fun l => ∏ i ∈ range l, ((v t i : ℝ) - v t l)), Int.cast_prod]
  refine prod_congr rfl fun l _ => ?_
  rw [Int.cast_prod, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, prod_map]
  simp

theorem rhoB_toWt (h : T.Pins) (hj : InR D j) :
    GlobalTheory.CompHt.rhoB (T.Dw j) (toWt (T.Dw j) (uOne Q j)) = GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants.rhoB Q j := by
  rw [GlobalTheory.CompHt.rhoB, rhoOf, ← toWt_uPr Q h hj, vdm_toWt h hj, vdm_toWt h hj, GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants.rhoB]

variable (D) in

def thetaExp (Dw : Datum H) (v : D.what₂.Tau → ℕ → ℤ) : WTZ D.host.E := wtOf Dw (toWt Dw v) ((D.R.nV / 2 : ℕ) : ℤ)

variable (D) in

def plainExp (Dw : Datum H) (v : D.what₂.Tau → ℕ → ℤ) : WTZ D.host.E := wtOf Dw (toWt Dw v) 0

theorem thetaExp_add (v v' : D.what₂.Tau → ℕ → ℤ) : thetaExp D Dw (v + v') = thetaExp D Dw v + plainExp D Dw v' := by
  rw [thetaExp, thetaExp, plainExp, ← wtOf_add, toWt_add, add_zero]

theorem thetaExp_kap (j : ℕ) : thetaExp D Dw (kapMinus D j) + plainExp D Dw (twW D j) = thetaExp D Dw (kap D j) := by
  rw [← thetaExp_add, kapMinus_add_twW]

theorem thetaExp_kap_eq (h : T.Pins) (hj : InR D j) (w : WeightFamilies.Wt D j) (hn : w.n = D.R.nV)
    (hw : Formalism.L2.Geo.wtOf w = DV.kapW D j) : thetaExp D (T.Dw j) (kap D j) = wtZ (wtA w) w.n := by
  obtain ⟨hp, hq, hr⟩ := sig_eq h hj
  obtain ⟨-, -, hΨ, hΨ', hA⟩ := GlobalTheory.WeightExponents.weight_exponents D T h j hj w
  have hp' : (T.Dw j).p = (D.R.sigW j).1 := hp
  have hq' : (T.Dw j).q = (D.R.sigW j).2 := hq
  refine Prod.ext (funext fun ⟨τ, i⟩ => ?_) ?_
  · show _ = ((wtA w (τ, i) : ℕ) : ℤ)
    by_cases hτ : InPsi T.H τ
    · obtain ⟨t, rfl⟩ := (hΨ τ).1 hτ
      rw [(hA t i).1, ext0]
      by_cases hi : i < (T.Dw j).p
      · refine (wtOf_big _ _ (psiOf h.1 t) i hi).trans ?_
        rw [toWt_psiOf, GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants.kap, dif_pos (by show i < _; omega), ← hw, dif_pos (by omega)]
        simp only [Formalism.L2.Geo.wtOf, Formalism.L2.Geo.wtOfN, hn]
        rw [dif_pos (by omega)]; ring
      · rw [dif_neg (by omega)]
        simp only [thetaExp, wtOf]
        unfold InPsi at hτ
        rw [dif_pos hτ, dif_neg hi]; rfl
    · obtain ⟨t, rfl⟩ := (hΨ' τ).1 hτ
      rw [(hA t i).2, ext0]
      by_cases hi : i < (T.Dw j).q
      · refine (wtOf_small _ _ (psiOf h.1 t) i hi).trans ?_
        rw [toWt_psiOf, GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants.kap, dif_pos (by show (T.Dw j).p + _ < _; omega), ← hw, dif_pos (by omega)]
        simp only [Formalism.L2.Geo.wtOf, Formalism.L2.Geo.wtOfN, hn]
        rw [dif_neg (by omega), dif_pos (by omega)]
        have e : ∀ (a : Fin (D.R.sigW j).2) (b : Fin (D.R.sigW j).2), (a : ℕ) + b + 1 = (D.R.sigW j).2 → Fin.rev a = b :=
          fun a b hab => Fin.ext (by rw [Fin.val_rev]; omega)
        rw [e _ ⟨i, by omega⟩ (by simp only; omega)]; ring
      · rw [dif_neg (by omega)]
        simp only [thetaExp, wtOf]
        unfold InPsi at hτ
        rw [dif_neg hτ]
        split_ifs <;> first | rfl | omega
  · obtain ⟨a, ha⟩ := w.n_even
    show 2 * ((D.R.nV / 2 : ℕ) : ℤ) = ((w.n : ℕ) : ℤ)
    omega

theorem thetaExp_kap_kapTop (h : T.Pins) (hK : DV.KapDef D) (i : Fin D.R.m) :
    thetaExp D (T.Dw ((i : ℕ) + 1)) (kap D ((i : ℕ) + 1)) =
      wtZ (wtA (Formalism.IndefR.FWT.kapTop D i)) (Formalism.IndefR.FWT.kapTop D i).n :=
  thetaExp_kap_eq h ⟨Nat.le_add_left _ _, i.2⟩ _ rfl (GlobalTheory.RecordWeightVec.wtOf_kapTop D hK i).2

end Transport

end GlobalTheory.SlopeRec
