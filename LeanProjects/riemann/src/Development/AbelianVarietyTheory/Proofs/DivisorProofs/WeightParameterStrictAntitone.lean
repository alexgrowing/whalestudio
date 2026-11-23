import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictAntiOfStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedWeightsDominantOfGapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BarGapParameterInequalityStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.QuoWt

theorem dominance : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (P : WtPar Dw),
    0 ≤ P.c₀ → 2 * (Dw.p + Dw.q) + CompHt.dimFlag Dw ≤ P.T →
    (∀ (τ : Psi H) (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 →
      ((b : ℕ) ≠ Dw.p → ((P.T : ℤ) + CompHt.dimFlag Dw + 2) * ((P.T : ℤ) + CompHt.dimFlag Dw + 2 + 2 * ((Dw.p + Dw.q : ℕ) : ℤ)) ≤
        P.u τ a - P.u τ b + 2) ∧
      ((b : ℕ) = Dw.p → ((P.T : ℤ) + P.c₀) * ((P.T : ℤ) + CompHt.dimFlag Dw + 1) + P.c₀ + 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 ≤
        P.u τ a - P.u τ b)) →
    ∀ s : ℕ, s ≤ 3 → ∀ τ : Psi H, Antitone (P.uMinus τ + (s * P.c₀) • hodgeWt Dw τ) ∧
      Antitone (((P.T + CompHt.dimFlag Dw + (if s = 0 then 3 else 4) : ℕ) : ℤ) • P.u₁ τ - (P.uMinus τ + (s * P.c₀) • hodgeWt Dw τ)) := GlobalTheory.T.shifted_weights_dominant_of_gaps

theorem arith : ∀ (T D c0 h0 N f m k PP : ℝ), 4 * D + 4 ≤ T → 4 * T ^ 2 ≤ h0 → PP * T * N * f ^ 2 * m ^ 2 * k * D ≤ h0 →
    4 * (c0 + 2 * N + T + D + 1) ≤ h0 → 0 ≤ c0 → c0 ≤ 22 * f ^ 2 * N ^ 4 → D = f * (N * (N - 1) / 2) → 40 ≤ PP →
    N + 4 ≤ 2 * k → 2 ≤ m → 6 ≤ N → 8 ≤ f →
    (T + c0) * (T + D + 1) + c0 + 2 * N - 2 ≤ h0 ∧ 2 * N + D ≤ T := GlobalTheory.T.bar_gap_parameter_inequality

theorem isQuot_u₁ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (P : WtPar Dw) (kc : ℕ) (hk : P.a + 1 = kc) : IsQuot Dw kc P.T P.c₀ P.u P.u₁ := by
  intro τ
  refine ⟨fun a (ha : (a : ℕ) + 1 = kc) => (P.anchored τ (by omega)).1, fun a b hb => ?_⟩
  have hb' : (a : ℕ) + 1 < Dw.p + Dw.q := hb ▸ b.2
  show P.u₁ τ a - P.u₁ τ b = (P.u τ a - P.u τ b + if (b : ℕ) = Dw.p then -P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) else 2) /
    ((P.T : ℤ) + CompHt.dimFlag Dw + 1)
  rw [← CompHS.gap_eq (P.u₁ τ) hb, P.gap_u₁ τ hb', P.gap_uMinus_sub_kap τ hb', CompHS.gap_eq (P.u τ) hb, hb,
    WtPar.T₁, dimFlag_eq]

theorem quo_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (P : WtPar Dw) (kc : ℕ) (hk : P.a + 1 = kc) (hN : kc ≤ Dw.p + Dw.q) (u1 : AllWt.Weight Dw)
    (hq : IsQuot Dw kc P.T P.c₀ P.u u1) : u1 = P.u₁ :=
  GlobalTheory.MeanTop.Inhab.dividedWeight_unique _ u1 (by show 1 ≤ kc; omega) hN (isQuot_u₁ Dw P kc hk) hq

section Pt

open IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem atPoint (PP A M : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ D.host.E / 2 ∧ (∀ u1, Quo p i PP u1 → u1 = (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) ∧ (∀ τ, StrictAnti ((⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ) ∧ StrictAnti (CompHt.uPrime (dat p i) (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ)) ∧ (∃ w : Psi p.T.Q.H → ℤ, (∀ τ, |w τ| ≤ 3 * (D.R.r : ℤ)) ∧ uM p i = (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP) + GlobalTheory.FlatLine.parWt (dat p i) w) ∧ ∀ s : ℕ, s ≤ 3 → ∀ τ, Antitone (uM p i τ + (s * cZero D ((i : ℕ) + 1)) • hodgeWt (dat p i) τ) ∧ Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + (if s = 0 then 3 else 4) : ℕ) : ℤ) • (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ - (uM p i τ + (s * cZero D ((i : ℕ) + 1)) • hodgeWt (dat p i) τ)) := by
  obtain ⟨⟨s1, s2, s3⟩, -, hdim, -, -, -, -, -, -, -, hyp⟩ := hw
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have ep : (dat p i).p = D.R.k + i := by rw [s1]; unfold Ranks.sigW; omega
  have eq : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [s2]; rfl
  have er : (dat p i).p + (dat p i).q = D.R.r := s3
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  set P : WtPar (dat p i) := ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ with hP
  have hPa : P.a + 1 = D.R.k - 1 := by show D.R.k - 2 + 1 = D.R.k - 1; omega
  have hquo : Quo p i PP P.u₁ := GlobalTheory.QuoWt.isQuot_u₁ (dat p i) P (D.R.k - 1) hPa
  obtain ⟨h0, S, eta, -, -, -, hT2, hrow, hH⟩ := hyp hi
  have hW := hH P.u₁
  have hdiv := (quo_iff p i PP h0 S eta P.u₁).1 hquo
  have ha : D.R.k - 2 < (dat p i).p + (dat p i).q := by omega
  refine ⟨by omega, by omega, ?_, fun u1 hu => GlobalTheory.QuoWt.quo_unique (dat p i) P _ hPa (by omega) u1 hu, fun τ => ?_, ?_, ?_⟩
  · have := hh.deg
    have := hh.f8
    omega
  · obtain ⟨a1, a2, -⟩ := GlobalTheory.MeanTop.divided_strictAnti _ _ _ hW hdiv τ
    refine ⟨a1, ?_⟩
    convert a2 using 1
    funext j
    simp only [CompHt.uPrime, hodgeWt, CompHt.barWt, GlobalTheory.MeanTop.Wts.u', wtsAt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : (j : ℕ) < (dat p i).p <;> simp [h] <;> ring
  · refine ⟨fun τ => -(FlagTan.kap (dat p i) τ ⟨D.R.k - 2, ha⟩), fun τ => ?_, ?_⟩
    · simp only [FlagTan.kap]
      rw [if_pos (by show D.R.k - 2 < (dat p i).p; omega), ep, eq, hr, abs_le]
      constructor <;> push_cast <;> omega
    · funext τ j
      have e := P.uMinus_eq τ (a := ⟨D.R.k - 2, ha⟩) rfl j
      have e1 : P.u τ ⟨D.R.k - 2, ha⟩ = 0 :=
        uWt_anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ ⟨D.R.k - 2, ha⟩ (by show D.R.k - 2 + 1 = D.R.k - 1; omega)
      have e0 : P.uMinus τ ⟨D.R.k - 2, ha⟩ = 0 := by
        simp only [WtPar.uMinus, Pi.sub_apply, Pi.smul_apply, hodgeWt, CompHt.barWt, smul_eq_mul, e1]
        rw [if_pos (by show D.R.k - 2 < (dat p i).p; omega)]
        ring
      show P.uMinus τ j = P.wt P.T τ j + GlobalTheory.FlatLine.parWt (dat p i) _ τ j
      rw [e, e0]
      simp [GlobalTheory.FlatLine.parWt, sub_eq_add_neg]
  · intro s hs τ
    have hc := cZero_spec D ((i : ℕ) + 1)
    have hf8 := hh.f8
    have hL := hh.big.2.1
    have hZ : (40 : ℝ) ≤ zBase L := by
      unfold zBase
      have a1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
      have a2 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast (show 6 ≤ D.R.r by omega)
      have a3 : (48 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
      have a4 : (10 : ℝ) ≤ L.sc.L := hL
      nlinarith
    have hPP : (40 : ℝ) ≤ PP := hZ.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hh.ppLow)
    have hD : ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
      rw [hdim]; push_cast [Nat.cast_choose_two]; ring
    have hh1 : 4 * CompHt.dimFlag (dat p i) + 4 ≤ lenT p i PP := hW.h1
    have hh2 : 4 * (cZero D ((i : ℕ) + 1) + 2 * ((D.R.r : ℕ) : ℤ) + lenT p i PP + CompHt.dimFlag (dat p i) + 1) ≤ h0 := by
      have := hW.h2.1
      change 4 * (cZero D ((i : ℕ) + 1) + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) + (lenT p i PP : ℤ) +
        (CompHt.dimFlag (dat p i) : ℤ) + 1) ≤ h0 at this
      rw [er] at this; exact this
    obtain ⟨r1, r2⟩ := GlobalTheory.QuoWt.arith (lenT p i PP : ℝ) (CompHt.dimFlag (dat p i) : ℝ) (cZero D ((i : ℕ) + 1) : ℝ) (h0 : ℝ)
      (D.R.r : ℝ) (D.R.f : ℝ) (D.R.m : ℝ) (D.R.k : ℝ) PP (by exact_mod_cast hh1) (by exact_mod_cast hT2) hrow
      (by exact_mod_cast hh2) (by exact_mod_cast hc.2.1) (by exact_mod_cast hc.2.2) hD hPP
      (by exact_mod_cast (show D.R.r + 4 ≤ 2 * D.R.k by omega)) (by exact_mod_cast hm)
      (by exact_mod_cast (show 6 ≤ D.R.r by omega)) (by exact_mod_cast hf8)
    have hbar : ((P.T : ℤ) + P.c₀) * ((P.T : ℤ) + CompHt.dimFlag (dat p i) + 1) + P.c₀ +
        2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) - 2 ≤ h0 := by
      rw [er]; exact_mod_cast r1
    have hTD : 2 * ((dat p i).p + (dat p i).q) + CompHt.dimFlag (dat p i) ≤ P.T := by
      rw [er]; exact_mod_cast r2
    exact GlobalTheory.QuoWt.dominance (dat p i) P hW.weightConst_nonneg hTD
      (fun τ a b hab => ⟨fun hb => (hW.h4 τ a b hab).1 hb, fun hb => hbar.trans ((hW.h4 τ a b hab).2.2 hb)⟩) s hs τ

end Pt

theorem weights_at_point : Size → Lifts fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → 1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 ∧ (∀ u1, Quo p i PP u1 → u1 = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) ∧ (∀ τ, StrictAnti ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ) ∧ StrictAnti (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ)) ∧ (∃ w : Psi p.T.Q.H → ℤ, (∀ τ, |w τ| ≤ 3 * ((Fm.D x ι).R.r : ℤ)) ∧ uM p i = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP) + GlobalTheory.FlatLine.parWt (dat p i) w) ∧ ∀ s : ℕ, s ≤ 3 → ∀ τ, Antitone (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ) ∧ Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + (if s = 0 then 3 else 4) : ℕ) : ℤ) • (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ - (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ)) := by
  intro _
  have hw : WtN := GlobalTheory.T.weight_bound_holds
  have hh : HostN 1 := GlobalTheory.CovTop.Sizes.hostN 1
  unfold WtN Lifts at hw
  unfold HostN Lifts at hh
  unfold Lifts
  refine Closed.imp (Closed.and hw hh) ?_
  intro eps Fm CH _ h
  obtain ⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩ := h
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi => ?_⟩
  exact atPoint p i _ _ _ hi (h1 x hx ((le_max_left _ _).trans hle) ι p hp i)
    (h2 x hx ((le_max_right _ _).trans hle) ι p hp i)

end GlobalTheory.QuoWt
