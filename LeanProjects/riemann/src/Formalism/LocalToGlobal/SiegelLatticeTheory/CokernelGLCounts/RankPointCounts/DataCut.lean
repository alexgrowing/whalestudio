import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.HermitianCurvature.StatementTC
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AddedBlockKernelSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensitySumsAndDomination
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SmoothBigCellSectionsExist
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalOrbitGerms
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFilterResCharLe
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportProposition

noncomputable section

namespace Formalism.L2.SG.DataCut

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.FourierDecayAlt Formalism.L2.SG.DataInst
open Classical ValuativeRel
open scoped ComplexOrder

def PtUnitAE (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (T T' n : ℕ) (w : Point D.host.E n), n ≤ D.R.rS + 1 →
    {p : PlF D | ¬ ((M p).split = none ∧ (∀ x ∈ (M p).R, (M p).psiR x = 1) ∧
      ∃ a, modPt δ T T' p w = some a ∧ (M p).InGLR a)}.Finite

def qP {D : Formalism.BasicNotions.D7} (p : PlF D) : ℝ :=
  (Nat.card (IsLocalRing.ResidueField 𝒪[(D.s.atP p).Fp]) : ℝ)

def DensLocBound (D : Formalism.BasicNotions.D7) : Prop :=
  2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
      (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)), IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ Z : CntLocal.MatZ D, (∃ Λ ∈ what₂, (CntLocal.EZ (CntLocal.Tn u') F0 Λ Z).Nonempty) →
      (∀ p, 0 < CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z p ∧
        CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z p / alpD u u' p ≤
          Real.exp (4 * (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹)) ∧
      {p | CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z p / alpD u u' p <
          Real.exp (-(5 * (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹))}.Finite

def AlpBound (D : Formalism.BasicNotions.D7) : Prop :=
  2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → ∀ (u u' : D.what₂.Word) (p : PlF D),
    Real.exp (-(2 * (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹)) ≤ alpD u u' p ∧
      alpD u u' p ≤ Real.exp (2 * (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹)

def PlacesOver (D : Formalism.BasicNotions.D7) : Prop :=
  (∀ p : PlF D, ((Loc.resChar p : ℕ) : ℝ) ≤ qP p) ∧
  ∀ (m : ℕ) (S : Finset (PlF D)), (∀ p ∈ S, Loc.resChar p = m) → S.card ≤ D.R.f

section Rows

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def rowKer (vR : TermDef.Term D u u' F0 what₂ → ℝ) (κ : TermDef.Term D u u' F0 what₂ → ℕ) (nc : ℝ)
    (x y : TB.Pt D.host.E) : ℂ :=
  ∑' ρ : ℕ, rowVec vR κ nc ρ x * (starRingEnd ℂ) (rowVec vR κ nc ρ y)

end Rows

def RowsFinAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ (nc : ℝ) (κ : TermDef.Term D u u' F0 what₂ → ℕ), RowLabel κ → ∀ x : TB.Pt D.host.E,
      {ρ : ℕ | rowVec (PairVal.vRdef D u u' F0 what₂ δ M) κ nc ρ x ≠ 0}.Finite

def RowsDomAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (Wp Wq : InfinitePlace D.host.E → Type) [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep), (∀ p, Agree δ M p) →
    ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Compat S u u' →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc → ∀ α : ℝ, 0 < α →
    BddAbove (densSet L δ ϖ u u' F0 what₂) →
    ∀ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ →
    ∀ Y : Finset (TB.Pt D.host.E), (∀ p ∈ Y, TB.IsPt p ((dOf S δ M u u').r + 1)) →
      TB.PSDOn Y (fun p q => ((supDens L δ ϖ u u' F0 what₂ / α : ℝ) : ℂ) *
          (dOf S δ M u u').Kr ((dOf S δ M u u').r + 1) p q -
        rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) p q)

def ClK {E W : Type} [Field E] (Dt : TB.Data E W) : Prop :=
  ∀ (i : ℕ) (Y : Finset (TB.Pt E)),
    ∃ (P : Type) (_ : Fintype P) (pl : P → PB.Place E) (η : ∀ p, TB.Pt E → A5.Point (pl p).K)
      (cl : P → TB.Pt E → Option E) (d : P → TB.Pt E → ℂ) (a : TB.Pt E → ℝ),
      ∀ x ∈ Y, ∀ y ∈ Y, Dt.Kr i x y = (a x : ℂ) * a y *
        ∏ p, if cl p x = cl p y then
          d p x * (starRingEnd ℂ) (d p y) * A5.Kp (pl p).R (pl p).ψ (η p x) (η p y) else 0

def ClS {E W : Type} [Field E] (Dt : TB.Data E W) : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ Dt.r + 1 → ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - s) →
    ∃ (P : Type) (_ : Fintype P) (S : P → J.LocSys E (TB.Pt E)) (a : TB.Pt E → ℝ),
      (∀ p, ((i = Dt.r + 1 ∧ s = 1) ∧ PB.IsTopSys (S p) Y false) ∨
        (¬ (i = Dt.r + 1 ∧ s = 1) ∧ PB.IsPull (S p) Y s false) ∨ PB.IsOut (S p) Y s (i = Dt.r + 1 ∧ s = 1)) ∧
      (∀ t t', t ≠ 0 → t' ≠ 0 → ∀ h ∈ Y, ∀ h' ∈ Y,
        (J.sysOf Dt i s).N t t' h h' = (J.scaleSys a (J.prodSys S)).N t t' h h') ∧
      (∀ h ∈ Y, ∀ h' ∈ Y, (J.sysOf Dt i s).B h h' = (J.scaleSys a (J.prodSys S)).B h h') ∧
      (J.sysOf Dt i s).L = ⨅ p, (S p).L ∧ (⨅ p, (S p).L') ≤ (J.sysOf Dt i s).L'

def ClT {E W : Type} [Field E] (Dt : TB.Data E W) : Prop :=
  ∀ (h h' : TB.Pt E) (t t' : E), TB.level h = Dt.r → TB.level h' = Dt.r → t ≠ 0 → t' ≠ 0 → t ≠ t' →
    Dt.Kr (Dt.r + 1) (TB.join h 1 t) (TB.join h' 1 t') = 0

def LMAt (D : Formalism.BasicNotions.D7) (P : ∀ {W : Type}, TB.Data D.host.E W → Prop) : Prop :=
  ∀ (Wp Wq : InfinitePlace D.host.E → Type) [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep), (∀ p, Agree δ M p) →
    ∀ u u' : D.what₂.Word, Compat S u u' → P (dOf S δ M u u')

def LocalModelK (D : Formalism.BasicNotions.D7) : Prop := LMAt D ClK

def LocalModelS (D : Formalism.BasicNotions.D7) : Prop := LMAt D ClS

def LocalModelT (D : Formalism.BasicNotions.D7) : Prop := LMAt D ClT

theorem localModelAt_of {D : Formalism.BasicNotions.D7} (hK : LocalModelK D) (hS : LocalModelS D) (hT : LocalModelT D) :
    LocalModelAt D := by
  intro Wp Wq _ _ _ _ S δ M hA u u' hC
  exact ⟨hK Wp Wq S δ M hA u u' hC, hS Wp Wq S δ M hA u u' hC, hT Wp Wq S δ M hA u u' hC,
    fun _ _ _ => rfl⟩

section KrF

variable {D : Formalism.BasicNotions.D7}

def badSet (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (T T' n : ℕ) (w : Point D.host.E n) : Set (PlF D) :=
  {p : PlF D | ¬ ((M p).split = none ∧ (∀ x ∈ (M p).R, (M p).psiR x = 1) ∧
      ∃ a, modPt δ T T' p w = some a ∧ (M p).InGLR a)}

theorem locK_eq_one (hK : Formalism.MainNotions.LocalModelPeriodLattices.KKAll) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {T T' n : ℕ}
    {w w' : Point D.host.E n} {p : PlF D} (hw : p ∉ badSet δ M T T' n w) (hw' : p ∉ badSet δ M T T' n w') :
    locK M δ T T' p n w w' = 1 := by
  simp only [badSet, Set.mem_setOf_eq, not_not] at hw hw'
  obtain ⟨_, hψ, a, ha, haG⟩ := hw
  obtain ⟨_, _, b, hb, hbG⟩ := hw'
  unfold locK
  rw [ha, hb]
  simp only
  rw [hK _ _ (M p) (hA p).1 n a b]
  exact Formalism.FourierDecayAlt.P.zero_kernel_all_ones _ (M p).R (M p).psiR hψ _ _
    (by rw [Formalism.MainNotions.LocalModelPeriodLattices.tr_sum, Formalism.MainNotions.LocalModelPeriodLattices.tr_sum])
    (Formalism.MainNotions.LocalModelPeriodLattices.inGLR_tr a haG) (Formalism.MainNotions.LocalModelPeriodLattices.inGLR_tr b hbG)

theorem dfac_eq_one {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {T T' : ℕ} {p : PlF D}
    (hs : (M p).split = none) (w : Point D.host.E (D.R.rS + 1)) : dfac M δ T T' p w = 1 := by
  have h := (hA p).2.2.2.2.2
  rw [hs] at h
  have hs' : (D.s.atP p).split = none := by
    cases h' : (D.s.atP p).split with
    | none => rfl
    | some sg => rw [h'] at h; exact h.elim
  unfold dfac
  rw [hs']

end KrF

section DensA

variable {D : Formalism.BasicNotions.D7}

theorem qP_nonneg (p : PlF D) : 0 ≤ qP p := Nat.cast_nonneg _

theorem densInputAt_of (hL : DensLocBound D) (hα : AlpBound D) (hP : PlacesOver D) : DensInputAt D := by
  intro hk δ M hA L u u' hT F0 what₂ hrows ϖ hϖ
  set s := D.R.k - 2 * D.R.rS - 2 with hs
  have hs2 : 2 ≤ s := by omega
  set a : PlF D → ℝ := fun p => (qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S qP Loc.resChar D.R.f s hs2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum

  have hαb := hα hk u u'
  have hal0 : ∀ p, 0 < alpD u u' p := fun p => lt_of_lt_of_le (Real.exp_pos _) (hαb p).1
  have hlogα : Summable fun p => Real.log (alpD u u' p) := by
    refine Summable.of_norm_bounded (g := fun p => 2 * a p) (haS.mul_left 2) (fun p => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := Real.log_le_log (Real.exp_pos _) (hαb p).1
    have h2 := Real.log_le_log (hal0 p) (hαb p).2
    rw [Real.log_exp] at h1 h2
    have ha' : a p = (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹ := rfl
    constructor <;> linarith
  have hMα : Multipliable (alpD u u') := Real.multipliable_of_summable_log hal0 hlogα
  have hαpos : 0 < ∏' p, alpD u u' p := by
    rw [← Real.rexp_tsum_eq_tprod hal0 hlogα]
    exact Real.exp_pos _

  have key : ∀ Z : CntLocal.MatZ D, (∃ Λ ∈ what₂, (CntLocal.EZ (CntLocal.Tn u') F0 Λ Z).Nonempty) →
      Multipliable (fun p => CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z p / alpD u u' p) ∧
      Multipliable (CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z) ∧
      ∏' p, CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z p =
        (∏' p, CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z p / alpD u u' p) * ∏' p, alpD u u' p ∧
      ∏' p, CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z p / alpD u u' p ≤
        Real.exp (4 * ∑' p, a p) := by
    intro Z hZ
    obtain ⟨hb, hfin⟩ := hL hk δ M hA L u u' hT F0 what₂ hrows ϖ hϖ Z hZ
    set d := CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z with hd
    set q : PlF D → ℝ := fun p => d p / alpD u u' p with hq
    have hq0 : ∀ p, 0 < q p := fun p => div_pos (hb p).1 (hal0 p)
    have hlog_le : ∀ p, Real.log (q p) ≤ 4 * a p := fun p => by
      rw [Real.log_le_iff_le_exp (hq0 p)]; exact (hb p).2
    have hlogS : Summable fun p => Real.log (q p) := by
      refine Summable.of_norm_bounded_eventually (g := fun p => 5 * a p) (haS.mul_left 5) ?_
      refine Filter.mem_of_superset hfin.compl_mem_cofinite ?_
      intro p hp
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hp
      show ‖Real.log (q p)‖ ≤ 5 * a p
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := Real.log_le_log (Real.exp_pos _) hp
        rw [Real.log_exp] at this
        have ha' : a p = (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹ := rfl
        have hq' : q p = d p / alpD u u' p := rfl
        rw [hq']
        linarith
      · linarith [hlog_le p, ha0 p]
    have hMq : Multipliable q := Real.multipliable_of_summable_log hq0 hlogS
    have hdq : d = fun p => q p * alpD u u' p := by
      funext p
      simp only [hq]
      rw [div_mul_cancel₀ _ (hal0 p).ne']
    have hMd : Multipliable d := by rw [hdq]; exact hMq.mul hMα
    refine ⟨hMq, hMd, ?_, ?_⟩
    · rw [hdq]; exact hMq.tprod_mul hMα
    · rw [← Real.rexp_tsum_eq_tprod hq0 hlogS]
      apply Real.exp_le_exp.2
      rw [← tsum_mul_left]
      exact hlogS.tsum_le_tsum hlog_le (haS.mul_left 4)
  have hbdd : BddAbove (densSet L δ ϖ u u' F0 what₂) := by
    refine ⟨Real.exp (4 * ∑' p, a p) * ∏' p, alpD u u' p, ?_⟩
    rintro _ ⟨Z, hZ, rfl⟩
    obtain ⟨-, -, he, hle⟩ := key Z hZ
    rw [he]
    exact mul_le_mul_of_nonneg_right hle hαpos.le
  refine ⟨fun Z hZ => (key Z hZ).2.1, hbdd, hMα, hαpos, hk, PlF D, qP, Loc.resChar,
    fun p => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩, hP.2, ?_⟩
  intro x hx
  by_cases hne : (densSet L δ ϖ u u' F0 what₂).Nonempty
  · have hx' : x * ∏' p, alpD u u' p < supDens L δ ϖ u u' F0 what₂ := (lt_div_iff₀ hαpos).1 hx
    obtain ⟨d, ⟨Z, hZ, rfl⟩, hxd⟩ := exists_lt_of_lt_csSup hne hx'
    obtain ⟨hMq, -, he, -⟩ := key Z hZ
    obtain ⟨hb, -⟩ := hL hk δ M hA L u u' hT F0 what₂ hrows ϖ hϖ Z hZ
    rw [he] at hxd
    have hxq : x < ∏' p, CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z p / alpD u u' p :=
      lt_of_mul_lt_mul_right hxd hαpos.le
    obtain ⟨S, hS⟩ := (hMq.hasProd.eventually (lt_mem_nhds hxq)).exists
    refine ⟨S, le_of_lt (lt_of_lt_of_le hS ?_)⟩
    exact Finset.prod_le_prod (fun p _ => (div_pos (hb p).1 (hal0 p)).le) (fun p _ => (hb p).2)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : supDens L δ ϖ u u' F0 what₂ = 0 := by simp [supDens, hne]
    rw [h0, zero_div] at hx
    refine ⟨∅, ?_⟩
    rw [Finset.prod_empty]
    linarith

end DensA

section Label

variable {D : Formalism.BasicNotions.D7}

instance countable_E : Countable D.host.E :=
  (Module.finBasis ℚ D.host.E).equivFun.injective.countable

instance countable_V : Countable (VS D).V :=
  (VS D).frame.equivFun.injective.countable

theorem countable_LFlag {r : ℕ} {T : D.host.E} : Countable (Lat.LFlag (VS D) r T) := by
  refine Function.Injective.countable (f := fun F : Lat.LFlag (VS D) r T => (F.fl.e, F.fl.z, F.zt)) ?_
  rintro ⟨⟨e, z, _, _, _, _⟩, zt⟩ ⟨⟨e', z', _, _, _, _⟩, zt'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem countable_Term (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Countable (TermDef.Term D u u' F0 what₂) := by
  have : ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, Countable (TermDef.TermsOf D u' F0 Λ) := fun Λ => by
    have := countable_LFlag (D := D) (r := D.R.rS) (T := ((Lat.Tu D u' : ℕ) : D.host.E))
    unfold TermDef.TermsOf TermDef.TermQ
    infer_instance
  refine Function.Injective.countable
    (f := fun t : TermDef.Term D u u' F0 what₂ => (⟨⟨t.lam, t.mem⟩, t.cls⟩ :
      Σ Λ : {Λ // Λ ∈ what₂}, TermDef.TermsOf D u' F0 Λ.1)) ?_
  rintro ⟨l, m, c⟩ ⟨l', m', c'⟩ h
  simp only [Sigma.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  cases eq_of_heq h2
  rfl

theorem rowLabelExists_of (hG : Corank.ScalarEquivG) (hR : ∀ u u' : D.what₂.Word, Corank.ScalarRepFree D u u') :
    RowLabelExists D := by
  intro u u' F0 what₂ hrows
  have e := Corank.scalarEquivT_of (Formalism.L2.SG.Pf.term_equivalence_iff D u u') (Corank.scalarEquiv_of_G hG u u') (hR u u')
    F0 what₂ hrows
  letI s : Setoid {t : TermDef.Term D u u' F0 what₂ // t.G ≠ 0} := ⟨_, e⟩
  have := countable_Term u u' F0 what₂
  obtain ⟨enc, henc⟩ := exists_injective_nat (Quotient s)
  refine ⟨fun t => if h : t.G ≠ 0 then enc (Quotient.mk s ⟨t, h⟩) else 0, ?_⟩
  intro t t' ht ht'
  simp only [dif_pos ht.2, dif_pos ht'.2, henc.eq_iff, Quotient.eq]
  exact Iff.rfl

end Label

section RowsA

variable {D : Formalism.BasicNotions.D7}

private theorem posSemidef_outer_product {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    (Matrix.of fun x y => u x * star (u y)).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (Matrix.of fun (_ : Unit) (j : ι) => star (u j))
  convert h using 1
  ext x y
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem psdOn_of_full {α : Type} (Y : Finset α) (K : α → α → ℂ) (c : ℕ → α → ℂ)
    (hfin : ∀ x, {ρ | c ρ x ≠ 0}.Finite)
    (hD : TB.PSDOn Y (fun p q => K p q - ∑' ρ, c ρ p * (starRingEnd ℂ) (c ρ q))) (R : Finset ℕ) :
    TB.PSDOn Y (fun p q => K p q - ∑ ρ ∈ R, c ρ p * (starRingEnd ℂ) (c ρ q)) := by
  classical
  have hF : ((Y : Set α)).Finite := Y.finite_toSet
  let F : Finset ℕ := (hF.biUnion fun x _ => hfin x).toFinset
  have hmem : ∀ x ∈ Y, ∀ ρ, ρ ∉ F → c ρ x = 0 := by
    intro x hx ρ hρ
    by_contra h
    exact hρ ((Set.Finite.mem_toFinset _).2 (Set.mem_iUnion₂.2 ⟨x, hx, h⟩))
  have hts : ∀ x ∈ Y, ∀ y ∈ Y, ∑' ρ, c ρ x * (starRingEnd ℂ) (c ρ y) =
      ∑ ρ ∈ F, c ρ x * (starRingEnd ℂ) (c ρ y) := by
    intro x hx y hy
    exact tsum_eq_sum (fun ρ hρ => by simp [hmem x hx ρ hρ])
  have hR : ∀ x ∈ Y, ∀ y ∈ Y, ∑ ρ ∈ R, c ρ x * (starRingEnd ℂ) (c ρ y) =
      ∑ ρ ∈ F ∩ R, c ρ x * (starRingEnd ℂ) (c ρ y) := by
    intro x hx y hy
    rw [Finset.inter_comm]
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro ρ hρR hρ
    have : ρ ∉ F := fun h => hρ (Finset.mem_inter.2 ⟨hρR, h⟩)
    simp [hmem x hx ρ this]
  simp only [TB.PSDOn] at hD ⊢
  have hS : (∑ ρ ∈ F \ R, Matrix.of fun x y : Y => c ρ x * star (c ρ y)).PosSemidef :=
    Finset.sum_induction _ Matrix.PosSemidef (fun A B hA hB => hA.add hB) Matrix.PosSemidef.zero
      (fun ρ _ => posSemidef_outer_product (fun x : Y => c ρ x))
  convert hD.add hS using 1
  ext x y
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.sum_apply, starRingEnd_apply]
  have h1 := hts x x.2 y y.2
  have h2 := hR x x.2 y y.2
  simp only [starRingEnd_apply] at h1 h2
  have e : F \ (F ∩ R) = F \ R := by
    ext ρ
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [h1, h2, ← Finset.sum_sdiff (Finset.inter_subset_left : F ∩ R ⊆ F), e]
  ring

end RowsA

section LMT

theorem signFlip_append {K : Type} [Ring K] (r : ℕ) : ∀ (b : ℕ) (x : TB.Pt K) (c : ℕ × K),
    signAux r b (x ++ [c]) =
      signAux r b x ++ [(c.1, (-1) ^ (r + 1 - (b + (x.map Prod.fst).sum + c.1 - 1)) * c.2)]
  | b, [], c => by simp [signAux]
  | b, (s, t) :: rest, c => by
    simp only [List.cons_append, signAux, signFlip_append r (b + s) rest c, List.map_cons, List.sum_cons, add_assoc]

theorem kind_ptOfList_join {D : Formalism.BasicNotions.D7} (h : TB.Pt D.host.E) (t : D.host.E) (hh : TB.level h = D.R.rS)
    (a : Point D.host.E (D.R.rS + 1)) (ha : ptOfList (D.R.rS + 1) (TB.join h 1 t) = some a) :
    kind a = some t := by
  unfold ptOfList at ha
  split_ifs at ha with hx
  cases ha
  set w := (Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).symm ⟨signPt D.R.rS (TB.join h 1 t), hx⟩ with hw
  have hl : (h.map Prod.fst).sum = D.R.rS := hh
  have hb : w.1 = (signPt D.R.rS h).map Prod.swap ++ [(t, 1)] := by
    show (signPt D.R.rS (h ++ [(1, t)])).map Prod.swap = (signPt D.R.rS h).map Prod.swap ++ [(t, 1)]
    have e : D.R.rS + 1 - (1 + (h.map Prod.fst).sum + 1 - 1) = 0 := by rw [hl]; omega
    rw [signPt, signFlip_append, e]
    simp [signPt]
  have hs : (((signPt D.R.rS h).map Prod.swap).map Prod.snd).sum = D.R.rS := by
    rw [List.map_map, show (Prod.snd ∘ Prod.swap : ℕ × D.host.E → ℕ) = Prod.fst from funext fun _ => rfl,
      signPt, sign_list_fst]
    exact hl
  have hdet : Dmin w (D.R.rS + 1) ≠ 0 := by
    rw [Formalism.L2.SG.Pf.dmin_top]
    exact Formalism.MainNotions.BridgeLemma.ptMat_det_ne w
  have h0 : Dmin w D.R.rS ≠ 0 := by
    intro h0
    apply hdet
    rw [Formalism.L2.SG.Pf.dmin_snoc w _ t hb hs, h0, zero_mul]
  unfold kind
  rw [if_neg h0, Formalism.L2.SG.Pf.zeta_snoc w h0 _ t hb hs]

theorem localModelT_holds (D : Formalism.BasicNotions.D7) : LocalModelT D := by
  intro Wp Wq _ _ _ _ S δ M hA u u' hC
  intro h h' t t' hh hh' _ _ htt
  have hr : (dOf S δ M u u').r = D.R.rS := hC.1
  rw [hr] at hh hh' ⊢
  show KrOf δ M (D.mem u).A.T (D.mem u').A.T (D.R.rS + 1) (TB.join h 1 t) (TB.join h' 1 t') = 0
  unfold KrOf
  rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _)]
  rcases ha : ptOfList (D.R.rS + 1) (TB.join h 1 t) with _ | a
  · rfl
  rcases hb : ptOfList (D.R.rS + 1) (TB.join h' 1 t') with _ | b
  · rfl
  have e1 := kind_ptOfList_join h t hh a ha
  have e2 := kind_ptOfList_join h' t' hh' b hb
  show Kglob δ M (D.mem u).A.T (D.mem u').A.T (D.R.rS + 1) a b / _ = 0
  rw [Kglob, dif_pos rfl]
  unfold KtopG
  rw [e1, e2, if_neg (by simpa using htt)]
  simp

end LMT

section RowsFin

variable {D : Formalism.BasicNotions.D7}

theorem rowsFinAt_of (hT : ∀ u u' : D.what₂.Word, TermDef.TermsAtFinite D u u') (hsig : (VS D).SigOK) :
    RowsFinAt D := by
  intro δ M hA u u' _ F0 what₂ hrows nc κ _ x
  rcases hx : ptOfList (D.R.rS + 1) x with _ | w
  · refine Set.finite_empty.subset ?_
    intro ρ hρ
    apply hρ
    simp [rowVec, hx]
  · have hfin := TermDef.term_atPt_finite (hT u u') hsig F0 what₂ hrows w
    refine (hfin.image κ).subset ?_
    intro ρ hρ
    by_contra hc
    apply hρ
    have he : IsEmpty {t : TermDef.Term D u u' F0 what₂ // Elig t ∧ κ t = ρ ∧ t.atPt w} :=
      ⟨fun t => hc ⟨t.1, t.2.2.2, t.2.2.1⟩⟩
    simp only [rowVec, hx]
    rw [tsum_empty, zero_div]

end RowsFin

section Places

def ResCardD (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : PlF D, Nat.card (IsLocalRing.ResidueField 𝒪[(D.s.atP p).Fp]) = p.asIdeal.absNorm

theorem locResChar_eq {F : Type} [Field F] [NumberField F] (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Loc.resChar p = Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.resChar p.asIdeal := by
  unfold Loc.resChar
  rw [ringChar.eq_iff]
  refine ⟨fun x => ?_⟩
  have h1 : ((x : ℕ) : 𝓞 F ⧸ p.asIdeal) = Ideal.Quotient.mk p.asIdeal (x : 𝓞 F) := (map_natCast _ x).symm
  rw [h1, Ideal.Quotient.eq_zero_iff_mem]
  have h2 : ((x : 𝓞 F) ∈ p.asIdeal) ↔ (((x : ℕ) : ℤ) ∈ p.asIdeal.under ℤ) := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
  rw [h2, ← Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.span_resChar, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

theorem placesOver_of {D : Formalism.BasicNotions.D7} (hR : ResCardD D) : PlacesOver D := by
  refine ⟨fun p => ?_, fun m S hS => ?_⟩
  · unfold qP
    rw [hR p, locResChar_eq]
    exact_mod_cast Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.resChar_le_absNorm p.isMaximal
  · classical
    let g : PlF D → {P : Ideal (𝓞 D.host.F) // P.IsMaximal} := fun p => ⟨p.asIdeal, p.isMaximal⟩
    have hg : Function.Injective g := fun a b h =>
      IsDedekindDomain.HeightOneSpectrum.ext (congrArg Subtype.val h)
    have h1 := Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.card_filter_resChar_le (K := D.host.F) (S.image g) m
    have hf : (S.image g).filter (fun P => Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.resChar P.1 = m) = S.image g := by
      refine Finset.filter_true_of_mem fun P hP => ?_
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hP
      rw [← locResChar_eq]
      exact hS p hp
    rw [hf, Finset.card_image_of_injective _ hg, Formalism.MainNotions.BridgeLemma.szf_finrankF D] at h1
    exact h1

end Places

def TopUnram (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ T T' : ℕ, ∃ θ0 : ∀ p, Option ((M p).Cls D.R.rS),
      ∀ w : Point D.host.E (D.R.rS + 1),
        (∃ S : Finset (PlF D), Formalism.L2.SG.Pf.UnramOff M δ T T' θ0 S w) ∧ ∀ p, Formalism.L2.SG.Pf.BBsq M δ T T' p w

section RD

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def EligAt (t : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) : Prop := Elig t ∧ t.atPt w

def PartnerSumC (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (vR : TermDef.Term D u u' F0 what₂ → ℝ) (th : TermDef.Term D u u' F0 what₂ → ∀ p, Option ((M p).Cls D.R.rS)) :
    Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 →
    HasSum (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ // Corank.TermScal D γ γ' ∧ EligAt γ' w'} =>
        PairVal.cAt vR γ'.1 w')
      (BBG M δ (D.mem u).A.T (D.mem u').A.T w' (kind w) (th γ))

def FiberCntC (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (vR : TermDef.Term D u u' F0 what₂ → ℝ) (nc : ℝ)
    (th : TermDef.Term D u u' F0 what₂ → ∀ p, Option ((M p).Cls D.R.rS)) (dn : TermDef.Term D u u' F0 what₂ → ℝ) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (γ₀ : TermDef.Term D u u' F0 what₂) (w₀ : Point D.host.E (D.R.rS + 1)), EligAt γ₀ w₀ →
    HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ kind w = kind w₀ ∧ th γ = th γ₀} =>
        (PairVal.massTerm γ.1 : ℂ) * PairVal.cAt vR γ.1 w)
      ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dn γ₀ : ℂ) *
        (((Formalism.L2.SG.Pf.autR M (th γ₀))⁻¹ : ℝ) : ℂ) * BBG M δ (D.mem u).A.T (D.mem u').A.T w (kind w₀) (th γ₀))

end RD

def RowsDatum (D : Formalism.BasicNotions.D7) : Prop :=
  (VS D).SigOK →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
      (∀ d ∈ densSet L δ ϖ u u' F0 what₂, 0 ≤ d) ∧
      ∃ (th : TermDef.Term D u u' F0 what₂ → ∀ p, Option ((M p).Cls D.R.rS)) (dn : TermDef.Term D u u' F0 what₂ → ℝ),
        (∀ θ0 : ∀ p, Option ((M p).Cls D.R.rS),
          (∀ w, ∃ S : Finset (PlF D), Formalism.L2.SG.Pf.UnramOff M δ (D.mem u).A.T (D.mem u').A.T θ0 S w) →
          ∀ γ w, EligAt γ w → Formalism.L2.SG.Pf.Restricted θ0 (th γ)) ∧
        (∀ γ w, EligAt γ w → dn γ ∈ densSet L δ ϖ u u' F0 what₂) ∧
        PartnerSumC δ M (PairVal.vRdef D u u' F0 what₂ δ M) th ∧
        FiberCntC δ M (PairVal.vRdef D u u' F0 what₂ δ M) nc th dn

section RDProof

theorem density_gram_matrix_sub_posSemidef {ι Θ : Type*} [Fintype ι] [Fintype Θ] (v : Θ → ι → ℂ) (a dens : Θ → ℝ) (Dsup : ℝ) (n : ι → ℝ)
    (ha : ∀ θ, 0 ≤ a θ) (hd : ∀ θ, dens θ ≤ Dsup) (hD0 : 0 ≤ Dsup) (hn : ∀ x, 0 ≤ n x)
    (hsupp : ∀ θ x y, v θ x ≠ 0 → v θ y ≠ 0 → n x = n y) :
    (Matrix.of fun x y => (Dsup : ℂ) * ∑ θ, (a θ : ℂ) * v θ x * star (v θ y) -
      (if 0 < n x ∧ 0 < n y then ((n x : ℂ) * ∑ θ, (dens θ : ℂ) * (a θ : ℂ) * v θ x * star (v θ y)) /
        ((Real.sqrt (n x * n y) : ℝ) : ℂ) else 0)).PosSemidef := by
  classical
  have hsum : ∀ (M : Θ → Matrix ι ι ℂ), (∀ θ, (M θ).PosSemidef) → (∑ θ, M θ).PosSemidef := fun M hM =>
    Finset.sum_induction _ Matrix.PosSemidef (fun A B hA hB => hA.add hB) Matrix.PosSemidef.zero
      (fun θ _ => hM θ)
  have h1 : (∑ θ, (((Dsup - dens θ) * a θ : ℝ) : ℂ) • Matrix.of fun x y =>
      (if 0 < n x then v θ x else 0) * star (if 0 < n y then v θ y else 0)).PosSemidef :=
    hsum _ fun θ => (posSemidef_outer_product (fun x => if 0 < n x then v θ x else 0)).smul
      (Complex.zero_le_real.mpr (mul_nonneg (sub_nonneg.mpr (hd θ)) (ha θ)))
  have h2 : (∑ θ, ((Dsup * a θ : ℝ) : ℂ) • Matrix.of fun x y =>
      (if 0 < n x then 0 else v θ x) * star (if 0 < n y then 0 else v θ y)).PosSemidef :=
    hsum _ fun θ => (posSemidef_outer_product (fun x => if 0 < n x then 0 else v θ x)).smul
      (Complex.zero_le_real.mpr (mul_nonneg hD0 (ha θ)))
  convert h1.add h2 using 1
  ext x y
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  by_cases hP : 0 < n x ∧ 0 < n y
  · rw [if_pos hP, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    simp only [if_pos hP.1, if_pos hP.2, star_zero, mul_zero, add_zero]
    by_cases hvx : v θ x = 0
    · simp [hvx]
    by_cases hvy : v θ y = 0
    · simp [hvy]
    have hxy := hsupp θ x y hvx hvy
    rw [← hxy, Real.sqrt_mul_self (hn x)]
    have hnx : (n x : ℂ) ≠ 0 := by exact_mod_cast hP.1.ne'
    field_simp
    push_cast
    ring
  · rw [if_neg hP, sub_zero, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    by_cases hx : 0 < n x <;> by_cases hy : 0 < n y
    · exact absurd ⟨hx, hy⟩ hP
    · simp only [if_pos hx, if_neg hy, star_zero, mul_zero, zero_mul, add_zero]
      by_cases hvx : v θ x = 0
      · simp [hvx]
      by_cases hvy : v θ y = 0
      · simp [hvy]
      have hxy := hsupp θ x y hvx hvy
      exact absurd (hxy ▸ hx) hy
    · simp only [if_neg hx, if_pos hy, star_zero, mul_zero, zero_mul, zero_add]
      by_cases hvx : v θ x = 0
      · simp [hvx]
      by_cases hvy : v θ y = 0
      · simp [hvy]
      have hxy := hsupp θ x y hvx hvy
      exact absurd (hxy ▸ hy) hx
    · simp only [if_neg hx, if_neg hy, star_zero, mul_zero, zero_mul, zero_add]
      push_cast
      ring

end RDProof

section RDProof2

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def chat (vR : TermDef.Term D u u' F0 what₂ → ℝ) (κ : TermDef.Term D u u' F0 what₂ → ℕ) (nc : ℝ) (ρ : ℕ)
    (w : Point D.host.E (D.R.rS + 1)) : ℂ :=
  (∑' t : {t : TermDef.Term D u u' F0 what₂ // Elig t ∧ κ t = ρ ∧ t.atPt w},
      ((Real.sqrt (PairVal.massTerm t.1) : ℝ) : ℂ) * PairVal.cAt vR t.1 w) /
    ((Real.sqrt (n0 nc (D.mem u).A.T (D.mem u').A.T w) : ℝ) : ℂ)

theorem rowVec_eq_chat (vR : TermDef.Term D u u' F0 what₂ → ℝ) (κ : TermDef.Term D u u' F0 what₂ → ℕ) (nc : ℝ)
    (ρ : ℕ) (x : TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)) (hx : ptOfList (D.R.rS + 1) x = some w) :
    rowVec vR κ nc ρ x = chat vR κ nc ρ w / (phi (D.R.rS + 1) x : ℂ) := by
  simp only [rowVec, hx, chat]
  push_cast
  rw [div_div]

theorem massTerm_nonneg (t : TermDef.Term D u u' F0 what₂) : 0 ≤ PairVal.massTerm t := by
  unfold PairVal.massTerm PairVal.massRow
  apply div_nonneg
  · unfold Formalism.MainNotions.S.wRow; positivity
  · unfold Formalism.MainNotions.S.Cnt.massRows
    exact Finset.sum_nonneg fun _ _ => by unfold Formalism.MainNotions.S.wRow; positivity

theorem lam_eq_of_termScal {t t' : TermDef.Term D u u' F0 what₂} (h : Corank.TermScal D t t') : t.lam = t'.lam := by
  obtain ⟨p, rfl, rfl, -⟩ := h
  rfl

theorem chat_eq_sum (vR : TermDef.Term D u u' F0 what₂ → ℝ) (κ : TermDef.Term D u u' F0 what₂ → ℕ) (nc : ℝ) (ρ : ℕ)
    (w : Point D.host.E (D.R.rS + 1)) (Γ : Finset (TermDef.Term D u u' F0 what₂)) (hΓ : ∀ t, t ∈ Γ ↔ EligAt t w) :
    chat vR κ nc ρ w = (∑ t ∈ Γ.filter (fun t => κ t = ρ),
      ((Real.sqrt (PairVal.massTerm t) : ℝ) : ℂ) * PairVal.cAt vR t w) /
        ((Real.sqrt (n0 nc (D.mem u).A.T (D.mem u').A.T w) : ℝ) : ℂ) := by
  simp only [chat]
  congr 1
  have e : ∀ t, (Elig t ∧ κ t = ρ ∧ t.atPt w) ↔ t ∈ Γ.filter (fun t => κ t = ρ) := by
    intro t
    simp only [Finset.mem_filter, hΓ, EligAt]
    tauto
  rw [← Finset.tsum_subtype]
  exact (Equiv.subtypeEquivRight e).tsum_eq
    (fun t : {t // t ∈ Γ.filter (fun t => κ t = ρ)} =>
      ((Real.sqrt (PairVal.massTerm t.1) : ℝ) : ℂ) * PairVal.cAt vR t.1 w)

end RDProof2

section RDProof3

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem normalizing_weight_nonneg {c : ℝ} (hc : 0 ≤ c) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : 0 ≤ n0 c T T' w := by
  unfold n0
  positivity

theorem normalizing_weight_eq_zero {c : ℝ} {T T' : ℕ} {w : Point D.host.E (D.R.rS + 1)} (hG : Gpt T T' w = 0) :
    n0 c T T' w = 0 := by
  have hk : D.R.k - 1 ≠ 0 := by
    have h1 := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    omega
  unfold n0
  rw [hG]
  simp [hk, Algebra.norm_zero]

theorem rows_pair {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (vR : TermDef.Term D u u' F0 what₂ → ℝ) {κ : TermDef.Term D u u' F0 what₂ → ℕ} (hκ : RowLabel κ) (nc : ℝ)
    {th : TermDef.Term D u u' F0 what₂ → ∀ p, Option ((M p).Cls D.R.rS)} (hPS : PartnerSumC δ M vR th)
    (wx wy : Point D.host.E (D.R.rS + 1)) (Γx Γy : Finset (TermDef.Term D u u' F0 what₂))
    (hΓx : ∀ t, t ∈ Γx ↔ EligAt t wx) (hΓy : ∀ t, t ∈ Γy ↔ EligAt t wy)
    (hGy : Gpt (D.mem u).A.T (D.mem u').A.T wy ≠ 0) :
    ∑' ρ, chat vR κ nc ρ wx * star (chat vR κ nc ρ wy) =
      (∑ t ∈ Γx, (PairVal.massTerm t : ℂ) * PairVal.cAt vR t wx *
          star (BBG M δ (D.mem u).A.T (D.mem u').A.T wy (kind wx) (th t))) /
        (((Real.sqrt (n0 nc (D.mem u).A.T (D.mem u').A.T wx) : ℝ) : ℂ) *
          ((Real.sqrt (n0 nc (D.mem u).A.T (D.mem u').A.T wy) : ℝ) : ℂ)) := by
  classical
  set ax : ℂ := ((Real.sqrt (n0 nc (D.mem u).A.T (D.mem u').A.T wx) : ℝ) : ℂ)
  set ay : ℂ := ((Real.sqrt (n0 nc (D.mem u).A.T (D.mem u').A.T wy) : ℝ) : ℂ)
  set f : TermDef.Term D u u' F0 what₂ → Point D.host.E (D.R.rS + 1) → ℂ := fun t w =>
    ((Real.sqrt (PairVal.massTerm t) : ℝ) : ℂ) * PairVal.cAt vR t w
  set Sx : ℕ → ℂ := fun ρ => ∑ t ∈ Γx.filter (fun t => κ t = ρ), f t wx
  set Sy : ℕ → ℂ := fun ρ => ∑ t ∈ Γy.filter (fun t => κ t = ρ), f t wy
  have hcx : ∀ ρ, chat vR κ nc ρ wx = Sx ρ / ax := fun ρ => chat_eq_sum vR κ nc ρ wx Γx hΓx
  have hcy : ∀ ρ, chat vR κ nc ρ wy = Sy ρ / ay := fun ρ => chat_eq_sum vR κ nc ρ wy Γy hΓy
  have hay : star ay = ay := by simp [ay, Complex.star_def]
  have hax : star ax = ax := by simp [ax, Complex.star_def]
  have e1 : ∀ ρ, chat vR κ nc ρ wx * star (chat vR κ nc ρ wy) = Sx ρ * star (Sy ρ) / (ax * ay) := by
    intro ρ
    rw [hcx, hcy, star_div₀, hay]
    ring
  simp_rw [e1]
  have hz : ∀ ρ ∉ Γx.image κ, Sx ρ * star (Sy ρ) / (ax * ay) = 0 := by
    intro ρ hρ
    have : Γx.filter (fun t => κ t = ρ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro t ht hκt
      exact hρ (Finset.mem_image.2 ⟨t, ht, hκt⟩)
    simp [Sx, this]
  rw [tsum_eq_sum (s := Γx.image κ) hz, ← Finset.sum_div]
  congr 1

  have hP : ∀ t ∈ Γx, Sy (κ t) = ((Real.sqrt (PairVal.massTerm t) : ℝ) : ℂ) *
      BBG M δ (D.mem u).A.T (D.mem u').A.T wy (kind wx) (th t) := by
    intro t ht
    have htE := (hΓx t).1 ht
    have hfilt : Γy.filter (fun t' => κ t' = κ t) = Γy.filter (fun t' => Corank.TermScal D t t') := by
      refine Finset.filter_congr fun t' ht' => ?_
      rw [eq_comm]
      exact hκ t t' htE.1 ((hΓy t').1 ht').1
    have hm : ∀ t' ∈ Γy.filter (fun t' => Corank.TermScal D t t'), f t' wy =
        ((Real.sqrt (PairVal.massTerm t) : ℝ) : ℂ) * PairVal.cAt vR t' wy := by
      intro t' ht'
      have hl := lam_eq_of_termScal (Finset.mem_filter.1 ht').2
      have : PairVal.massTerm t' = PairVal.massTerm t := by
        unfold PairVal.massTerm
        rw [hl]
      simp only [f, this]
    show ∑ t' ∈ Γy.filter (fun t' => κ t' = κ t), f t' wy = _
    rw [hfilt, Finset.sum_congr rfl hm, ← Finset.mul_sum]
    congr 1
    have hset : ∀ t', (Corank.TermScal D t t' ∧ EligAt t' wy) ↔ t' ∈ Γy.filter (fun t' => Corank.TermScal D t t') := by
      intro t'
      rw [Finset.mem_filter, hΓy]
      tauto
    rw [← Finset.tsum_subtype, ← (Equiv.subtypeEquivRight hset).tsum_eq]
    exact (hPS t wx htE wy hGy).tsum_eq
  have hfib : ∑ ρ ∈ Γx.image κ, Sx ρ * star (Sy ρ) = ∑ t ∈ Γx, f t wx * star (Sy (κ t)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := Γx.image κ)
      (fun t ht => Finset.mem_image_of_mem κ ht) (fun t => f t wx * star (Sy (κ t)))]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [Sx, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_filter.1 ht).2]
  rw [hfib]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hP t ht]
  have hm0 := massTerm_nonneg t
  simp only [f, star_mul', Complex.star_def, Complex.conj_ofReal]
  have hsq : ((Real.sqrt (PairVal.massTerm t) : ℝ) : ℂ) * ((Real.sqrt (PairVal.massTerm t) : ℝ) : ℂ) =
      (PairVal.massTerm t : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hm0]
  rw [← hsq]
  ring

end RDProof3

section RDProof4

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem dom_points (hN : SupportG.NormProd D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p)
    (hrows : IsRowReps D F0 what₂) {nc : ℝ} (hnc : 0 < nc) (vR : TermDef.Term D u u' F0 what₂ → ℝ)
    {κ : TermDef.Term D u u' F0 what₂ → ℕ} (hκ : RowLabel κ) (hTF : TermDef.TermsAtFinite D u u')
    (hsig : (VS D).SigOK) {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : ∀ w : Point D.host.E (D.R.rS + 1),
      (∃ S : Finset (PlF D), Formalism.L2.SG.Pf.UnramOff M δ (D.mem u).A.T (D.mem u').A.T θ0 S w) ∧
        ∀ p, Formalism.L2.SG.Pf.BBsq M δ (D.mem u).A.T (D.mem u').A.T p w)
    {th : TermDef.Term D u u' F0 what₂ → ∀ p, Option ((M p).Cls D.R.rS)} {dn : TermDef.Term D u u' F0 what₂ → ℝ}
    (hres : ∀ γ w, EligAt γ w → Formalism.L2.SG.Pf.Restricted θ0 (th γ)) (sd : ℝ) (hsd : 0 ≤ sd)
    (hdn : ∀ γ w, EligAt γ w → dn γ ≤ sd) (hPS : PartnerSumC δ M vR th) (hFC : FiberCntC δ M vR nc th dn)
    {ι : Type} [Fintype ι] (w : ι → Point D.host.E (D.R.rS + 1)) :
    (Matrix.of fun x y => (sd : ℂ) * KtopG M δ (D.mem u).A.T (D.mem u').A.T (w x) (w y) -
      ∑' ρ, chat vR κ nc ρ (w x) * star (chat vR κ nc ρ (w y))).PosSemidef := by
  classical
  have hfinA : ∀ x, {t : TermDef.Term D u u' F0 what₂ | t.atPt (w x)}.Finite := fun x =>
    TermDef.term_atPt_finite hTF hsig F0 what₂ hrows (w x)
  let Γ : ι → Finset (TermDef.Term D u u' F0 what₂) := fun x => (hfinA x).toFinset.filter Elig
  have hΓ : ∀ x t, t ∈ Γ x ↔ EligAt t (w x) := by
    intro x t
    simp only [Γ, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, EligAt]
    tauto
  let n : ι → ℝ := fun x => n0 nc (D.mem u).A.T (D.mem u').A.T (w x)
  have hn0 : ∀ x, 0 ≤ n x := fun x => normalizing_weight_nonneg hnc.le _ _ _
  have hnG : ∀ x, 0 < n x → Gpt (D.mem u).A.T (D.mem u').A.T (w x) ≠ 0 := by
    intro x h hG
    have : n x = 0 := normalizing_weight_eq_zero hG
    linarith
  let dat : ι → TermDef.Term D u u' F0 what₂ → Option D.host.E × (∀ p, Option ((M p).Cls D.R.rS)) :=
    fun x t => (kind (w x), th t)
  obtain ⟨Θs, hΘs⟩ : ∃ Θs : Finset (Option D.host.E × (∀ p, Option ((M p).Cls D.R.rS))),
      Θs = Finset.univ.biUnion (fun x => (Γ x).image (dat x)) := ⟨_, rfl⟩
  have maps : ∀ x, ∀ t ∈ Γ x, dat x t ∈ Θs := fun x t ht => by
    rw [hΘs]
    exact Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, Finset.mem_image_of_mem _ ht⟩
  have memΘ : ∀ j : Θs, ∃ x, ∃ t ∈ Γ x, dat x t = j.1 := by
    intro j
    have hj : j.1 ∈ Finset.univ.biUnion (fun x => (Γ x).image (dat x)) := by rw [← hΘs]; exact j.2
    obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.1 hj
    obtain ⟨t, ht, he⟩ := Finset.mem_image.1 hx
    exact ⟨x, t, ht, he⟩
  choose xr rep hrep hdat using memΘ
  have repE : ∀ j, EligAt (rep j) (w (xr j)) := fun j => (hΓ _ _).1 (hrep j)
  have e1 : ∀ j : Θs, j.1.1 = kind (w (xr j)) := fun j => (congrArg Prod.fst (hdat j)).symm
  have e2 : ∀ j : Θs, j.1.2 = th (rep j) := fun j => (congrArg Prod.snd (hdat j)).symm
  have hresΘ : ∀ j ∈ Θs, Formalism.L2.SG.Pf.Restricted θ0 j.2 := fun j hj => by
    rw [e2 ⟨j, hj⟩]
    exact hres _ _ (repE ⟨j, hj⟩)
  have hkindΘ : ∀ j ∈ Θs, ∃ x, j.1 = kind (w x) := fun j hj => ⟨xr ⟨j, hj⟩, e1 ⟨j, hj⟩⟩
  choose Sx hSx using fun x => (hU (w x)).1
  have hB : ∀ x p, Formalism.L2.SG.Pf.BBsq M δ (D.mem u).A.T (D.mem u').A.T p (w x) := fun x => (hU (w x)).2
  let v : Θs → ι → ℂ := fun j x => BBG M δ (D.mem u).A.T (D.mem u').A.T (w x) j.1.1 j.1.2
  let a : Θs → ℝ := fun j => (Formalism.L2.SG.Pf.autR M j.1.2)⁻¹
  let dens : Θs → ℝ := fun j => dn (rep j)
  have hsupp : ∀ j x y, v j x ≠ 0 → v j y ≠ 0 → n x = n y := by
    intro j x y hx hy
    exact SupportG.n0_eq_of_normG_eq (Formalism.L2.SG.Pf.supportVec_of_normProd hN δ M hA _ _ (w x) (w y) j.1.1 j.1.2
      (Formalism.L2.SG.Pf.bbtop_mulSupport_finite (hSx x) (hresΘ j.1 j.2))
      (Formalism.L2.SG.Pf.bbtop_mulSupport_finite (hSx y) (hresΘ j.1 j.2)) hx hy) _
  have hclose := density_gram_matrix_sub_posSemidef v a dens sd n (fun j => inv_nonneg.2 (Formalism.L2.SG.Pf.autR_nonneg _))
    (fun j => hdn _ _ (repE j)) hsd hn0 hsupp
  have hKA := Formalism.L2.SG.Pf.ktop_sub_posSemidef w θ0 Sx hSx hB Θs (fun j hj => ⟨hkindΘ j hj, hresΘ j hj⟩)
  have hrow : ∀ x y, ∑' ρ, chat vR κ nc ρ (w x) * star (chat vR κ nc ρ (w y)) =
      if 0 < n x ∧ 0 < n y then ((n x : ℂ) * ∑ j, (dens j : ℂ) * (a j : ℂ) * v j x * star (v j y)) /
        ((Real.sqrt (n x * n y) : ℝ) : ℂ) else 0 := by
    intro x y
    split_ifs with hxy
    · rw [rows_pair vR hκ nc hPS (w x) (w y) (Γ x) (Γ y) (hΓ x) (hΓ y) (hnG y hxy.2),
        Real.sqrt_mul (hn0 x), Complex.ofReal_mul]
      congr 1
      rw [← Finset.sum_fiberwise_of_maps_to (maps x), ← Finset.sum_coe_sort Θs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hfib : ∀ t ∈ (Γ x).filter (fun t => dat x t = j.1),
          (PairVal.massTerm t : ℂ) * PairVal.cAt vR t (w x) *
            star (BBG M δ (D.mem u).A.T (D.mem u').A.T (w y) (kind (w x)) (th t)) =
          ((PairVal.massTerm t : ℂ) * PairVal.cAt vR t (w x)) * star (v j y) := by
        intro t ht
        have h2 := (Finset.mem_filter.1 ht).2
        simp only [v, ← h2, dat]
      rw [Finset.sum_congr rfl hfib, ← Finset.sum_mul]
      have hF := hFC (w x) (hnG x hxy.1) (rep j) (w (xr j)) (repE j)
      have hset : ∀ t, (EligAt t (w x) ∧ kind (w x) = kind (w (xr j)) ∧ th t = th (rep j)) ↔
          t ∈ (Γ x).filter (fun t => dat x t = j.1) := by
        intro t
        rw [Finset.mem_filter, hΓ, ← hdat j]
        simp only [dat, Prod.mk.injEq]
        try tauto
      have hsum : ∑ t ∈ (Γ x).filter (fun t => dat x t = j.1), (PairVal.massTerm t : ℂ) * PairVal.cAt vR t (w x) =
          (n x : ℂ) * (dens j : ℂ) * (a j : ℂ) * v j x := by
        have h1 : ∑ t ∈ (Γ x).filter (fun t => dat x t = j.1), (PairVal.massTerm t : ℂ) * PairVal.cAt vR t (w x) =
            ∑' t : {t : TermDef.Term D u u' F0 what₂ // EligAt t (w x) ∧ kind (w x) = kind (w (xr j)) ∧
              th t = th (rep j)}, (PairVal.massTerm t.1 : ℂ) * PairVal.cAt vR t.1 (w x) := by
          rw [← Finset.tsum_subtype]
          exact ((Equiv.subtypeEquivRight hset).tsum_eq
            (fun t : {t // t ∈ (Γ x).filter (fun t => dat x t = j.1)} =>
              (PairVal.massTerm t.1 : ℂ) * PairVal.cAt vR t.1 (w x))).symm
        rw [h1, hF.tsum_eq]
        simp only [n, dens, a, v, e1 j, e2 j]
      rw [hsum]
      ring
    · have h0 : n x = 0 ∨ n y = 0 := by
        by_contra h
        push_neg at h
        exact hxy ⟨lt_of_le_of_ne (hn0 x) (Ne.symm h.1), lt_of_le_of_ne (hn0 y) (Ne.symm h.2)⟩
      rcases h0 with h0 | h0
      · have hc : ∀ ρ, chat vR κ nc ρ (w x) = 0 := fun ρ => by
          have h0' : n0 nc (D.mem u).A.T (D.mem u').A.T (w x) = 0 := h0
          simp only [chat, h0', Real.sqrt_zero, Complex.ofReal_zero, div_zero]
        simp [hc]
      · have hc : ∀ ρ, chat vR κ nc ρ (w y) = 0 := fun ρ => by
          have h0' : n0 nc (D.mem u).A.T (D.mem u').A.T (w y) = 0 := h0
          simp only [chat, h0', Real.sqrt_zero, Complex.ofReal_zero, div_zero]
        simp [hc]
  have hM : (Matrix.of fun x y => (sd : ℂ) * KtopG M δ (D.mem u).A.T (D.mem u').A.T (w x) (w y) -
      ∑' ρ, chat vR κ nc ρ (w x) * star (chat vR κ nc ρ (w y))) =
      (sd : ℂ) • (Matrix.of fun x y => KtopG M δ (D.mem u).A.T (D.mem u').A.T (w x) (w y) -
        ∑ j ∈ Θs, (((Formalism.L2.SG.Pf.autR M j.2)⁻¹ : ℝ) : ℂ) * BBG M δ (D.mem u).A.T (D.mem u').A.T (w x) j.1 j.2 *
          star (BBG M δ (D.mem u).A.T (D.mem u').A.T (w y) j.1 j.2)) +
      (Matrix.of fun x y => (sd : ℂ) * ∑ j, (a j : ℂ) * v j x * star (v j y) -
        (if 0 < n x ∧ 0 < n y then ((n x : ℂ) * ∑ j, (dens j : ℂ) * (a j : ℂ) * v j x * star (v j y)) /
          ((Real.sqrt (n x * n y) : ℝ) : ℂ) else 0)) := by
    ext x y
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [hrow x y]
    have hA' : ∑ j : Θs, (a j : ℂ) * v j x * star (v j y) = ∑ j ∈ Θs,
        (((Formalism.L2.SG.Pf.autR M j.2)⁻¹ : ℝ) : ℂ) * BBG M δ (D.mem u).A.T (D.mem u').A.T (w x) j.1 j.2 *
          star (BBG M δ (D.mem u).A.T (D.mem u').A.T (w y) j.1 j.2) :=
      Finset.sum_coe_sort Θs (fun j => (((Formalism.L2.SG.Pf.autR M j.2)⁻¹ : ℝ) : ℂ) *
        BBG M δ (D.mem u).A.T (D.mem u').A.T (w x) j.1 j.2 *
          star (BBG M δ (D.mem u).A.T (D.mem u').A.T (w y) j.1 j.2))
    rw [hA']
    ring
  rw [hM]
  exact (hKA.smul (Complex.zero_le_real.2 hsd)).add hclose

end RDProof4

section RDProof5

variable {D : Formalism.BasicNotions.D7}

end RDProof5

section Close

theorem rowLabelExists_holds (D : Formalism.BasicNotions.D7) : RowLabelExists D := rowLabelExists_of Formalism.L2.SG.Closed.ScalarEquivG_holds (fun u u' => Formalism.L2.SG.Closed.ScalarRepFree_holds D u u')

theorem localModelAt_of_KS {D : Formalism.BasicNotions.D7} (hK : LocalModelK D) (hS : LocalModelS D) : LocalModelAt D := localModelAt_of hK hS (localModelT_holds D)

end Close

end Formalism.L2.SG.DataCut
