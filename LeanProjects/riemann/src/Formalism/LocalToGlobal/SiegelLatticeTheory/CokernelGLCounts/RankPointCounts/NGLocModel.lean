import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGDictPf

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.NGLocModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

open Formalism.MainNotions.S.LocNG Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

theorem sum_le_sumSq {P : FPair H r} (R : Reps P) (d0 : Datum P) (S : Term V M r → Prop) (Ds : Finset (Datum P))
    (hD : ∀ d ∈ Ds, d ∈ R.RD) :
    ∑ d ∈ Ds, ENNReal.ofReal (Datum.wt d0 d) * ((‖amp R d S‖₊ : ENNReal) ^ 2) ≤ sumSq R d0 S := by
  unfold sumSq
  rw [← Finset.sum_subtype_of_mem
    (fun d => ENNReal.ofReal (Datum.wt d0 d) * ((‖amp R d S‖₊ : ENNReal) ^ 2)) hD]
  exact ENNReal.sum_le_tsum _

theorem real_sum_le {P : FPair H r} (R : Reps P) (d0 : Datum P) (S : Term V M r → Prop) (Ds : Finset (Datum P))
    (hD : ∀ d ∈ Ds, d ∈ R.RD) {B : ENNReal} (hB : sumSq R d0 S ≤ B) (hBt : B ≠ ⊤) :
    ∑ d ∈ Ds, Datum.wt d0 d * ‖amp R d S‖ ^ 2 ≤ B.toReal := by
  have h1 := (sum_le_sumSq R d0 S Ds hD).trans hB
  have hfin : ∀ d ∈ Ds, ENNReal.ofReal (Datum.wt d0 d) * ((‖amp R d S‖₊ : ENNReal) ^ 2) ≠ ⊤ := fun d _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  calc ∑ d ∈ Ds, Datum.wt d0 d * ‖amp R d S‖ ^ 2
      ≤ ∑ d ∈ Ds, (ENNReal.ofReal (Datum.wt d0 d) * ((‖amp R d S‖₊ : ENNReal) ^ 2)).toReal := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = (∑ d ∈ Ds, ENNReal.ofReal (Datum.wt d0 d) * ((‖amp R d S‖₊ : ENNReal) ^ 2)).toReal :=
        (ENNReal.toReal_sum hfin).symm
    _ ≤ B.toReal := ENNReal.toReal_mono hBt h1

theorem ngAt_real (k C1 : ℕ) (hk : 2 * r + 5 ≤ k) {P : FPair H r} (hNG : NGAt k P (C1 : ℝ)) (R : Reps P)
    (d0 : Datum P) (Ds : Finset (Datum P)) (hD : ∀ d ∈ Ds, d ∈ R.RD) (hn : nn R d0 ≠ ⊤) (hHp : 0 ≤ P.Hp) :
    ∑ d ∈ Ds, Datum.wt d0 d * ‖amp R d (BBne (H := H))‖ ^ 2 ≤
        P.Hp ^ (C1 * (r + 1) ^ 2) * (((qF F : ℕ) : ℝ) ^ (k - 2 * r - 5))⁻¹ * (nn R d0).toReal ∧
      ∑ d ∈ Ds, Datum.wt d0 d * ‖amp R d (fun t => ¬ BBne (H := H) t)‖ ^ 2 ≤
        P.Hp ^ (C1 * (r + 1) ^ 2) * (nn R d0).toReal := by
  obtain ⟨h1, h2, -, -⟩ := hNG R d0
  have hq : (0 : ℝ) ≤ ((qF F : ℕ) : ℝ) := Nat.cast_nonneg _
  have eC : ((C1 : ℕ) : ℝ) * ((r : ℝ) + 1) ^ 2 = ((C1 * (r + 1) ^ 2 : ℕ) : ℝ) := by push_cast; ring
  have hk' : ((k - 2 * r - 5 : ℕ) : ℝ) = (k : ℝ) - 2 * r - 5 := by
    have e1 : k - 2 * r - 5 + (2 * r + 5) = k := by omega
    have e2 := congrArg (Nat.cast (R := ℝ)) e1
    push_cast at e2
    linarith
  have eK : -((k : ℝ) - 2 * r - 5) = -((k - 2 * r - 5 : ℕ) : ℝ) := by rw [hk']
  rw [eC, Real.rpow_natCast] at h1 h2
  rw [eK, Real.rpow_neg hq, Real.rpow_natCast] at h1
  have hX1 : 0 ≤ P.Hp ^ (C1 * (r + 1) ^ 2) * (((qF F : ℕ) : ℝ) ^ (k - 2 * r - 5))⁻¹ :=
    mul_nonneg (pow_nonneg hHp _) (inv_nonneg.mpr (pow_nonneg hq _))
  have hX2 : 0 ≤ P.Hp ^ (C1 * (r + 1) ^ 2) := pow_nonneg hHp _
  constructor
  · have h3 := real_sum_le R d0 _ Ds hD h1 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hn)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hX1] at h3
  · have h3 := real_sum_le R d0 _ Ds hD h2 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hn)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hX2] at h3

end Gen

section Fam

variable {D : D7}

structure LocFam (Z : LocDat D) (Cl Nu : Type) where
  P : Finset (PlF D)
  Om : Finset {p // p ∈ P}
  FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS
  R : ∀ p : PlF D, LocNG.Reps (FP p)
  d0 : ∀ p : PlF D, LocNG.Datum (FP p)
  Ds : ∀ p : PlF D, Finset (LocNG.Datum (FP p))
  ngenL : PlF D → ℝ
  V0 : ℝ
  rw : Cl → ℝ
  dat : Cl → Nu → Option (∀ p : {p // p ∈ P}, {d // d ∈ Ds p.1})

def LocFam.toL {Z : LocDat D} {Cl Nu : Type} (Fm : LocFam Z Cl Nu) : PN.LocalNG Cl Nu where
  P := {p // p ∈ Fm.P}
  Om := Fm.Om
  D p := {d // d ∈ Fm.Ds p.1}
  wt p d := LocNG.Datum.wt (Fm.d0 p.1) d.1
  aN p d := LocNG.amp (Fm.R p.1) d.1 (LocNG.BBne (H := locH Z p.1))
  aZ p d := LocNG.amp (Fm.R p.1) d.1 (fun t => ¬ LocNG.BBne (H := locH Z p.1) t)
  H p := (Fm.FP p.1).Hp
  nn p := (LocNG.nn (Fm.R p.1) (Fm.d0 p.1)).toReal
  ngen p := Fm.ngenL p.1
  q p := LocNG.qF (D.s.atP p.1).Fp
  V0 := Fm.V0
  rw := Fm.rw
  dat := Fm.dat

theorem ngAt_toL {Z : LocDat D} {Cl Nu : Type} (Fm : LocFam Z Cl Nu) (C1 : ℕ) (hk : 2 * D.R.rS + 5 ≤ D.R.k)
    (hNG : ∀ p ∈ Fm.P, LocNG.NGAt D.R.k (Fm.FP p) (C1 : ℝ))
    (hD : ∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) (hn : ∀ p ∈ Fm.P, LocNG.nn (Fm.R p) (Fm.d0 p) ≠ ⊤)
    (hH : ∀ p ∈ Fm.P, 0 ≤ (Fm.FP p).Hp) : Fm.toL.NGAt C1 D.R.rS D.R.k := by
  unfold PN.LocalNG.NGAt
  refine ⟨fun p _ => ?_, ?_⟩
  · have h1 := (ngAt_real D.R.k C1 hk (hNG p.1 p.2) (Fm.R p.1) (Fm.d0 p.1) (Fm.Ds p.1) (hD p.1 p.2)
      (hn p.1 p.2) (hH p.1 p.2)).1
    rw [← Finset.sum_coe_sort (Fm.Ds p.1)] at h1
    exact h1
  · intro p
    have h1 := (ngAt_real D.R.k C1 hk (hNG p.1 p.2) (Fm.R p.1) (Fm.d0 p.1) (Fm.Ds p.1) (hD p.1 p.2)
      (hn p.1 p.2) (hH p.1 p.2)).2
    rw [← Finset.sum_coe_sort (Fm.Ds p.1)] at h1
    exact h1

def FamOK {Z : LocDat D} {τ : Type} {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (γ : PN.Pts D.host.E D.R.rS) (S : Finset (Cl × Nu)) (C0n : ℕ) (AAre : ℝ)
    (Fm : LocFam Z Cl Nu) : Prop :=
  (∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta (Z.M p))) ∧
  (∀ p ∈ Fm.P, ∃ (d : LocNG.Datum (Fm.FP p)) (t : Formalism.MainNotions.S.Loc.Term (Vp D p) (Z.M p) D.R.rS),
    LocNG.IsTermOver (Fm.FP p) d t) ∧
  (∀ p : {p // p ∈ Fm.P}, p ∈ Fm.Om ↔ ¬ (Fm.FP p.1).PrimeTo) ∧
  (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) ∧ (∀ p ∈ Fm.P, LocNG.nn (Fm.R p) (Fm.d0 p) ≠ ⊤) ∧
  0 ≤ Fm.V0 ∧ (∀ c, 0 ≤ Fm.rw c) ∧ Fm.toL.MassRatioAt C0n D.R.rS ∧ Fm.toL.Unfold ∧
  (∀ x ∈ S, N.a2 x.1 γ x.2 = Fm.toL.a2 x.1 x.2) ∧ N.Hh γ = Fm.toL.Htot ∧
  0 < Fm.toL.ngenTot ∧ Fm.toL.ngenTot ≤ AAre * 2 * N.Hh γ ^ PN.eN D.R.rS * N.n γ

def a2W {Cl Nu : Type} (L : PN.LocalNG Cl Nu) (amp : (∀ p, L.D p) → ℂ) (c : Cl) (ν : Nu) : ℝ :=
  match L.dat c ν with
  | none => 0
  | some d => L.rw c * ‖amp d‖ ^ 2

theorem localAmplitudeSq_eq_weighted {Cl Nu : Type} (L : PN.LocalNG Cl Nu) (c : Cl) (ν : Nu) : L.a2 c ν = a2W L L.ampNG c ν := rfl

def FamOKS {Z : LocDat D} {τ : Type} {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (γ : PN.Pts D.host.E D.R.rS) (S : Finset (Cl × Nu)) (C0n : ℕ) (AAre : ℝ)
    (amp : ∀ L : PN.LocalNG Cl Nu, (∀ p, L.D p) → ℂ) (Fm : LocFam Z Cl Nu) : Prop :=
  (∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta (Z.M p))) ∧
  (∀ p ∈ Fm.P, ∃ (d : LocNG.Datum (Fm.FP p)) (t : Formalism.MainNotions.S.Loc.Term (Vp D p) (Z.M p) D.R.rS),
    LocNG.IsTermOver (Fm.FP p) d t) ∧
  (∀ p : {p // p ∈ Fm.P}, p ∈ Fm.Om ↔ ¬ (Fm.FP p.1).PrimeTo) ∧
  (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) ∧ (∀ p ∈ Fm.P, LocNG.nn (Fm.R p) (Fm.d0 p) ≠ ⊤) ∧
  0 ≤ Fm.V0 ∧ (∀ c, 0 ≤ Fm.rw c) ∧ Fm.toL.MassRatioAt C0n D.R.rS ∧ Fm.toL.Unfold ∧
  (∀ x ∈ S, N.a2 x.1 γ x.2 = a2W Fm.toL (amp Fm.toL) x.1 x.2) ∧ N.Hh γ = Fm.toL.Htot ∧
  0 < Fm.toL.ngenTot ∧ Fm.toL.ngenTot ≤ AAre * 2 * N.Hh γ ^ PN.eN D.R.rS * N.n γ

theorem famOK_iff {Z : LocDat D} {τ : Type} {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (γ : PN.Pts D.host.E D.R.rS) (S : Finset (Cl × Nu)) (C0n : ℕ) (AAre : ℝ)
    (Fm : LocFam Z Cl Nu) : FamOK N γ S C0n AAre Fm ↔ FamOKS N γ S C0n AAre (fun L => L.ampNG) Fm := by
  unfold FamOK FamOKS
  simp only [localAmplitudeSq_eq_weighted]

theorem localLe_of_fam {Z : LocDat D} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (C1 C0n : ℕ) (AAre : ℝ) (hk : 2 * D.R.rS + 5 ≤ D.R.k)
    (hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS (C1 : ℝ))
    (h : ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ Fm : LocFam Z Cl Nu, FamOK N γ S C0n AAre Fm) :
    LocalInputLe X N C1 C0n D.R.k AAre := by
  intro γ hγ S
  obtain ⟨Fm, hR, hex, hOm, hD, hn, hV0, hrw, hM, hU, ha, hH, hpos, hle⟩ := h γ hγ S
  have hrank : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    intro p
    rw [finrank_Vp]
    have h1 := D.R.r_eq
    have h2 : 2 * D.R.rS + 2 = D.R.m := by
      have hm2 := D.R.two_le_m
      obtain ⟨j, hj⟩ := D.R.m_even
      simp only [Formalism.BasicNotions.Ranks.rS]; omega
    omega
  have hNG : ∀ p ∈ Fm.P, LocNG.NGAt D.R.k (Fm.FP p) (C1 : ℝ) := fun p hp =>
    hQ (D.s.atP p).Fp (D.s.atP p).Ep (Z.M p) (Z.agree p).1 (Vp D p) (locH Z p) (hrank p) (Fm.FP p) (hR p hp)
  have hq2 : ∀ p ∈ Fm.P, 2 ≤ LocNG.qF (D.s.atP p).Fp := fun p hp => Formalism.MainNotions.KappaEndpoints.two_le_residue_card (Z.agree p).1
  have hqH : ∀ p ∈ Fm.P, ¬ (Fm.FP p).PrimeTo → (LocNG.qF (D.s.atP p).Fp : ℝ) ≤ (Fm.FP p).Hp := fun p hp hpr =>
    Formalism.L2.SG.Pf.residue_le_height_nonprime (Z.agree p).1 (hR p hp) (hex p hp) hpr
  have hH1 : ∀ p ∈ Fm.P, 1 ≤ (Fm.FP p).Hp := by
    intro p hp
    by_cases hpr : (Fm.FP p).PrimeTo
    · exact le_of_eq ((hNG p hp (Fm.R p) (Fm.d0 p)).2.2.2 hpr).1.symm
    · have h2 : (2 : ℝ) ≤ (LocNG.qF (D.s.atP p).Fp : ℝ) := by exact_mod_cast hq2 p hp
      linarith [hqH p hp hpr]
  have hHp : ∀ p ∈ Fm.P, 0 ≤ (Fm.FP p).Hp := fun p hp => le_trans zero_le_one (hH1 p hp)
  have hB : Fm.toL.Basic := by
    refine ⟨fun p d => ?_, fun p => hH1 p.1 p.2, fun p => hq2 p.1 p.2, fun p hp => hqH p.1 p.2 ((hOm p).1 hp),
      fun p => ENNReal.toReal_nonneg, hV0, hrw⟩
    show 0 ≤ LocNG.Datum.wt (Fm.d0 p.1) d.1
    unfold LocNG.Datum.wt LocNG.volRel
    positivity
  exact ⟨Fm.toL, hB, ngAt_toL Fm C1 hk hNG hD hn hHp, hM, hU, ha, hH, hpos, hle⟩

end Fam

section Step

def zOf {D : D7} {X : HidaSetting D} (Y : Full X) : LocDat D := ⟨Y.δ, Y.M, Y.agree⟩

def StepFamC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        ∀ γ, PN.IsPt (Y.tO u u') (NOf2 Y u u' (sc s ν) ν (fun _ => 0)) γ →
          ∀ S : Finset (Set (TauC Y u u') × NuC D), ∃ Fm : LocFam (zOf Y) (Set (TauC Y u u')) (NuC D),
            FamOK (NOf2 Y u u' (sc s ν) ν (fun _ => 0)) γ S C0n
              (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA) Fm

theorem stepLocPinnedC_of_fam (hQ5 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39) (hF : StepFamC) : StepLocPinnedC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C0n, CSt, hCSt, a₀, b₀, h2⟩ := hF Cg cb Cw cT CT C0
  refine ⟨39, C0n, CSt, hCSt, a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hBk ν hν => ?_⟩
  obtain ⟨s, hs1, hs0, hsb, hL⟩ := h2 C' Cl e1 e2 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat
    Ire hBk ν hν
  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := by
    obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH
    dsimp only at hH
    obtain ⟨-, -, h3, h4, -⟩ := hH
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have : 2 * D.R.m + 3 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left hm2 3]
    omega
  have hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS ((39 : ℕ) : ℝ) := by
    have := hQ5 D hk4
    exact_mod_cast this
  exact ⟨s, hs1, hs0, hsb, localLe_of_fam _ _ 39 C0n _ (by omega) hQ hL⟩

theorem rowNGC_of_fam (hR : PN.RowNGJoint) (hCh : PN.NGChain) (hQ5 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39) (hX : NondegenerateGramTuple)
    (hB : StepChoiceConstantsC) (hE : StepPinExists) (hT0 : StepTermVanish) (hF : StepFamC) (hT : StepThmBPinnedC)
    (hQ : CorankOneEquivalence) (hN : StepNormals) (hP : StepPoints) (hO : StepNormOne) : RowNGC := by
  exact rowNGC_of_loc hR hCh hX hB hE hT0 (stepLocPinnedC_of_fam hQ5 hF) hT hQ hN hP hO

end Step

end Formalism.L2.SG.NGLocModel
