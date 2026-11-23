import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcArith
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FieldDictionaryHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AssembleM

noncomputable section

namespace Formalism.L2.SG.Pf.NcArithG

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets MeasureTheory NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem rm_eq (D : D7) : D.R.m = 2 * (D.R.rS + 1) := by
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  show D.R.m = 2 * (D.R.m / 2 - 1 + 1)
  omega

theorem cMass_succ {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (k : ℕ) (hk : 2 ≤ k) :
    Formalism.L2.SG.Pf.Cnt.cMass K F k = Formalism.L2.SG.Pf.Cnt.cMass K F (k - 1) * Formalism.HermitianLatticesTheory.massRatioRightSide K k := by
  unfold Formalism.L2.SG.Pf.Cnt.cMass
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Finset.prod_Icc_succ_top (by omega), Nat.add_sub_cancel, mul_assoc]

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncValueC_of_global (a' Ω ATyp A' AT PT : ℝ)
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (ha : 0 < a') (hATyp : 0 < ATyp) (hA' : 0 < A') (hPT : 0 < PT)
    (hS : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' * Ω)
    (hR : Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Module.finrank ℚ D.host.F) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Module.finrank ℚ D.host.F *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Module.finrank ℚ D.host.F : ℕ) : ℤ)) *
        |(NumberField.discr D.host.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3))
    (hG1 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ =
      |(NumberField.discr D.host.F : ℝ)| ^ (((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3) *
        ((Lat.gS D : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3) * Module.finrank ℚ D.host.F))
    (hG2 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnat /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK =
      ((Lat.gS D : ℕ) : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) * Module.finrank ℚ D.host.F : ℕ) : ℤ)) /
        ATyp)
    (hG3 : Ω = |(NumberField.discr D.host.F : ℝ)| ^
        (-((D.R.r : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2)) * A')
    (hG4 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al * ATyp = AT * A')
    (hG5 : AT * ∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i = PT)
    (hRM : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ =
      Formalism.L2.SG.Pf.Cnt.cMass D.host.E D.host.F D.R.k * ((Tw u : ℕ) : ℝ) ^ (D.R.k * Module.finrank ℚ D.host.F) * PT)
    (hV : Formalism.HermitianLatticesTheory.vInv D.host.E =
      |(NumberField.discr D.host.F : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.F) / 2)
    (hfE : Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F)
    (hng : ngFac D = ((Lat.gS D : ℕ) : ℝ) ^ (D.R.m * Module.finrank ℚ D.host.F * (D.R.k - 1))) :
    Formalism.L2.SG.Pf.NcAsm.NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by

  set B := bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq with hB
  obtain ⟨hKc, hFc, -⟩ := Formalism.L2.SG.Pf.Cnt.field_dictionary_holds D
  set dd : ℝ := |(NumberField.discr D.host.F : ℝ)| with hdd
  set f : ℕ := Module.finrank ℚ D.host.F with hfdef
  set k : ℕ := D.R.k with hkdef
  set s : ℕ := D.R.rS with hsdef
  set gg : ℝ := ((Lat.gS D : ℕ) : ℝ) with hgg
  set TT : ℝ := ((Tw u : ℕ) : ℝ) with hTT
  set Lk : ℝ := ∏ i ∈ Finset.Icc (k + 1) D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i with hLk
  have hm : D.R.m = 2 * (s + 1) := rm_eq D
  have hk5 : D.R.m + 3 ≤ k := D.R.m_add_three_le_k
  have hk2 : 2 ≤ k := by omega
  have hr : D.R.r = k + 2 * s + 1 := by
    show D.R.k + D.R.m - 1 = k + 2 * s + 1
    omega
  have hf : 0 < f := Module.finrank_pos
  have hdpos : 0 < dd := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.F)
  have hgpos : 0 < gg := by
    have h0 := (D.host.g_prime 0).pos
    have h1' := (D.host.g_prime 1).pos
    rw [hgg]
    unfold Lat.gS
    exact_mod_cast Nat.mul_pos h0 h1'
  have hTpos : 0 < TT := by rw [hTT]; exact_mod_cast (D.mem u).A.T_prime.pos

  obtain ⟨hp, hKo, hSo, hSo', hMo, hU00o, hH, hH', hHpp, hHpp', hN, hN', hZZ, hPP, hal, -⟩ := hP
  have hKp : ∀ p, 0 < B.μKp p := fun p => (hp p).2.2.2.2.2.1
  have hμK : 0 < B.μK := mul_pos hKo (Finset.prod_pos fun p _ => hKp p)

  have hLkpos : 0 < Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F k := by
    rw [← Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc k hk2]
    exact Formalism.HermitianLattices.Ext.L3.lValEta_pos hKc k hk2
  have hLkk : 0 < Lk := by
    apply Finset.prod_pos
    intro i hi
    have hi2 : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    rw [← Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc i hi2]
    exact Formalism.HermitianLattices.Ext.L3.lValEta_pos hKc i hi2
  have hcm := (Formalism.L2.SG.Pf.Asm.cMass_spec hKc hFc (k - 1) (by omega)).1
  have hIcc : (∏ i ∈ Finset.Icc k D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i) =
      Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F k * Lk := by
    have hIo : Finset.Ioc k D.R.r = Finset.Icc (k + 1) D.R.r := by
      ext i; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [Finset.Icc_eq_cons_Ioc (show k ≤ D.R.r by omega), Finset.prod_cons, hLk, hIo]

  have hvI : 2 * Formalism.HermitianLatticesTheory.vInv D.host.E = dd ^ ((1 : ℝ) / f) := by rw [hV]; ring
  have hvIpos : 0 < Formalism.HermitianLatticesTheory.vInv D.host.E := by
    rw [hV]; positivity
  have hpow1 : (dd ^ ((1 : ℝ) / f)) ^ f = dd := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdpos.le]
    rw [show (1 : ℝ) / f * (f : ℝ) = 1 by field_simp]
    exact Real.rpow_one dd
  have hsq : Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv D.host.E) ^ f) = dd ^ ((1 : ℝ) / 2) := by
    rw [hvI, hpow1, Real.sqrt_eq_rpow]
  have hvk : (Formalism.HermitianLatticesTheory.vInv D.host.E) ^ (k * f) = dd ^ (k : ℝ) / 2 ^ (k * f) := by
    have h2 : Formalism.HermitianLatticesTheory.vInv D.host.E = dd ^ ((1 : ℝ) / f) / 2 := by rw [hV]
    rw [h2, div_pow, pow_mul', hpow1, Real.rpow_natCast]

  set e : ℝ := -(8 * (s : ℝ) ^ 3 + 6 * (s : ℝ) ^ 2 + 6 * k * (s : ℝ) ^ 2 + s) / 3 with he
  set Xe : ℝ := ((s : ℝ) + 1) * (8 * (s : ℝ) ^ 2 + 10 * s + 3) / 3 with hXe
  set e2 : ℝ := (D.R.r : ℝ) * (2 * s + 1) - ((2 * (s : ℝ) + 1) ^ 2) / 2 with he2
  set E1 : ℝ := -((2 * s * (s + 1) * (k - 1) : ℕ) : ℝ) + 1 / 2 - k with hE1
  have hrR : (D.R.r : ℝ) = k + 2 * s + 1 := by rw [hr]; push_cast; ring
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hexp : e = E1 - Xe + e2 := by
    rw [he, hE1, hXe, he2, hrR]
    push_cast
    rw [hk1]
    ring
  have hde : dd ^ e = dd ^ E1 * (dd ^ Xe)⁻¹ * dd ^ e2 := by
    rw [hexp, Real.rpow_add hdpos, Real.rpow_sub hdpos, div_eq_mul_inv]
  have hdE1 : dd ^ E1 = dd ^ ((-((2 * s * (s + 1) * (k - 1) : ℕ) : ℤ) : ℤ) : ℝ) * dd ^ ((1 : ℝ) / 2) *
      (dd ^ (k : ℝ))⁻¹ := by
    rw [hE1, ← Real.rpow_neg hdpos.le, ← Real.rpow_add hdpos, ← Real.rpow_add hdpos]
    congr 1
    push_cast
    ring

  have hgc : gg ^ ((s + 1) * (2 * s + 3) * f) * gg ^ (D.R.m * f * (k - 1)) =
      gg ^ ((s + 1) * (2 * k + 2 * s + 1) * f) := by
    rw [← pow_add]
    congr 1
    rw [hm]
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel]
    ring
  have hgpow : gg ^ (-(((s + 1) * (2 * k + 2 * s + 1) * f : ℕ) : ℤ)) =
      (gg ^ ((s + 1) * (2 * k + 2 * s + 1) * f))⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hTpow : TT ^ (-((k * f : ℕ) : ℤ)) = (TT ^ (k * f))⁻¹ := by rw [zpow_neg, zpow_natCast]

  have hal : B.al = AT * A' / ATyp := by rw [eq_div_iff hATyp.ne']; exact hG4
  have hAT : AT = PT / Lk := by rw [eq_div_iff hLkk.ne']; exact hG5
  have hratio : Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E k =
      ((Nat.factorial (k - 1) : ℝ) ^ f * (dd ^ (k : ℝ) / 2 ^ (k * f)) / Real.pi ^ (k * f)) /
        dd ^ ((1 : ℝ) / 2) * Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F k := by
    unfold Formalism.HermitianLatticesTheory.massRatioRightSide
    rw [hfE, hsq, Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc k hk2, mul_pow, ← pow_mul, div_pow, hvk]
    ring
  have hratio_pos : 0 < Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E k := Formalism.HermitianLattices.Ext.L3.massRatio_pos hKc k hk2

  have hKrat : B.μKnat / B.μH' = (B.μKnat / B.μK) * (Ω / a') := by
    have h1 : B.μK / B.μH' = Ω / a' := by
      rw [div_eq_div_iff hH'.ne' ha.ne']
      linarith [hS]
    rw [← h1]
    field_simp
  unfold Formalism.L2.SG.Pf.NcAsm.NcValueC
  rw [← hB]
  calc _ = dd ^ E1 * 2 ^ (k * f) * (Real.pi ^ k / (Nat.factorial (k - 1) : ℝ)) ^ f * TT ^ (-((k * f : ℕ) : ℤ)) *
          A' / ATyp := by
        unfold Formalism.L2.SG.Pf.Cnt.cExpl
        try rw [← hdd]
        try rw [← hfdef]
        try rw [← hkdef]
        try rw [← hsdef]
        rw [hIcc, hRM, cMass_succ k hk2, hratio, hal, hAT, hdE1,
          ← Real.rpow_intCast dd, hTpow, div_pow, ← pow_mul]
        have hpi : 0 < Real.pi := Real.pi_pos
        have hfac : (0 : ℝ) < (Nat.factorial (k - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
        field_simp
    _ = Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat / B.μH' *
          ngFac D := by
        rw [show Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat /
            B.μH' * ngFac D = (Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * B.volH * B.volN * B.volN') *
            (B.unitLevelVolume / B.volZZ) * (B.μKnat / B.μH') * ngFac D by ring]
        rw [hR, hG1, hKrat, hG2, hG3, hng]
        try rw [← hdd]
        try rw [← hfdef]
        try rw [← hkdef]
        try rw [← hsdef]
        try rw [← hgg]
        try rw [← hTT]
        rw [hde, hgpow, Real.rpow_neg hdpos.le]
        rw [← hgc]
        have hX : 0 < dd ^ Xe := Real.rpow_pos_of_pos hdpos _
        have he2p : 0 < dd ^ e2 := Real.rpow_pos_of_pos hdpos _
        have hgA : 0 < gg ^ ((s + 1) * (2 * s + 3) * f) := pow_pos hgpos _
        have hgC : 0 < gg ^ (D.R.m * f * (k - 1)) := pow_pos hgpos _
        field_simp

end Formalism.L2.SG.Pf.NcArithG
