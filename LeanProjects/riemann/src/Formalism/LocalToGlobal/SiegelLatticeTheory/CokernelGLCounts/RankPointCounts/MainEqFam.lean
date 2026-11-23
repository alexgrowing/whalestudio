import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc
  Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqLoc

namespace Formalism.L2.SG.Pf.MainEqFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ampG {Cl Nu : Type} (L : PN.LocalNG Cl Nu) (d : ∀ p, L.D p) : ℂ := ∏ p, L.aZ p (d p)

variable {D : D7}

theorem localLeG_of_fam {Z : LocDat D} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (C1 C0n : ℕ) (AAre : ℝ) (hk : 2 * D.R.rS + 5 ≤ D.R.k)
    (hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS (C1 : ℝ))
    (h : ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ Fm : LocFam Z Cl Nu,
      FamOKS N γ S C0n AAre (fun L => ampG L) Fm) :
    LocalInputLeG X N C1 C0n AAre := by
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
  exact ⟨Fm.toL, hB, (ngAt_toL Fm C1 hk hNG hD hn hHp).2, hM, hU, ha, hH, hpos, hle⟩

def StepFamG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        ∀ γ, PN.IsPt (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν (fun _ => 0)) γ →
          ∀ S : Finset (Set (TauC Y u u) × NuC D), ∃ Fm : LocFam (zOf Y) (Set (TauC Y u u)) (NuC D),
            FamOKS (NOfG Y u (sc s ν) ν (fun _ => 0)) γ S C0n
              (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)
              (fun L => ampG L) Fm

end Formalism.L2.SG.Pf.MainEqFam

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqFam

theorem stepLocPinnedG_of_fam (hQ5 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39) (hF : StepFamG) : StepLocPinnedG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C0n, CSt, hCSt, a₀, b₀, h2⟩ := hF Cg cb Cw cT CT C0
  refine ⟨39, C0n, CSt, hCSt, a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hBk ν hν => ?_⟩
  obtain ⟨s, hs1, hs0, hsb, hL⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat
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
  exact ⟨s, hs1, hs0, hsb, localLeG_of_fam _ _ 39 C0n _ (by omega) hQ hL⟩

end Formalism.L2.SG.Pf
