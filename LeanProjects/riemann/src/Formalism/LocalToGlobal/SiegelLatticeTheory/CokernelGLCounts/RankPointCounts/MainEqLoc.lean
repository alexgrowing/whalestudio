import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqAna

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf.MainEqLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocalInputLeG {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {E : Type} [Field E] {r : ℕ}
    {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu) (C1 C0 : ℕ) (AAre : ℝ) : Prop :=
  ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ L : PN.LocalNG Cl Nu, L.Basic ∧ ZAt L C1 r ∧
    L.MassRatioAt C0 r ∧ L.Unfold ∧ (∀ x ∈ S, N.a2 x.1 γ x.2 = weightedGenericAmplitudeSq L x.1 x.2) ∧ N.Hh γ = L.Htot ∧
    0 < L.ngenTot ∧ L.ngenTot ≤ AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ

theorem localInputG_of_le {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {E : Type} [Field E] {r : ℕ}
    {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu) (C1 C0 : ℕ) (AAre : ℝ) (h : LocalInputLeG X N C1 C0 AAre)
    (hng : ∀ γ, N.ngen γ = AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ) : LocalInputG X N C1 C0 := by
  intro γ hγ S
  obtain ⟨L, hB, hZ, hM, hU, ha, hH, hpos, hle⟩ := h γ hγ S
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ / L.ngenTot := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by
    rw [hc, le_div_iff₀ hpos, one_mul]
    exact hle
  have hV0 : 0 ≤ L.V0 := hB.2.2.2.2.2.1
  refine ⟨{ L with V0 := L.V0 * c }, ?_, hZ, hM, ?_, ?_, hH, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hB
    unfold Formalism.FourierDecayAlt.PN.LocalNG.Basic
    exact ⟨h1, h2, h3, h4, h5, mul_nonneg h6 (by linarith), h7⟩
  · intro d S' hS'
    have h0 := hU d S' hS'
    have hw : 0 ≤ L.V0 * ∏ p, L.wt p (d p) :=
      mul_nonneg hV0 (Finset.prod_nonneg fun p _ => hB.1 p (d p))
    calc ∑ x ∈ S', L.rw x.1 ≤ L.V0 * ∏ p, L.wt p (d p) := h0
      _ ≤ L.V0 * c * ∏ p, L.wt p (d p) := by nlinarith
  · intro x hx
    rw [ha x hx]
    first
      | rfl
      | (unfold Formalism.L2.SG.Pf.MainEqCut.weightedGenericAmplitudeSq Formalism.L2.SG.Pf.MainEqCut.ampGen; rfl)
      | (cases hd : L.dat x.1 x.2 <;> simp [Formalism.L2.SG.Pf.MainEqCut.weightedGenericAmplitudeSq, Formalism.L2.SG.Pf.MainEqCut.ampGen, hd])
  · show N.ngen γ = L.V0 * c * ∏ p, L.ngen p
    rw [hng γ]
    have e : L.ngenTot = L.V0 * ∏ p, L.ngen p := rfl
    have hne : L.ngenTot ≠ 0 := hpos.ne'
    rw [show L.V0 * c * ∏ p, L.ngen p = L.ngenTot * c by rw [e]; ring, hc, mul_div_assoc',
      mul_div_cancel_left₀ _ hne]

def StepLocPinnedG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
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
        LocalInputLeG (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν (fun _ => 0)) C1 C0n
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)

end Formalism.L2.SG.Pf.MainEqLoc

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqLoc

theorem stepLocGenPinnedG_of_loc (h : StepLocPinnedG) : StepLocGenPinnedG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, CSt, hCSt, C'₀, Cl₀, H⟩ := h Cg cb Cw cT CT C0
  refine ⟨C1, C0n, CSt, hCSt, C'₀, Cl₀, ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hpin
  obtain ⟨s, hs1, hs2, hs3, hloc⟩ :=
    H C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hpin
  let AAre : ℝ := PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA
  let N0 := NOfG Y u (sc s ν) ν (fun _ => 0)
  let ng : PN.Pts D.host.E D.R.rS → ℝ := fun γ => AAre * 2 * N0.Hh γ ^ PN.eN D.R.rS * N0.n γ
  refine ⟨s, ng, 2, hs1, hs2, hs3, by norm_num, le_refl _, ?_, ?_⟩
  · exact localInputG_of_le _ _ C1 C0n AAre hloc (fun γ => rfl)
  · intro γ _
    refine ⟨?_, le_refl _⟩
    change 0 ≤ Formalism.L2.SG.RowsConc.nPt _ _ _ γ
    unfold Formalism.L2.SG.RowsConc.nPt
    apply Finset.prod_nonneg
    intro w _
    apply mul_nonneg
    · exact pow_nonneg (mul_nonneg (inv_nonneg.2 (Even.pow_nonneg (Even.mul_right (even_two_mul _) _) _))
        (w.1.nonneg _)) _
    · apply Finset.prod_nonneg
      intro a _
      exact Even.pow_nonneg (Even.mul_right (even_two_mul _) _) _

end Formalism.L2.SG.Pf
