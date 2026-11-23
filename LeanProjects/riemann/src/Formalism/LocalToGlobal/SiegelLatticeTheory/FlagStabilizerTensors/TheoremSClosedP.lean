import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowFormAllOf

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.SpectralTiesReal

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.RealObj in

def CarrierP : Prop :=
  ∃ C₄ CA₀ : ℝ, 1 ≤ C₄ ∧ ∀ CA : ℝ, CA₀ ≤ CA → 1 ≤ CA →
    ∀ C0 CG CDel cT Cb : ℝ, 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
      (τ : D.what₂.Tau) (Cp Th' : ℝ)
      (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
      (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd C Th : ℝ)
      {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
      (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂),
      Formalism.BasicNotions.Ties D → u ≠ u' → k0 ≤ (gOf D e).k → Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f →
      (∀ x : InfinitePlace D.host.E,
        InfinitePlace.mk ((T.X.B.I.φ (T.X.pl.symm (e x))).comp T.X.ιE.symm.toRingHom) = x) →
      J.SzHyp (gOf D e) CA C0 CG CDel cT Cb L.sc.b Cp Th' (deOf D τ u) (deOf D τ u')
        (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
      (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
      CarrierFull T.X T.hb T.Y u u' X0 T.ψ sd C Th vR Q i0 i0' νq C₄ CA (gOf D e) (deOf D τ u) (deOf D τ u')
        (lOf D (deOf D τ u) (deOf D τ u'))

open Formalism.L2.SG.AdBridge Formalism.L2.SG.CntLocal Formalism.L2.SG.DataInst Formalism.L2.SG.RowsConc in

theorem theoremS_rec2P
    (hLMA : ∀ D : D7, LocalModelAt D) (hDIA : ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → DensInputAt D) (hRIA : ∀ D : D7, RowsInputP D)
    (hNG : Formalism.L2.SG.RowsPos.RowNGP)
    (C₄ Cthr : ℝ) (h4 : 1 ≤ C₄) :
    ∃ CA C : ℝ, Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (hF : FinX T.Y) (u u' : D.what₂.Word)
      (G0 : Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ)
      (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
      (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E)
      (Lsp : LocSp D T.Y.M) (ϖ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, 𝒪[(D.s.atP p).Fp])
      (κ : Formalism.L2.SG.TermDef.Term D u u' (T.X.Fu u) (T.Y.what₂ u) → ℕ)
      (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u)) (nc Th Cp Cf : ℝ),
      Formalism.BasicNotions.Ties D → u ≠ u' → 0 ≤ L.sc.b →

      CarrierFull T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq C₄ CA G0 de de' l →
      Fintype.card (InfinitePlace T.X.B.I.F) = D.R.f →

      k0 ≤ G0.k →
      J.SzHyp G0 CA C0 CG CDel cT Cb L.sc.b Cp Th de de' (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') l →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log L.sc.b ≤ G0.f * Real.log G0.k →
      2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k →
      PB.SizeNumbers G0.k G0.r G0.f L.sc.b G0.g1 G0.g2 (1 / 3) Cn →
      (G0.size de (D.mem u).A.T (D.duS u)).Dstar = D.what₂.Dstar →

      (T.Y.tO u u').RowBig (epsL D) (ddC T.X T.Y u u') → (T.Y.tO u u').RowNotScalar (epsL D) (ddC T.X T.Y u u') →
      Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f →
      Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (T.Y.tO u u').AbsConv →

      (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
      (∀ p, Irreducible (ϖ p)) → Formula T.Y.δ Lsp u u' (T.X.Fu u) (T.Y.what₂ u) nc → RowLabel κ →
      RowsSum (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) κ (nc * ∏' p, alpD u u' p)
        (Formalism.L2.SG.RealObj.VtPt T.X u u' 1 i0 i0' (T.Y.FN u) (T.Y.FN u') νq) →

      Formalism.L2.SG.MassDataForm.RowFormC T.X T.hb T.Y u u' X0 T.ψ
        (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq κ nc →
      PB.MassDataHyp (massDataY T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
          (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq) →
      PB.Link (T.Y.tO u u') (massDataY T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
          (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq)
        G0 de (D.mem u).A.T (D.duS u) (D.duS u') →
      PB.SplitInputs (T.Y.tO u u') (massDataY T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p)
          C Th (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq).tt →

      Formalism.L2.SG.TermOp.KExpansion (T.X.Fu u) (T.X.Fu u') (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u') T.Y.hK
        (T.Y.Dt u) (T.Y.Dt u') →
      Formalism.L2.SG.TermOp.AbsConvT (T.X.Fu u) (T.X.Fu u') T.Y.TR (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u') →
      (T.Y.tO u u').IdDegenerate → (T.Y.tO u u').part (T.Y.tO u u').degSet = 0 →
      ‖(T.Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u') / D.what₂.Dstar) ∧
      L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar := by
  obtain ⟨CA, C, h1, h2, h3, h5, hrest⟩ := theoremS_rec hLMA hDIA hRIA C₄ Cthr h4
  refine ⟨CA, C, h1, h2, h3, h5, fun C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6 => ?_⟩
  obtain ⟨k0, hk⟩ := hrest C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  refine ⟨k0, fun Cg cb Cw cTf CT C0f hcb hcT => ?_⟩
  obtain ⟨C4, hC4, CN'₀, ClN₀, hN⟩ := hNG Cg cb Cw cTf CT C0f hcb hcT
  refine ⟨C4, CN'₀, ClN₀, hC4, fun C' Cl hC' hCl => ?_⟩
  intro D L T hF u u' G0 de de' l i0 i0' νq X0 Lsp ϖ κ Q nc Th Cp Cf hTies hne hb0 hCar hcard hk0 hSz h16 hCf hsize
    hSN hDst hRB hRNS hHyp0 hStand hCT hAC hTT hϖ hFo hκ hSum hKVI hBI hLink hSplit hE hA hId hK2
  have hGk : G0.k = D.R.k ∧ G0.r = D.R.rS ∧ G0.f = D.R.f := by
    have hCar' := hCar
    obtain ⟨Wp, Wq, i1, i2, i3, i4, i5, S, _, _, _, _, _, _, _, _, _, -, hG, -, -, -, hC, -⟩ := hCar'
    subst hG
    exact ⟨hC.2.1, hC.1, glob_f_eq S hC⟩
  have hdd : ddC T.X T.Y u u' = (D.duS u : ℝ) * D.duS u' / (G0.size de (D.mem u).A.T (D.duS u)).Dstar := by
    unfold ddC
    rw [hCT.2.2.1 u, hCT.2.2.1 u', hCT.2.2.2.1, hDst]
  have hRNG := hN C' Cl hC' hCl D L T.X T.Y u u' hTies hHyp0 hStand hCT hAC
  have hLTr : Formalism.L2.SG.Pf.LocCP.LocTied D := by
    obtain ⟨_, _, _, _, _, _, _, h⟩ := hCT.2.2.2.2.2.2.1
    exact h
  rw [hdd] at hRB hRNS hRNG
  refine hk D L T.X T.hb T.Y hF u u' G0 de de' l i0 i0' νq X0 T.ψ Lsp ϖ κ Q nc Th Cp Cf (1 / 3) C4 hne
    ⟨T.hI hF⟩ hb0 hCar hcard hk0 hSz h16 hCf hsize hTT (Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hStand) hLTr hϖ hFo hκ hSum hKVI hBI hLink hSplit hSN ?_ ?_ ?_ hDst hE hA
    hId hK2
  · rw [hGk.1, hGk.2.2]
    exact hRB
  · rw [hGk.1, hGk.2.2]
    exact hRNS
  · rw [hGk.1, hGk.2.1, hGk.2.2]
    exact hRNG

open Formalism.L2.SG.AdBridge Formalism.L2.SG.CntLocal Formalism.L2.SG.DataInst Formalism.L2.SG.RowsConc in

theorem theoremS_rec3P
    (hLMA : ∀ D : D7, LocalModelAt D) (hDIA : ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → DensInputAt D) (hRIA : ∀ D : D7, RowsInputP D)
    (hNG : Formalism.L2.SG.RowsPos.RowNGP) (hCar : CarrierP) (Cthr : ℝ) :
    ∃ C₄ CA C : ℝ, 1 ≤ C₄ ∧ Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (hF : FinX T.Y) (u u' : D.what₂.Word)
      (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (τ : D.what₂.Tau)
      (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
      (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E)
      (Lsp : LocSp D T.Y.M) (ϖ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, 𝒪[(D.s.atP p).Fp])
      (κ : Formalism.L2.SG.TermDef.Term D u u' (T.X.Fu u) (T.Y.what₂ u) → ℕ)
      (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u)) (nc Th Cp Cf : ℝ),
      Formalism.BasicNotions.Ties D → u ≠ u' → 0 ≤ L.sc.b →

      (∀ v, i0 v = i0' v) → Formalism.L2.SG.RealObj.PtRepExists T.X u u' 1 i0 i0' → Formalism.L2.SG.RealObj.NuQPin T.X u u' νq →
      (∀ x : InfinitePlace D.host.E,
        InfinitePlace.mk ((T.X.B.I.φ (T.X.pl.symm (e x))).comp T.X.ιE.symm.toRingHom) = x) →
      Fintype.card (InfinitePlace T.X.B.I.F) = D.R.f →

      k0 ≤ (gOf D e).k →
      J.SzHyp (gOf D e) CA C0 CG CDel cT Cb L.sc.b Cp Th (deOf D τ u) (deOf D τ u') (D.mem u).A.T (D.mem u').A.T
        (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log L.sc.b ≤ (gOf D e).f * Real.log (gOf D e).k →
      2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k →
      PB.SizeNumbers (gOf D e).k (gOf D e).r (gOf D e).f L.sc.b (gOf D e).g1
        (gOf D e).g2 (1 / 3) Cn →
      ((gOf D e).size (deOf D τ u) (D.mem u).A.T (D.duS u)).Dstar = D.what₂.Dstar →

      (T.Y.tO u u').RowBig (epsL D) (ddC T.X T.Y u u') → (T.Y.tO u u').RowNotScalar (epsL D) (ddC T.X T.Y u u') →
      Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f →
      Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (T.Y.tO u u').AbsConv →

      (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
      (∀ p, Irreducible (ϖ p)) → Formula T.Y.δ Lsp u u' (T.X.Fu u) (T.Y.what₂ u) nc → RowLabel κ →
      RowsSum (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) κ (nc * ∏' p, alpD u u' p)
        (Formalism.L2.SG.RealObj.VtPt T.X u u' 1 i0 i0' (T.Y.FN u) (T.Y.FN u') νq) →

      Formalism.L2.SG.MassDataForm.RowFormC T.X T.hb T.Y u u' X0 T.ψ
        (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq κ nc →
      PB.MassDataHyp (massDataY T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p)
          C Th (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq) →
      PB.Link (T.Y.tO u u') (massDataY T.X T.hb T.Y u u' X0 T.ψ
          (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
          (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq)
        (gOf D e) (deOf D τ u) (D.mem u).A.T (D.duS u) (D.duS u') →
      PB.SplitInputs (T.Y.tO u u') (massDataY T.X T.hb T.Y u u' X0 T.ψ
          (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
          (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq).tt →

      Formalism.L2.SG.TermOp.KExpansion (T.X.Fu u) (T.X.Fu u') (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u') T.Y.hK
        (T.Y.Dt u) (T.Y.Dt u') →
      Formalism.L2.SG.TermOp.AbsConvT (T.X.Fu u) (T.X.Fu u') T.Y.TR (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u') →
      (T.Y.tO u u').IdDegenerate → (T.Y.tO u u').part (T.Y.tO u u').degSet = 0 →
      ‖(T.Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u') / D.what₂.Dstar) ∧
      L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar := by
  obtain ⟨C₄, CA₀, h4, hC⟩ := hCar
  obtain ⟨CA, C, h1, h2, h3, h5, hrest⟩ := theoremS_rec2P hLMA hDIA hRIA hNG C₄ (max Cthr CA₀) h4
  refine ⟨C₄, CA, C, h4, le_trans (le_max_left _ _) h1, h2, h3, h5, fun C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6 => ?_⟩
  obtain ⟨k0, hk⟩ := hrest C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  obtain ⟨k0c, hCk⟩ := hC CA (le_trans (le_max_right _ _) h1) h2 C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  refine ⟨max k0 k0c, fun Cg cb Cw cTf CT C0f hcb hcT => ?_⟩
  obtain ⟨Cn, C'₀, Cl₀, hCn, hrow⟩ := hk Cg cb Cw cTf CT C0f hcb hcT
  obtain ⟨C'₁, Cl₁, hCc⟩ := hCk Cg cb Cw cTf CT C0f hcb hcT
  refine ⟨Cn, max C'₀ C'₁, max Cl₀ Cl₁, hCn, fun C' Cl hC' hCl => ?_⟩
  intro D L T hF u u' e τ i0 i0' νq X0 Lsp ϖ κ Q nc Th Cp Cf hTies hne hb0 hii hPt hNu hPT hcard hk0 hSz h16 hCf hsize hSN
    hDst hRB hRNS hHyp0 hStand hCT hAC hTT hϖ hFo hκ hSum hKVI hBI hLink hSplit hE hA hId hK2
  have hCF := hCc C' Cl (le_trans (le_max_right _ _) hC') (le_trans (le_max_right _ _) hCl) D L T u u' e τ Cp Th i0 i0' νq X0
    (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
    (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q hTies hne (le_trans (le_max_right _ _) hk0) hHyp0 hPT
    hSz hii hPt hNu
  exact hrow C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_left _ _) hCl) D L T hF u u' (gOf D e) (deOf D τ u)
    (deOf D τ u') (lOf D (deOf D τ u) (deOf D τ u')) i0 i0' νq X0 Lsp ϖ κ Q nc Th Cp Cf hTies hne hb0 hCF hcard
    (le_trans (le_max_left _ _) hk0) hSz h16 hCf hsize hSN hDst hRB hRNS hHyp0 hStand hCT hAC hTT hϖ hFo hκ hSum hKVI hBI
    hLink hSplit hE hA hId hK2

def VIndepAtAllP : Prop :=
  ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k)
      (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf),
      Formalism.BasicNotions.Ties D → u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (∀ v, i0 v = i0' v) →
      NuQPin T.X u u' νq → PtRepExists T.X u u' 1 i0 i0' → Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f →
      Formalism.L2.SG.Pf.RowForm.VIndepAtC T.X u u' i0 i0' νq 1

def RowFormAllP : Prop :=
  ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E)
      (C Th : ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u))
      (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf) (Lsp : LocSp D T.Y.M)
      (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (κ : Formalism.L2.SG.TermDef.Term D u u' (T.X.Fu u) (T.Y.what₂ u) → ℕ),
      Formalism.BasicNotions.Ties D → Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f →
      u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (∀ i, 3 ≤ D.host.g i) →
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE T.X.B.I.cm.sig T.X.B.I.J X0).det ≠ 0 →
      2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
      (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
      RowLabel κ → (∀ p, Irreducible (ϖ p)) →
      Formalism.L2.SG.MassDataForm.RowFormC T.X T.hb T.Y u u' X0 T.ψ
        (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq κ
        (Formalism.L2.SG.Pf.Cnt.cExpl D (T.X.Fu u) (T.Y.what₂ u))

theorem rowFormAllP_of (hFC : FormulaC) (hVP : Formalism.L2.SG.VolPin.VolumeOddGeneric) (hVA : VIndepAtAllP) (hNc : NormalizingConstantPositiveAll) :
    RowFormAllP := by
  intro Cg cb Cw cTf CT C0f hcb hcT
  obtain ⟨C'₀, Cl₀, hV⟩ := hVA Cg cb Cw cTf CT C0f hcb hcT
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 => ?_⟩
  intro D L T u u' X0 C Th Q i0 i0' νq Lsp ϖ κ hTies hH0 hne hSt hCT hg3 hdet hk hcong hi hPR hNu hRL hϖ
  have hWD : Formalism.L2.SG.WuDecay.WuDecay T.X := hCT.2.2.2.2.1
  have hAbs : Formalism.L2.SG.TermOp.AbsConvT (T.X.Fu u) (T.X.Fu u') T.Y.TR (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u') :=
    Formalism.L2.SG.Pf.absConvC_outright D T.X T.Y u u'
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u' (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Pf.fundExistsC_holds D T.X T.Y u u')
      (Formalism.L2.SG.Pf.KernelOfEmbedding.ooIntAll_of (Y := T.Y) hWD u u')
  obtain ⟨hN, hc0⟩ := hNc D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hSt hCT hdet hk hcong hi hPR hNu hϖ
  have hP := Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties T.X
  have hV0 : 0 < T.X.volK2 := ENNReal.toReal_pos (ne_of_gt hK2.2.2.1) (ne_of_lt hK2.2.2.2)
  have hLT : Formalism.L2.SG.Pf.LocCP.LocTied D := by
    obtain ⟨_, _, _, _, _, _, _, hL⟩ := hCT.2.2.2.2.2.2.1
    exact hL
  exact Formalism.L2.SG.Pf.rowFormC_of_leaves3 T.X T.hb T.Y u u' X0 T.ψ _ C Th Q i0 i0' νq κ _ hRL hi hPR hNu hk hAbs
    (fun i => ⟨hg3 i, gUnramAll D u u' hSt i⟩) (Formalism.L2.SG.Pf.LiftedPhaseAgreement.phaseTieC_holds T.X T.Y u u' κ hP) hVP hP
    (Formalism.L2.SG.Pf.normRepExists_of (Formalism.L2.SG.Pf.NormRepX.norm_representative_holds D u u' hP)
      (Formalism.L2.SG.Closed.TermFun_holds D u u') (T.Y.rowsOK u))
    (hV C' Cl h1 h2 D L T u u' i0 i0' νq hTies hne hSt hCT hi hNu hPR hH0)
    hN hLT hV0 hc0 (hFC D T u u' Lsp hLT hSt hcong).1 (tprod_alpD_pos D hk u u')

theorem theoremS_closedP
    (hLMA : ∀ D : D7, LocalModelAt D) (hDIA : ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → DensInputAt D) (hRIA : ∀ D : D7, RowsInputP D)
    (hNG : Formalism.L2.SG.RowsPos.RowNGP) (hKpp : KppOffC) (hCar : CarrierP) (hKE : KernelExponentAgreement)
    (hFo : Formalism.L2.SG.Full.FoldOKC) (hO : Formalism.L2.SG.Full.OOIntAllC) (hA : Formalism.L2.SG.Full.AbsConvC)
    (hFX : FinXC) (hWu : Formalism.L2.SG.Pf.WuDecayOfGap)
    (hCh : ChoicesC) (hFC : FormulaC) (hRS : RowsSumC) (hRF : RowFormAllP) (hBI : MassDataHypAll) (hLk : LinkAll) (hSp : SplitAll)
    (Cthr : ℝ) :
    ∃ C₄ CA C : ℝ, 1 ≤ C₄ ∧ Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word), Formalism.BasicNotions.Ties D → u ≠ u' → 0 ≤ L.sc.b →
      SizesAt CA C0 CG CDel cT Cb Cn k0 D L T u u' →
      Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → Formalism.MainNotions.S.Cnt.Stand D u u' →
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D L C' Cl Cg cb Cw cTf CT C0f →
      Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D →
      (T.Y.tO u u').RowBig (epsL D) (ddC T.X T.Y u u') → (T.Y.tO u u').RowNotScalar (epsL D) (ddC T.X T.Y u u') →
      ‖(T.Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u') / D.what₂.Dstar) ∧
      L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar := by
  obtain ⟨C₄, CA, C, h4, h1, h2, h3, h5, hrest⟩ := theoremS_rec3P hLMA hDIA hRIA hNG hCar Cthr
  refine ⟨C₄, CA, C, h4, h1, h2, h3, h5, fun C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6 => ?_⟩
  obtain ⟨k0, hk⟩ := hrest C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  refine ⟨k0, fun Cg cb Cw cTf CT C0f hcb hcT => ?_⟩
  obtain ⟨Cn, C'₀, Cl₀, hCn, hrow⟩ := hk Cg cb Cw cTf CT C0f hcb hcT
  obtain ⟨C'₁, Cl₁, hKz⟩ := hKpp Cg cb Cw cTf CT C0f
  obtain ⟨C'₂, Cl₂, hRFc⟩ := hRF Cg cb Cw cTf CT C0f hcb hcT
  refine ⟨Cn, max (max C'₀ C'₁) C'₂, max (max Cl₀ Cl₁) Cl₂, hCn, fun C' Cl hC' hCl => ?_⟩
  intro D L T u u' hTies hne hb0 hSz hH0 hSt hKH hGap hLT hTF hRB hRNS
  obtain ⟨e, τ, Cp, Th, Cf, hPT, hk0, hSzH, h16, hCf, hsize, hSN, hDst, hTT⟩ := hSz
  have hTh : 0 < Th := hSzH.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hF := hFX D T hGap
  have hWP := hWu D hGap T.X
  have hCT : ConcTie T.X T.Y := T.concTie hF (Formalism.L2.SG.Closed.level_subgroup_properties T.X)
    (fun u => Formalism.L2.SG.Closed.NeatKu_holds (X := T.X) (u := u) T.Y.hK) hWP.1 hWP.2 hLT hTF
  obtain ⟨i0, i0', νq, X0, Lsp, ϖ, κ, Q, hii, hPt, hNu, hdet, hϖ, hκ⟩ := hCh D T u u' hne hSt hTT hsize
  have hFm := hFC D T u u' Lsp hLT hSt hTT
  have hg3 : ∀ i, 3 ≤ D.host.g i := by
    obtain ⟨hb16, hk32, -, -, hg1, hg2, -⟩ := hSN
    have hk : (32 : ℝ) ≤ ((gOf D e).k : ℝ) := by exact_mod_cast hk32
    have h512 : (512 : ℝ) ≤ ((gOf D e).k : ℝ) * L.sc.b := by nlinarith
    have h3 : (3 : ℝ) ≤ (((gOf D e).k : ℝ) * L.sc.b) ^ 8 := by
      have h1 : (1 : ℝ) ≤ ((gOf D e).k : ℝ) * L.sc.b := by linarith
      calc (3 : ℝ) ≤ ((gOf D e).k : ℝ) * L.sc.b := by linarith
        _ ≤ (((gOf D e).k : ℝ) * L.sc.b) ^ 8 := le_self_pow₀ h1 (by norm_num)
    intro i
    fin_cases i
    · have := h3.trans hg1
      exact_mod_cast this
    · have := h3.trans hg2
      exact_mod_cast this
  have hAC := absConvTied_of_full hFo Formalism.L2.SG.Pf.fundExistsC_holds hO hA D T.X T.Y u u' hCT
  have hKZ := hKz C' Cl (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC')
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCl) D L T.X T.Y u u' hKH hCT hne
  have hdeg := Formalism.L2.SG.RowsOther.kppOff_of_termZero (T.Y.tO u u') hKZ
  exact hrow C' Cl (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC')
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCl) D L T hF u u' e τ i0 i0' νq X0 Lsp ϖ κ
    Q (Formalism.L2.SG.Pf.Cnt.cExpl D (T.X.Fu u) (T.Y.what₂ u)) Th Cp Cf hTies hne hb0 hii hPt hNu hPT (cardC_holds D T) hk0 hSzH h16 hCf hsize hSN hDst hRB hRNS hH0 hSt hCT hAC hTT hϖ hFm hκ
    (hRS D T u u' i0 i0' νq Lsp κ hne hSt hCT hg3 hsize hTT hii hPt hNu hκ)
    (hRFc C' Cl (le_trans (le_max_right _ _) hC') (le_trans (le_max_right _ _) hCl) D L T u u' X0 C Th Q i0 i0' νq Lsp ϖ κ
      hTies hH0 hne hSt hCT hg3 hdet hsize hTT hii hPt hNu hκ hϖ)
    (hBI D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hSt hGap hCT hdet h3 hTh hsize hTT hii hPt hNu hϖ)
    (hLk D T u u' e τ X0 C Th Q i0 i0' νq Lsp ϖ hne hSt hCT hdet hDst)
    (hSp D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hSt hCT hg3)
    (hKE D T.X T.Y u u' hCT) hAC (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO T.Y u u') hdeg

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
