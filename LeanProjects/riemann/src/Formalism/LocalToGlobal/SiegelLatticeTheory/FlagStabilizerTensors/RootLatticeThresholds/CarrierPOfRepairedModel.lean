import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInputExistsRepaired
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSClosedP

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.SpectralTiesReal

open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.RealObj

def CarrierSideBoundPositive (Cb : ℝ) : Prop :=
  ∀ C₆ Cc : ℝ, 0 < C₆ → ∃ CA₀ : ℝ, ∀ CA : ℝ, CA₀ ≤ CA → 1 ≤ CA →
    ∀ C0 CG CDel cT Cb' : ℝ, 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb' → 1 < cT * Cb' →
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
      J.SzHyp (gOf D e) CA C0 CG CDel cT Cb' L.sc.b Cp Th' (deOf D τ u) (deOf D τ u')
        (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
      (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
      Formalism.L2.SG.Pf.CarrierT.CarrierDataBound T.X u u' 1 i0 i0' (T.Y.FN u) (T.Y.FN u') νq
        (massDataY T.X T.hb T.Y u u' X0 T.ψ sd C Th vR Q i0 i0' νq).IntN CA (gOf D e) (deOf D τ u) (deOf D τ u')
        (lOf D (deOf D τ u) (deOf D τ u')) C₆ Cc Cb

theorem carrierP_of_repaired_model (hPA : P5.ThmPActual) (hLEM : MA.LemmaEModel) (hMP : JCT.ModelPlaceBuilt2)
    (hBB : KB.BuiltBounds2) (Cb : ℝ) (hX : CarrierSideBoundPositive Cb) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP := by
  obtain ⟨C₆, Cc, C₄, hC6, hC4, hmain⟩ :=
    Formalism.L2.SG.Pf.CarrierT.carrier_input_exists_repaired hPA hLEM hMP hBB Cb
  obtain ⟨CA₀, hrest⟩ := hX C₆ Cc hC6
  refine ⟨C₄, CA₀, hC4, fun CA hCA h1CA C0 CG CDel cT Cb' a2 a3 a4 a5 a6 a7 => ?_⟩
  obtain ⟨k0, hk0⟩ := hrest CA hCA h1CA C0 CG CDel cT Cb' a2 a3 a4 a5 a6 a7
  refine ⟨k0, fun Cg cb Cw cTf CT C0f hcb hcT => ?_⟩
  obtain ⟨C'₀, Cl₀, hcl⟩ := hk0 Cg cb Cw cTf CT C0f hcb hcT
  refine ⟨C'₀, Cl₀, ?_⟩
  intro C' Cl hC' hCl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th F0 what₂ vR Q hTi hne hk hH0 hPl hSz hi hPt hNu
  obtain ⟨Wp, Wq, i1, i2, i3, i4, i5, S, T', f, χ, ν', m₀, top, A₀, τ', Qm, Qim, eP, eQ, h1, h2, h3, h4, h5, h6, -, -,
    h9, h10, h11, h12⟩ := hmain D T.X u u' 1 i0 i0' (T.Y.FN u) (T.Y.FN u') νq T.Y.δ T.Y.M _ CA _ _ _ _
    (hcl C' Cl hC' hCl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th vR Q hTi hne hk hH0 hPl hSz hi hPt hNu)
  exact ⟨Wp, Wq, i1, i2, i3, i4, i5, S, T', f, ν', m₀, τ', Qm, Qim, eP, eQ, h1, h2, h3, h4, h5, h6, h9, h10, h11, h12⟩

end Formalism.L2.SG.SpectralTiesReal
