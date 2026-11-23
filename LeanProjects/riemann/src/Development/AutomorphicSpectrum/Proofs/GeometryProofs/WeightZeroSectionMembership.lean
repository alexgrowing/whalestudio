import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactificationCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKeySecOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug

set_option maxHeartbeats 2000000 in

theorem bdd_mem_cuspOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (x : ℝ) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ∀ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0), f ∈ GlobalTheory.AllWt.suppOn Z → (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ GlobalTheory.AllWt.framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f z ≤ C) → f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) := by
  intro E _ _ _ H Dw l Xo c r U h e hL hp hq x Z u hu f hf hfZ hb
  have hF : FnAlgClosed Xo c :=
    GlobalTheory.CompanionTheory.Ar.Rec.CompOver.fnAlgClosed_of_card (U c.F.val.toRingHom) rfl (hL.unf _ rfl) h (hL.unTest _ rfl) hL.genT
      hL.comps
  refine ⟨GlobalTheory.AllWt.mem_cuspW.2 ⟨hf, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩, hfZ⟩
  have hU := hL.unf σ hσ
  have hK : Nonempty (GlobalTheory.ShFam.KeySec Xo c) := by
    obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hU
    exact GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ σ hσ ee F (by omega) hF
  have hdec : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (GlobalTheory.AllWt.wtOf Dw u 0).1 (τ, j) ≤ (GlobalTheory.AllWt.wtOf Dw u 0).1 (τ, i) := by
    intro τ i j hij hj
    by_cases hτ : τ (H.rt : E) = H.rt0
    · have hjp : j < Dw.p := by simpa [Datum.mult, hτ] using hj
      have e1 := GlobalTheory.AllWt.wtOf_big u 0 ⟨τ, hτ⟩ j hjp
      have e2 := GlobalTheory.AllWt.wtOf_big u 0 ⟨τ, hτ⟩ i (by omega)
      simp only at e1 e2
      rw [e1, e2]
      have := (hu ⟨τ, hτ⟩).antitone (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨j, by omega⟩ from hij)
      omega
    · have hjq : j < Dw.q := by simpa [Datum.mult, hτ] using hj
      have hc := GlobalTheory.AllWt.conj_mem hτ
      have e1 := GlobalTheory.AllWt.wtOf_small u 0 ⟨conjEmb τ, hc⟩ j hjq
      have e2 := GlobalTheory.AllWt.wtOf_small u 0 ⟨conjEmb τ, hc⟩ i (by omega)
      simp only [GlobalTheory.AllWt.conjEmb_conjEmb] at e1 e2
      rw [e1, e2]
      have := (hu ⟨conjEmb τ, hc⟩).antitone
        (show (⟨Dw.p + (Dw.q - 1 - j), by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from
          Fin.mk_le_mk.2 (by omega))
      omega
  have hsec := GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU _ _ _ _ _ _ σ _ (U σ) hK hσ hU (by omega) _
    (GlobalTheory.AllWt.even_wtOf u 0) hdec f hf k
  have hr := hU.1
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k

  obtain ⟨t⟩ : Nonempty (GlobalTheory.AllWt.Psi H) := by
    obtain ⟨ρ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hρ : ρ (H.rt : E) = H.rt0
    · exact ⟨⟨ρ, hρ⟩⟩
    · exact ⟨⟨conjEmb ρ, GlobalTheory.AllWt.conj_mem hρ⟩⟩
  have ht : relab c σ t.1 ∈ ((U σ).X k).Ψ := by
    refine (hΨ _).2 ?_
    have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
    exact (congrArg σ (Subtype.ext t.2)).trans hσ0
  have hbig : ∀ j : Fin r, ∀ hj : Dw.q ≤ (j : ℕ), GlobalTheory.AllWt.modelWt (U σ) (GlobalTheory.AllWt.wtOf Dw u 0) k ⟨_, ht⟩ j =
      u t ⟨(j : ℕ) - Dw.q, by omega⟩ := by
    intro j hj
    have hjr := j.2
    have := GlobalTheory.AllWt.modelWt_wtOf_big (U σ) u 0 k hp0 t ht ((j : ℕ) - Dw.q) (by omega) (by omega)
    rwa [show (⟨Dw.q + ((j : ℕ) - Dw.q), by omega⟩ : Fin r) = j from Fin.ext (by simp only; omega)] at this
  have hsm : ∀ j : Fin r, ∀ hj : (j : ℕ) < Dw.q, GlobalTheory.AllWt.modelWt (U σ) (GlobalTheory.AllWt.wtOf Dw u 0) k ⟨_, ht⟩ j =
      u t ⟨Dw.p + (j : ℕ), by omega⟩ := fun j hj =>
    GlobalTheory.AllWt.modelWt_wtOf_small (U σ) u 0 k hp0 t ht j hj j.2
  obtain ⟨C, hC⟩ := hb σ hσ
  have hpos := GlobalTheory.AllWt.lieFacZ_pos (Dw := Dw) x (GlobalTheory.AllWt.wtOf Dw u 0)
  have hbdd : ((U σ).X k).IsBddSec (GlobalTheory.AllWt.modelWt (U σ) (GlobalTheory.AllWt.wtOf Dw u 0) k) (rdU (U σ) f k) := by
    refine ⟨hsec, max (C / GlobalTheory.AllWt.lieFacZ Dw x (GlobalTheory.AllWt.wtOf Dw u 0)) 0, fun y hy => ?_⟩
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ GlobalTheory.AllWt.framesOn (U σ) Z
    · refine le_max_of_le_left ((le_div_iff₀' hpos).2 ?_)
      have h1 := hC ⟨k, y⟩ hz
      simpa only [GlobalTheory.AllWt.homN, GlobalTheory.AllWt.ptN] using h1
    · have h0 : rdU (U σ) f k y = 0 := GlobalTheory.AllWt.rdU_eq_zero (U σ) hfZ hz
      refine le_max_of_le_right (le_of_eq ?_)
      simp [Data.pnorm, h0]
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.cuspStatement_holds r _ _ ⟨_, ht⟩ (by omega) (by omega) (fun i j hij hjp => ?_)
    (fun i0 i1 h0 h1 => ?_) _ hbdd
  · have hjr := j.2
    have hir := i.2
    by_cases hjq : (j : ℕ) < Dw.q
    · rw [hsm j hjq, hsm i (by omega)]
      exact (hu t).antitone (Fin.mk_le_mk.2 (by omega))
    · have hiq : Dw.q ≤ (i : ℕ) := by omega
      rw [hbig j (by omega), hbig i hiq]
      exact (hu t).antitone (Fin.mk_le_mk.2 (by omega))
  · have hi1 := i1.2
    rw [hsm i0 (by omega), hbig i1 (by omega)]
    exact (hu t) (Fin.mk_lt_mk.2 (by omega))

end GlobalTheory.CompanionTheory.Ar.Plug
