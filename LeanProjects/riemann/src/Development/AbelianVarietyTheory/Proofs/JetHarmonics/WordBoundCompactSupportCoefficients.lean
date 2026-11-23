import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRadialPartPolyDiffOperatorClosedStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsMulGOfSmoothLog
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordOperatorRadialPointwiseBoundStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPictureSmulCutoffGMultiplierStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorNormEqRadialValueNormStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TLPlanAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem polyLift_listProd {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ) (H : List (RA P Bs)) (hH : ∀ h ∈ H, PolyLift P Bs o κ h) :
    PolyLift P Bs (H.length * o) (H.length * κ) H.prod := by
  obtain ⟨h1, -, hmul⟩ := GlobalTheory.T.polyLift_one_mono_mul Wp Wq P Bs
  induction H with
  | nil => simpa using h1
  | cons a H ih =>
    have := hmul _ _ _ _ _ _ (hH a (by simp)) (ih fun h hh => hH h (by simp [hh]))
    rw [List.prod_cons, List.length_cons, Nat.succ_mul, Nat.succ_mul, add_comm _ o, add_comm _ κ]
    exact this

theorem wordBound_cptCoef : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), KB.CutWord P p.l0 w → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ KB.CptCoef p.T.base f) := by
  intro a ha Wp Wq _ _ _ _ _ _ P p w hw
  obtain ⟨X, μ, L, st, hD, hL⟩ := p.hΘ
  obtain ⟨d, hd⟩ := Formalism.FourierDecayAlt.P.normal_form_actual Wp Wq P _ _ _ _ p.hP X
  have hNF : IsNF (Bs := p.T.base) X d := hd
  have hok := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P _ _ _ _ st p.l0 hD.1.1 p.hl.1 p.hl.2.1 hD.2.2.2.2.1 hD.2.2.2.2.2.1 w
    hw.1 hw.2
  have hl : (D.positionted w).length = w.length := by simp [D.positionted]
  obtain ⟨C, J, Ts, hC, hTs, hB⟩ := GlobalTheory.T.wordOperator_radial_pointwise_bound Wp Wq P p.T.base X μ L st p.l0 d hD hNF (Fin w.length) _ (a P.r)
    (ha Wp Wq P p.T.base X μ L st p.l0 d hD hNF) (D.positionted w) hok.1
  rw [hl] at hTs hB
  have hlift : ∀ H : List (RA P p.T.base), ∃ Θ : B.DiffOp P.k P.r Wp Wq, H ∈ Ts →
      Formalism.FourierDecayAlt.P.CutMP.PolyOp (w.length * (2 * P.r + P.k + 1))
        (w.length * (8 * (P.r + 1) * (2 * P.r + P.k + 1))) Θ ∧ TL.RadIs P p.T.base Θ H.prod.1 := by
    intro H
    by_cases hH : H ∈ Ts
    · obtain ⟨Θ, hΘ⟩ := polyLift_listProd P p.T.base _ _ H (hTs H hH).2
      rw [(hTs H hH).1] at hΘ
      exact ⟨Θ, fun _ => hΘ⟩
    · obtain ⟨Θ, -⟩ := (GlobalTheory.T.polyLift_one_mono_mul Wp Wq P p.T.base).1
      exact ⟨Θ, fun h => absurd h hH⟩
  choose lf hlf using hlift
  refine ⟨C, J, Ts.map lf, hC, ?_, ?_⟩
  · intro Θ hΘ
    obtain ⟨H, hH, rfl⟩ := List.mem_map.1 hΘ
    exact (hlf H hH).1
  · rintro φ f ⟨hφ, hf⟩ e c hc hG
    obtain ⟨hm1, hm2⟩ := GlobalTheory.T.radial_picture_smul_cutoff_G_multiplier Wp Wq P p.T.base φ f
    obtain ⟨hsl, hcpt⟩ := hm1 hφ
    obtain ⟨W, hW⟩ := mulG_exists Wp Wq P p.T.base X μ L st p.l0 d hD hNF φ hsl
    obtain ⟨⟨ε, hε, hN⟩, -⟩ := Formalism.FourierDecayAlt.P.compact_support_facts P.k P.r Wp Wq p.T.base f hf
    obtain ⟨Φ, hΦ⟩ := Formalism.FourierDecayAlt.P5.radJFExists Wp Wq P _ _ _ _ p.T.base f p.hP rfl rfl rfl rfl
      ⟨hN.2.1, ε, hε, hN.2.2⟩
    have hΦ' : Top.IsRadOf P p.T.base Φ f := hΦ
    have hrad := hL w hw _ (hcpt hf) _ (hm2 W Φ hW hΦ') e
    rw [TL.act_e1Vec] at hrad
    obtain ⟨x, hx, hg, hdd, lam, hlam, hV⟩ := GlobalTheory.T.bigCellVector_norm_eq_radialValue_norm Wp Wq P p c hc hG
    have hb := hB φ W hsl hW Φ e x hx
    rw [hg, hdd] at hb
    have hs : ((Ts.map lf).map fun Θ => ‖B.hsVec (p.V (B.opApply Θ f) (TBB.bigPt P.r c))‖).sum =
        lam * (Ts.map fun H => nv (H.prod.1 Φ) x).sum := by
      rw [List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun H hH => ?_
      exact hV _ _ ((hlf H hH).2 f hf Φ hΦ')
    rw [hV _ _ hrad, hs]
    have := mul_le_mul_of_nonneg_left hb hlam.le
    refine le_trans (le_of_eq rfl) (this.trans (le_of_eq ?_))
    ring

end GlobalTheory.HatNF
