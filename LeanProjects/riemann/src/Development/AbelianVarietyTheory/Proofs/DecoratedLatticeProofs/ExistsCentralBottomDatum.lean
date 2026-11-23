import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomHypothesisMatchingCentral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlacedBesselPointsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchingTranslatesBottomStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselCompatibilityStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem GlobalTheory.MiTop.levChi_mul_lev {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ Lev.levG V β L) (hk' : k' ∈ Lev.levG V β L) :
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  unfold Lev.levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg _ ((Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

theorem GlobalTheory.MiTop.conj_in_level {G : Type} [Group G] (J : Subgroup G) (χ : G → ℂ)
    (hm : ∀ a ∈ J, ∀ b ∈ J, χ (a * b) = χ a * χ b) (h0 : ∀ a, χ a ≠ 0) {k : G} (hk : k ∈ J) (j : G) :
    (j ∈ J ↔ k * j * k⁻¹ ∈ J) ∧ (j ∈ J → χ (k * j * k⁻¹) = χ j) := by
  refine ⟨⟨fun hj => J.mul_mem (J.mul_mem hk hj) (J.inv_mem hk), fun hj => ?_⟩, fun hj => ?_⟩
  · have := J.mul_mem (J.mul_mem (J.inv_mem hk) hj) hk
    rwa [show k⁻¹ * (k * j * k⁻¹) * k = j by group] at this
  · have e := hm _ (J.mul_mem (J.mul_mem hk hj) (J.inv_mem hk)) _ hk
    rw [show k * j * k⁻¹ * k = k * j by group, hm _ hk _ hj, mul_comm (χ k)] at e
    exact (mul_right_cancel₀ (h0 k) e).symm

theorem GlobalTheory.MiTop.matches_mul_lev {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)
    {t k : GA D (D.sp.Y 0)} (ht : Matches W.S.X W.Q.instEq (rJ W) (rChi W) t) (hk : k ∈ rJ W) :
    Matches W.S.X W.Q.instEq (rJ W) (rChi W) (t * k) := by
  refine ⟨mul_mem ht.1 hk.1, fun j => ?_⟩
  have hc := GlobalTheory.MiTop.conj_in_level (G := GA D (D.sp.Y 0))
    (Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (rChi W)
    (fun a ha b hb => GlobalTheory.MiTop.levChi_mul_lev _ _ _ ha hb) (fun a => Lev.levChi_ne_zero _ _) hk j
  have h2 := ht.2 (k * j * k⁻¹)
  have e : (t⁻¹)⁻¹ * (k * j * k⁻¹) * t⁻¹ = ((t * k)⁻¹)⁻¹ * j * (t * k)⁻¹ := by group
  rw [e] at h2
  exact ⟨hc.1.trans h2.1, fun hj => (h2.2 (hc.1.1 hj)).trans (hc.2 hj)⟩

theorem GlobalTheory.MiTop.one_central_pin : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.Framed B → ∃ d : BotDat W u, d.B = B ∧ d.b = (show GA D (D.sp.Y 0) from f.g.b 0) ∧ d.Pin z := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr
  classical
  by_cases hex : ∃ (u : D.what₂.Word) (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), PlacedP f B ∧ Framed B
  · obtain ⟨u₀, f₀, B₀, hpl₀, hF₀⟩ := hex
    obtain ⟨a₀, a, hAt⟩ := GlobalTheory.T.exists_placed_bessel_points W hP u₀ f₀ B₀ (by first | exact PlacedP.placed _ _ hpl₀ | exact hpl₀) hF₀
    have hm := GlobalTheory.MiTop.botHyp_match W hP.bot
    have hS : Matches W.S.X W.Q.instEq (rJ W) (rChi W) (show GA D (D.sp.Y 0) from W.Q.tS) := by
      have h1 := hm.2.2.2.1 1 (one_mem _) (one_mem _)
      rwa [one_mul] at h1
    obtain ⟨z, hzf, hzc, c, hcf, hcc, k₀, hk₀, ht⟩ :=
      GlobalTheory.T.matching_translates_bottom W hP.bot hr u₀ B₀ _ hAt.2.2.2.1 _ hS.1 hAt.2.2.2 hS
    have ht₀ : tOf f₀ B₀ a₀ (c⁻¹ * a) = z * (show GA D (D.sp.Y 0) from W.Q.tS) * k₀ := by
      have hc : a₀ * (c⁻¹ * a) = c⁻¹ * (a₀ * a) := by
        rw [← mul_assoc, Subgroup.mem_center_iff.1 (inv_mem hcc) a₀, mul_assoc]
      unfold tOf at ht ⊢
      rw [hc, map_mul, map_inv]
      generalize (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u₀) = x at ht ⊢
      generalize embA B₀.d B₀.o (a₀ * a) = p at ht ⊢
      generalize embA B₀.d B₀.o c = q at ht ⊢
      generalize (show GA D (D.sp.Y 0) from f₀.g.b 0) = b at ht ⊢
      generalize (show GA D (D.sp.Y 0) from W.Q.tS) = s at ht ⊢
      calc x⁻¹ * (q⁻¹ * p) * b = x⁻¹ * q⁻¹ * x * (x⁻¹ * p * b) := by group
        _ = z * s * k₀ := by rw [ht]; group
    have hAt₀ : IsAt f₀ B₀ a₀ (c⁻¹ * a) := by
      refine ⟨hAt.1, mul_mem (inv_mem hcf) hAt.2.1, mul_mem (inv_mem hcc) hAt.2.2.1, ?_⟩
      rw [ht₀]
      exact GlobalTheory.MiTop.matches_mul_lev W (hm.2.2.2.1 z hzf hzc) hk₀
    refine ⟨z, hzf, hzc, fun u f B hpl hF => ?_⟩
    obtain ⟨b₀, b, hAt'⟩ := GlobalTheory.T.exists_placed_bessel_points W hP u f B (by first | exact PlacedP.placed _ _ hpl | exact hpl) hF
    obtain ⟨a₁, hAt1, k, hk, hkt⟩ := GlobalTheory.T.placed_bessel_compatibility W hP hr u u₀ f f₀ B B₀ hpl hpl₀ hF hF₀ b₀ b a₀ _ hAt' hAt₀
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBT, _⟩ := hpl
    refine ⟨⟨B, (show GA D (D.sp.Y 0) from f.g.b 0), b₀, a₁, k₀ * k⟩, rfl, rfl,
      ⟨hBT.adapted, hAt1.1, hAt1.2.1, hAt1.2.2.1, ?_, ?_⟩⟩
    · exact (Formalism.IndefR.Lev.levG _ _ _).mul_mem hk₀ hk
    · have e := hkt
      rw [ht₀] at e
      unfold tOf at e
      show embA B.d B.o (b₀ * a₁) * (show GA D (D.sp.Y 0) from f.g.b 0) =
        (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS) * (k₀ * k))
      have e' : ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
          (embA B.d B.o (b₀ * a₁) * (show GA D (D.sp.Y 0) from f.g.b 0)) =
          z * (show GA D (D.sp.Y 0) from W.Q.tS) * k₀ * k := by
        rw [← mul_assoc]; exact e
      rw [← mul_assoc (z * _) k₀ k, ← e', mul_inv_cancel_left]
  · exact ⟨1, one_mem _, one_mem _, fun u f B hpl hF => (hex ⟨u, f, B, hpl, hF⟩).elim⟩
