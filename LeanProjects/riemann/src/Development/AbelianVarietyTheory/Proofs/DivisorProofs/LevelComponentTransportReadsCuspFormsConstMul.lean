import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

theorem exists_const_of_forall_unit_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {O : Set V} (hO : IsOpen O) (hc : IsPreconnected O) (hne : O.Nonempty) {ι : Type} (P Q : ι → V → ℂ)
    (hP : ∀ j, DifferentiableOn ℂ (P j) O) (hQ : ∀ j, DifferentiableOn ℂ (Q j) O)
    (h : ∀ x ∈ O, ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ j, P j x = u * Q j x) :
    ∃ c : ℂˣ, ∀ j, ∀ x ∈ O, P j x = c * Q j x := by
  by_cases h0 : ∃ j, ∃ x₁ ∈ O, Q j x₁ ≠ 0
  · obtain ⟨j₀, x₁, hx₁, hq⟩ := h0
    obtain ⟨u₁, hu₁, hPu⟩ := h x₁ hx₁
    have hu0 : u₁ ≠ 0 := by
      intro e
      rw [e, norm_zero] at hu₁
      exact zero_ne_one hu₁

    have step : ∀ j, ∀ x ∈ O, P j x + (1 - Q j x₁) / Q j₀ x₁ * P j₀ x =
        u₁ * (Q j x + (1 - Q j x₁) / Q j₀ x₁ * Q j₀ x) := by
      intro j
      set μ : ℂ := (1 - Q j x₁) / Q j₀ x₁ with hμ
      obtain ⟨-, c', hc'⟩ := GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq V Unit O hO hc hne
        (fun x => P j x + μ * P j₀ x) (fun _ x => Q j x + μ * Q j₀ x)
        ((hP j).add ((hP j₀).const_smul μ))
        (fun _ => (hQ j).add ((hQ j₀).const_smul μ))
        (fun x hx => by
          obtain ⟨u, hu, hPx⟩ := h x hx
          refine ⟨(), ?_⟩
          simp only [hPx, ← mul_add, mul_left_comm μ u, norm_mul, hu, one_mul])
      have hQ1 : Q j x₁ + μ * Q j₀ x₁ = 1 := by
        rw [hμ, div_mul_cancel₀ _ hq]
        ring
      have hc1 : c' = u₁ := by
        have e := hc' x₁ hx₁
        rw [hQ1, mul_one, hPu j, hPu j₀, mul_left_comm μ u₁, ← mul_add, hQ1, mul_one] at e
        exact e.symm
      intro x hx
      rw [hc' x hx, hc1]
    have h₀ : ∀ x ∈ O, P j₀ x = u₁ * Q j₀ x := by
      intro x hx
      have e := step j₀ x hx
      have hne' : 1 + (1 - Q j₀ x₁) / Q j₀ x₁ ≠ 0 := by
        rw [add_div' _ _ _ hq]
        simp [hq]
      have : (1 + (1 - Q j₀ x₁) / Q j₀ x₁) * (P j₀ x - u₁ * Q j₀ x) = 0 := by
        linear_combination e
      rcases mul_eq_zero.1 this with h1 | h1
      · exact (hne' h1).elim
      · exact sub_eq_zero.1 h1
    refine ⟨Units.mk0 u₁ hu0, fun j x hx => ?_⟩
    have e := step j x hx
    rw [Units.val_mk0]
    linear_combination e - (1 - Q j x₁) / Q j₀ x₁ * h₀ x hx
  · push_neg at h0
    refine ⟨1, fun j x hx => ?_⟩
    obtain ⟨u, -, hPx⟩ := h x hx
    rw [hPx j, h0 j x hx, mul_zero, mul_zero]

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem transp_reads_const_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a → ∃ c : ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom → ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ), rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) γ F.1) k x = (c : ℂ) * rdU (uAt r v i) F.1 k' (castFrame h2 (lact a x)) := by
  intro D L hT Gi Gl Kc Y cX eX Csz p hp r h hr i v ψ γ k k' a ht
  obtain ⟨hm, hb, -⟩ := ht
  have hl := h.laws v
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ := (r.used v).full.toCore.good_σ₀
  have hU : IsUnf (uAt r v i) := hl.p.unf _ hj _ hσ
  have hpins := hl.p.pins
  have hpq : 1 ≤ ((r.used v).full.Q.Dw ((i : ℕ) + 1)).p + ((r.used v).full.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(hpins.2.2.2 _ hj).1, (hpins.2.2.2 _ hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D (r.used v).full.Q ((i : ℕ) + 1) hpq hpins.2.1.2
  have hsecF : ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
      F.1 ∈ sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n := fun F =>
    ((mem_cusp _ _ _ _ _ _).1 (Submodule.mem_inf.1 F.2).1).1
  have hsecG : ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
      actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1 ∈
        sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n := fun F =>
    actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ (hsecF F)
  have P1 : ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom)
      (hy : castFrame hm.psi (lact a x) ∈ ((uAt r v i).X k').dom) (t : _)
      (hbt : FrBor t ((uAt r v i).un k' ⟨castFrame hm.psi (lact a x), hy⟩)
        (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c γ ((uAt r v i).un k ⟨x, hx⟩)))
      (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)),
      rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
        toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t : CAt (r.used v).full.σ₀) *
          rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) := by
    intro x hx hy t hbt F
    have e1 : rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
        toC (evR _ _ (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1)
          ((uAt r v i).un k ⟨x, hx⟩)) := dif_pos hx
    have e2 : rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) =
        toC (evR _ _ F.1 ((uAt r v i).un k' ⟨_, hy⟩)) := dif_pos hy
    have e3 := evalAt_actL hL (hl.p.evalWD _ hj) frMap_trans_id γ (hsecF F).1 ((uAt r v i).un k ⟨x, hx⟩)
    have e4 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ _ _).2.2.2.2.2.2 (CAt _)
      (inferInstanceAs (IsReduced ℂ)) _ _ F.1 (hsecF F) t _ _ hbt
    rw [e1, e2]
    exact congrArg toC (e3.trans e4)
  have hUf : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) := hU
  have hσf : Formalism.L2.PjFree.GoodEmb (r.used v).full.Q.c (r.used v).full.σ₀ := hσ
  have hr1 : 1 ≤ D.R.r := hU.1 ▸ hpq
  have hxi : ∀ k k' (τ : D.host.E →+* ℂ), ‖τ ((uAt r v i).X k).ξ0‖ = ‖τ ((uAt r v i).X k').ξ0‖ :=
    fun k k' τ => (hl.p.xiAbs _ hj _ hσ k τ).trans (hl.p.xiAbs _ hj _ hσ k' τ).symm
  obtain ⟨hun1, -⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσf hUf
  have hsk : ∀ (f : Rul ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c),
      f ∈ sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n → ∀ k,
      ((uAt r v i).X k).IsSec (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) (rdU (uAt r v i) f k) :=
    fun f hf k => hU.2.2.2.2.1 _ _ (dom_wtA _) f hf k
  have key : ∀ x ∈ ((uAt r v i).X k).dom, ∃ u : ℂ, ‖u‖ = 1 ∧
      ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
        rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
          u * rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) := by
    intro x hx
    obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀'⟩, -⟩ := hun1 k ⟨x, hx⟩
    have e₀ : x₀.1 = rmul x b₀ := e₀'
    obtain ⟨hy₀, t₀, hbt₀⟩ := hb x₀.1 x₀.2
    obtain ⟨ρ, ν, -, -, hmv⟩ := mvPt_spec hL.total γ ((uAt r v i).un k x₀)
    have hx₀' : GlobalTheory.FrameNorm.IsUnitFr ((uAt r v i).X k') (castFrame hm.psi (lact a x₀.1)) := fun τ j => by
      exact (congrArg norm (hm.dmin_eq x₀.1 τ j)).trans (hx₀ _ _)
    obtain ⟨-, -, -, -, -, -, ht1⟩ := GlobalTheory.LevelCusp.exists_match (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσf hUf hr1
      hxi (x := x₀) (x' := ⟨castFrame hm.psi (lact a x₀.1), hy₀⟩) hmv hbt₀ hx₀ hx₀'
    refine ⟨toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t₀ : CAt (r.used v).full.σ₀), ?_, fun F => ?_⟩
    · have : toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t₀ : CAt (r.used v).full.σ₀) =
          ∏ j, toC (t₀ j : CAt (r.used v).full.σ₀) ^ ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n j := rfl
      rw [this, norm_prod]
      exact Finset.prod_eq_one fun j _ => by
        rw [norm_pow, show ‖toC (t₀ j : CAt (r.used v).full.σ₀)‖ = 1 from ht1 j, one_pow]
    · have A := P1 x₀.1 x₀.2 hy₀ t₀ hbt₀ F
      have B := (hsk _ (hsecG F) k).2.1 x hx b₀ hb₀
      have C := (hsk _ (hsecF F) k').2.1 _ (hb x hx).1 _ (GlobalTheory.Dict.Pull.cast_bor hm.psi hb₀)
      have e5 : castFrame hm.psi (lact a x₀.1) = rmul (castFrame hm.psi (lact a x)) (GlobalTheory.Dict.castFr hm.psi b₀) := by
        rw [e₀]
        exact (congrArg (castFrame hm.psi) (GlobalTheory.Dict.Extend.lact_rmul a x b₀)).trans (GlobalTheory.Dict.Pull.cast_rmul hm.psi _ _)
      have e6 : bchar (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k') (GlobalTheory.Dict.castFr hm.psi b₀) =
          bchar (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) b₀ :=
        GlobalTheory.Dict.Pull.cast_bchar hm.psi (GlobalTheory.LevelCusp.laU_match (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hm _ _) b₀
      rw [e5, C, e6, e₀, B] at A
      have hβ := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne ((uAt r v i).X k) (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) hb₀
      apply mul_left_cancel₀ hβ
      rw [A]
      ring
  obtain ⟨c, hc⟩ := exists_const_of_forall_unit_mul (FourierCoefficientDomain.isOpen_dom _)
    (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).isPreconnected
    (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).nonempty
    (fun (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) x =>
      rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x)
    (fun (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) x =>
      rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)))
    (fun F => (hsk _ (hsecG F) k).1)
    (fun F => (hsk _ (hsecF F) k').1.comp
      ((GlobalTheory.Dict.Pull.cast_diff hm.psi).comp (GlobalTheory.Dict.Extend.differentiable_lact a)).differentiableOn
      (fun x hx => (hb x hx).1))
    key
  refine ⟨c, fun F x hx h2 => ?_⟩
  exact hc F x hx

end GlobalTheory.ShareOn
