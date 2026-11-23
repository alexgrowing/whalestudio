import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspOfMovesAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfBorelMovesOpenFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCandidateBorelMoveOpenFramesBaireStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem movesAt_of_movesAt_open : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' k'' : (uAt r v i).Comp) (a c : GL (Fin D.R.r) D.host.E) (hma : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (hmc : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k'') c) (W : Set (Frame ((uAt r v i).X k).Ψ D.R.r)), IsOpen W → W.Nonempty → W ⊆ ((uAt r v i).X k).dom → (∀ (z : Frame ((uAt r v i).X k).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k).dom), z ∈ W → MovesAt p r i v γ k k' a hma z hz ∧ MovesAt p r i v γ k k'' c hmc z hz) → ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k'' c hmc x hx → MovesAt p r i v γ k k' a hma x hx := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v γ k k' k'' a c hma hmc W hWo hWn hWd hW x hx hcx
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hU : IsUnf (uAt r v i) := (h.laws v).p.toLawsCore.unf _ hj _ (r.used v).full.toCore.good_σ₀
  obtain ⟨-, htr, hsy, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid D.host.E _ _ _
    ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (CAt (r.used v).full.σ₀)

  have step : ∀ z (hz : z ∈ ((uAt r v i).X k).dom), z ∈ W →
      ∃ γ' ∈ ((uAt r v i).X k').Γ, ∃ b ∈ Bor ((uAt r v i).X k').Ψ D.R.r,
        (⟨k'', castFrame hmc.psi (lact c z)⟩ : Σ k, Frame ((uAt r v i).X k).Ψ D.R.r) =
          ⟨k', rmul (lact γ' (castFrame hma.psi (lact a z))) b⟩ := by
    intro z hz hzW
    obtain ⟨⟨hy₁, t₁, f₁⟩, ⟨hy₂, t₂, f₂⟩⟩ := hW z hz hzW
    have hb := htr _ _ _ _ _ f₁ (hsy _ _ _ f₂)
    exact (hU.2.2.2.1 k' k'' ⟨_, hy₁⟩ ⟨_, hy₂⟩).1 ⟨_, hb⟩
  obtain ⟨z₀, hz₀⟩ := hWn
  have hk : k'' = k' := by
    obtain ⟨g₀, -, b₀, -, e₀⟩ := step z₀ (hWd hz₀) hz₀
    exact (Sigma.mk.inj_iff.1 e₀).1
  subst hk
  have hcast : ∀ z (b : Frame ((uAt r v i).X k'').Ψ D.R.r) (γ' : GL (Fin D.R.r) D.host.E),
      castFrame hmc.psi (lact c z) = rmul (lact γ' (castFrame hma.psi (lact a z))) b →
      lact c z = rmul (lact γ' (lact a z)) (castFrame hma.psi.symm b) := by
    intro z b γ' e
    funext τ
    have := congrFun e ⟨τ.1, hma.psi ▸ τ.2⟩
    exact this
  have hborc : ∀ b ∈ Bor ((uAt r v i).X k'').Ψ D.R.r, castFrame hma.psi.symm b ∈ Bor ((uAt r v i).X k).Ψ D.R.r := by
    intro b hb τ
    exact hb ⟨τ.1, hma.psi ▸ τ.2⟩
  obtain ⟨γ', hγ', V, hVo, hVn, hVd, hV⟩ := GlobalTheory.T.exists_candidate_borel_move_open_frames_baire ((uAt r v i).X k) ((uAt r v i).X k'').Γ a c W hWo ⟨z₀, hz₀⟩ hWd
    (fun z hz => by
      obtain ⟨γ', hγ', b, hb, e⟩ := step z (hWd hz) hz
      exact ⟨γ', hγ', _, hborc b hb, hcast z b γ' (eq_of_heq (Sigma.mk.inj_iff.1 e).2)⟩)
  obtain ⟨s, hs⟩ := GlobalTheory.T.scalar_of_borel_moves_open_frames ((uAt r v i).X k) _ V hVo hVn hVd hV
  set m : GL (Fin D.R.r) D.host.E := (γ' * a)⁻¹ * c with hm_def
  have hcm : (c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) =
      (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * (a : Matrix _ _ _) * (m : Matrix _ _ _) := by
    have : c = γ' * a * m := by rw [hm_def]; group
    rw [this]; simp [Units.val_mul]
  obtain ⟨hy₂, t₂, f₂⟩ := hcx
  have hy₁ : castFrame hma.psi (lact a x) ∈ ((uAt r v i).X k'').dom := hma.mem_dom hx
  let bm : Frame ((uAt r v i).X k'').Ψ D.R.r := fun τ => (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1
  have hbm : bm ∈ Bor ((uAt r v i).X k'').Ψ D.R.r := by
    intro τ
    refine ⟨?_, fun p q hpq => ?_⟩
    · show ((m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1).det ≠ 0
      rw [show (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = τ.1.mapMatrix (m : Matrix _ _ _) from rfl,
        ← RingHom.map_det]
      have hu : IsUnit (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det :=
        (Matrix.isUnit_iff_isUnit_det _).1 m.isUnit
      exact (map_ne_zero τ.1).2 hu.ne_zero
    · show (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 p q = 0
      rw [hs, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (ne_of_lt hpq).symm, map_zero]
  have heq : castFrame hmc.psi (lact c x) = rmul (lact γ' (castFrame hma.psi (lact a x))) bm := by
    funext τ
    show (c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, _⟩ =
      ((γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * ((a : Matrix _ _ _).map τ.1 * mat x ⟨τ.1, _⟩)) *
        (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1
    rw [hcm, hs, Matrix.map_mul, Matrix.map_mul]
    have hsc : (Matrix.scalar (Fin D.R.r) s).map τ.1 = Matrix.scalar (Fin D.R.r) (τ.1 s) := by
      ext p q; by_cases hpq : p = q <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hpq]
    rw [hsc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    congr 2
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
  have hb := (hU.2.2.2.1 k'' k'' ⟨_, hy₁⟩ ⟨_, hy₂⟩).2 ⟨γ', hγ', bm, hbm, congrArg (Sigma.mk k'') heq⟩
  obtain ⟨t', ht'⟩ := hb
  exact ⟨hy₁, _, htr _ _ _ _ _ ht' f₂⟩

end GlobalTheory.ShareOn

end
