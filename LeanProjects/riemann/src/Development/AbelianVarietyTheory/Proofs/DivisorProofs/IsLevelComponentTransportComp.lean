import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ModelAtBare
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isTransp_comp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ γ' : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k₁ k₂ : (uAt r v i).Comp) (a a' : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ' k k₁ a' → IsTransp p r i v ψ γ k₁ k₂ a → IsTransp p r i v ψ (γ' * γ) k k₂ (a * a') := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v ψ γ γ' k k₁ k₂ a a' h₁ h₂
  obtain ⟨m₁, f₁, l₁⟩ := h₁
  obtain ⟨m₂, f₂, l₂⟩ := h₂
  have hP := (h.laws v).p
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left 1 _, i.isLt⟩
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q ((i : ℕ) + 1)
    (GlobalTheory.Proof.ModelAtPrimeToLevel.one_le_rank hP hj) hP.pins.2.1.2
  have hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k₂) (a * a') :=
    { psi := m₁.psi.trans m₂.psi
      p0 := m₁.p0.trans m₂.p0
      xi := m₁.xi.trans m₂.xi
      iso := fun u w => by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, m₂.iso, m₁.iso]
      lat := fun w => by
        rw [m₁.lat, m₂.lat, Units.val_mul, Matrix.mulVec_mulVec] }
  refine ⟨hm, fun x hx => ?_, fun w => ?_⟩
  · obtain ⟨hy₁, t₁, b₁⟩ := f₁ x hx
    obtain ⟨hy₂, t₂, b₂⟩ := f₂ _ hy₁
    have ef : castFrame hm.psi (lact (a * a') x) =
        castFrame m₂.psi (lact a (castFrame m₁.psi (lact a' x))) := by
      funext τ
      simp only [castFrame, lact, mat, Units.val_mul, Matrix.map_mul, Matrix.of_apply]
      rw [mul_assoc]
      rfl
    set Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)
    set c := (r.used v).full.Q.c
    set y₀ := (uAt r v i).un k ⟨x, hx⟩
    set y₁ := (uAt r v i).un k₁ ⟨castFrame m₁.psi (lact a' x), hy₁⟩
    have e1 := hL.mul γ' γ _ y₀ _ _ (mvPt_spec hL.total γ' y₀) (mvPt_spec hL.total γ (mvLev Xo c γ' y₀))
    have e2 := hL.func (γ' * γ) _ y₀ _ _ (mvPt_spec hL.total (γ' * γ) y₀) e1
    have e3 : mvLev Xo c γ (mvLev Xo c γ' y₀) = mvLev Xo c (γ' * γ) y₀ :=
      ((GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id _ _) _).1 _ _ e2
        (GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id _ _) _).2.1)
    have e4 := hL.bor γ _ t₁ y₁ _ (mvLev Xo c γ' y₀) _ b₁ (mvPt_spec hL.total γ y₁)
      (mvPt_spec hL.total γ (mvLev Xo c γ' y₀))
    have e5 := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ _ _ _ _ _ _).2.1 t₂ t₁ _ _ _ b₂ e4
    have key : ∀ (z : Frame ((uAt r v i).X k₂).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k₂).dom),
        z = castFrame m₂.psi (lact a (castFrame m₁.psi (lact a' x))) →
        FrBor (t₂ * t₁) ((uAt r v i).un k₂ ⟨z, hz⟩) (mvLev Xo c (γ' * γ) y₀) := by
      rintro z hz rfl
      rw [← e3]
      exact e5
    exact ⟨ef ▸ hy₂, t₂ * t₁, key _ _ ef⟩
  · obtain ⟨hw₁, q₁⟩ := l₁ w
    obtain ⟨hw₂, q₂⟩ := l₂ ⟨_, hw₁⟩
    have e : ((a * a' : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (w : Fin D.R.r → D.host.E) =
        (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec
          ((a' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (w : Fin D.R.r → D.host.E)) := by
      rw [Units.val_mul, Matrix.mulVec_mulVec]
    have hs : ∀ z, (γ' * γ).symm z = γ.symm (γ'.symm z) := fun z =>
      (γ' * γ).injective (by
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply])
    rw [e]
    refine ⟨hw₂, q₂.trans ?_⟩
    refine congrArg (ψ k₂) ?_
    refine (congrArg γ.symm ((congrArg (ψ k₁).symm q₁).trans ((ψ k₁).symm_apply_apply _))).trans ?_
    exact (hs _).symm

end GlobalTheory.ShareOn

end
