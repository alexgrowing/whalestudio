import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatPIffMulVec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalCongruenceBackTriangularFrameStatement

set_option autoImplicit false

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

theorem natCast_mem_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h2 : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h2
  exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable {E : Type} [Field E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}

theorem lact_mul_lact (a b : GL (Fin r) E) (x : Frame Ψ r) : lact (a * b) x = lact a (lact b x) := by
  funext τ
  simp only [lact, Units.val_mul, Matrix.map_mul]
  exact Matrix.mul_assoc _ _ _

theorem lact_rmul_comm (a : GL (Fin r) E) (x b : Frame Ψ r) : lact a (rmul x b) = rmul (lact a x) b := by
  funext τ
  show (a : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) =
    ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) * mat b τ
  rw [Matrix.mul_assoc]

theorem lact_one_frame (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  simp only [lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

end Cong

set_option maxHeartbeats 1000000 in

theorem sub_mem_half_smul_latP : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp), ∀ γ ∈ ((uAt r v i).X k).Γ, ∀ w ∈ lattice₂ D ((uAt r v i).X k).Λ, Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w ∈ p.T.Q.l.Mb • lattice₂ D ((uAt r v i).X k).Λ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v k γ hγ w hw
  have hL := (h.laws v).p.toLawsCore
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ := (r.used v).full.toCore.good_σ₀
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D _ hL.pins
  have hU := (Formalism.L2.PjFree.isUnf_ofPj _).2 (hL.unf _ hj _ hσ)
  obtain ⟨th, hrk, hth, hD⟩ := hL.dictU _ hj _ hσ
  obtain ⟨⟨x0, hx0, -⟩, -⟩ := hD.2.2
  obtain ⟨η, hηU, hηc, b, hb, hx⟩ := GlobalTheory.T.exists_principal_congruence_back_triangular_frame _ _ _ _ _ _ _ _ _ hσ hU hA (hnum _ hj).2.1 k γ hγ (x0 k) (hx0 k).1
  have hηΓ : η ∈ ((uAt r v i).X k).Γ :=
    GlobalTheory.PrincCore.hasPrinc_core D _ hL _ hj _ hσ k η hηU hηc
  have hmem : (η * γ)⁻¹ ∈ ((uAt r v i).X k).Γ := inv_mem (mul_mem hηΓ hγ)
  have hfix : lact (η * γ)⁻¹ (x0 k) = rmul (x0 k) b := by
    calc lact (η * γ)⁻¹ (x0 k) = lact (η * γ)⁻¹ (rmul (lact η (lact γ (x0 k))) b) := congrArg _ hx
      _ = rmul (lact (η * γ)⁻¹ (lact η (lact γ (x0 k)))) b := lact_rmul_comm _ _ _
      _ = rmul (lact ((η * γ)⁻¹ * (η * γ)) (x0 k)) b := by
        rw [lact_mul_lact ((η * γ)⁻¹) (η * γ), lact_mul_lact η γ]
      _ = rmul (x0 k) b := by rw [inv_mul_cancel, lact_one_frame]
  have h1 := ((uAt r v i).X k).Γ_free _ hmem (x0 k) (hx0 k).1 b hb hfix
  have hγη : γ = η⁻¹ := by
    rw [inv_eq_one] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hγU := ((uAt r v i).X k).Γ_stab γ hγ

  have hcong : ∀ u ∈ ((uAt r v i).X k).Λ, ∃ y ∈ ((uAt r v i).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u - u = ((r.used v).full.Q.l.M : D.host.E) • y := by
    intro u hu
    obtain ⟨y, hy, he⟩ := hηc (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u) ((hγU.2 u).1 hu)
    have hηγ : Matrix.mulVec (η : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)
        (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u) = u := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, hγη, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨-y, ((uAt r v i).X k).Λ.neg_mem hy, ?_⟩
    rw [hηγ] at he
    rw [smul_neg, ← he]
    abel

  have hM0 : ((r.used v).full.Q.l.M : D.host.E) ≠ 0 := by
    have := (r.used v).full.Q.l.three_le
    exact_mod_cast (show (r.used v).full.Q.l.M ≠ 0 by omega)
  obtain ⟨z, hz⟩ : ∃ z : Fin D.R.r → D.host.E, z = ((r.used v).full.Q.l.M : D.host.E)⁻¹ •
      (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w) := ⟨_, rfl⟩
  have hzP : z ∈ lattice₂ D ((uAt r v i).X k).Λ := by
    refine mem_latP.2 fun a ha => ?_
    obtain ⟨y, hy, he⟩ := hcong (a • w) (mem_latP.1 hw a ha)
    have : a • z = y := by
      rw [hz, smul_comm, smul_sub, ← Matrix.mulVec_smul, he, smul_smul, inv_mul_cancel₀ hM0, one_smul]
    rw [this]
    exact hy
  have hMmem : ((r.used v).full.Q.l.M : 𝓞 D.host.E) ∈ (r.used v).full.Q.l.Mb := natCast_mem_half _
  have hfin : Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w =
      ((r.used v).full.Q.l.M : 𝓞 D.host.E) • z := by
    rw [hz, ← algebraMap_smul D.host.E, smul_smul, map_natCast, mul_inv_cancel₀ hM0, one_smul]
  rw [hfin]
  exact Submodule.smul_mem_smul hMmem hzP

end GlobalTheory.ShareOn
