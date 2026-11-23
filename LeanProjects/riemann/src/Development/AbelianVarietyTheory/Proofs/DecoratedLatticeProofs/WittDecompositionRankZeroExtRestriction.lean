import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallQ
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawThetaIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HyperbolicZeroEmbeddingId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepRankZeroWittEmbeddingValueAtZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumIsTwoVariableThetaFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing MeasureTheory GlobalTheory.FinPl.VLast

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.VLast.KernPf

variable {D : D7}

theorem wittDecomposition_rankZero_coreEmbed_proj {S S₀ : HSp D} (e : HypDec S S₀ 0) : e.j0 ⬝ e.p0 = 1 := by
  have h := e.sum_eq_one
  have h1 : e.jX ⬝ e.pX = 0 := by ext i k; simp [Matrix.mul_apply]
  have h2 : e.jY ⬝ e.pY = 0 := by ext i k; simp [Matrix.mul_apply]
  rwa [h1, h2, zero_add, add_zero] at h

def wittCoreRestrictionHom {S S₀ : HSp D} {ρ : ℕ} (e : HypDec S S₀ ρ) (T : HSp D) : WO S T →+ WO S₀ T where
  toFun w := w ⬝ e.j0
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

theorem wittCoreRestrictionHom_apply {S S₀ : HSp D} {ρ : ℕ} (e : HypDec S S₀ ρ) (T : HSp D) (w : WO S T) : wittCoreRestrictionHom e T w = w ⬝ e.j0 := rfl

theorem continuous_restrict_j_zero {S S₀ : HSp D} {ρ : ℕ} (e : HypDec S S₀ ρ) (T : HSp D) : Continuous (wittCoreRestrictionHom e T) :=
  continuous_id.matrix_mul continuous_const

theorem wittDecomposition_rankZero_ext_restriction {S S₀ : HSp D} (e : HypDec S S₀ 0) (T : HSp D) (w : WO S T) : e.ext0 T (wittCoreRestrictionHom e T w) = w := by
  rw [HypDec.matrixExtendByZero_apply, wittCoreRestrictionHom_apply, Matrix.mul_assoc, wittDecomposition_rankZero_coreEmbed_proj, Matrix.mul_one]

theorem symplectic_restrict_j_zero {S S₀ : HSp D} (e : HypDec S S₀ 0) (T : HSp D) (w w' : WO S T) :
    symplOH S T w w' = symplOH S₀ T (wittCoreRestrictionHom e T w) (wittCoreRestrictionHom e T w') := by
  rw [← e.wittDecomp_sympl_extAnisotropic_extAnisotropic T, wittDecomposition_rankZero_ext_restriction, wittDecomposition_rankZero_ext_restriction]

theorem theta_restrict_j_zero {S S₀ T : HSp D} (e : HypDec S S₀ 0) {ψ : AddChar (AF D.host.F) ℂ} {Φ : WO S₀ T → ℂ}
    (hΦ : IsThetaFunO ψ S₀ T Φ) : IsThetaFunO ψ S T (fun w => Φ (wittCoreRestrictionHom e T w)) where
  quasi γ w := by
    have h := hΦ.quasi (γ ⬝ e.i₀) (wittCoreRestrictionHom e T w)
    have hr : ratW T S₀ (γ ⬝ e.i₀) = wittCoreRestrictionHom e T (ratW T S γ) := by
      rw [ratW_eq, ratW_eq, rat_mul, wittCoreRestrictionHom_apply]; rfl
    rw [hr] at h
    rw [map_add, symplectic_restrict_j_zero e T]
    exact h
  level := by
    obtain ⟨U, hU, hfix⟩ := hΦ.level
    refine ⟨U.comap (wittCoreRestrictionHom e T), hU.preimage (continuous_restrict_j_zero e T), fun u hu hinf => ?_⟩
    have h0 : (wittCoreRestrictionHom e T u).map (infPart D) = 0 := by
      rw [wittCoreRestrictionHom_apply, Matrix.map_mul, hinf, Matrix.zero_mul]
    have hf := hfix _ hu h0
    funext w
    have hw := congrFun hf (wittCoreRestrictionHom e T w)
    simp only [heisO] at hw ⊢
    rw [symplectic_restrict_j_zero e T, map_add]
    exact hw
  cont := hΦ.cont.comp (continuous_restrict_j_zero e T)
  smooth k L hL hLf w := by
    have h := hΦ.smooth k ((wittCoreRestrictionHom e T).comp L) ((continuous_restrict_j_zero e T).comp hL) (fun t => by
      show (wittCoreRestrictionHom e T (L t)).map (finPart D) = 0
      rw [wittCoreRestrictionHom_apply, Matrix.map_mul, hLf t, Matrix.zero_mul]) (wittCoreRestrictionHom e T w)
    simpa only [AddMonoidHom.comp_apply, map_add] using h

theorem om_core_eq_rankZero (ψ : AddChar (AF D.host.F) ℂ) {S S₀ T : HSp D} (e : HypDec S S₀ 0)
    (χS χT χS' χT' : (AE D)ˣ →* Circle) (om : Om S T) (om₁ om₂ : Om S₀ T)
    (h1 : IsWeilDatumO ψ S T χS χT om) (h1' : IsWeilDatumO ψ S₀ T χS χT om₁)
    (h2 : IsWeilDatumO ψ S T χS' χT' om) (h2' : IsWeilDatumO ψ S₀ T χS' χT' om₂)
    (Φ : WO S₀ T → ℂ) (hΦ : IsThetaFunO ψ S₀ T Φ) (g : GA D S₀) (h : GA D T) :
    om₁ (g, h) Φ 0 = om₂ (g, h) Φ 0 := by
  have hf := theta_restrict_j_zero e hΦ
  have a := GlobalTheory.FinPl.VLast.Transport.weilRep_rankZeroWittEmbedding_valueAtZero D ψ S S₀ T e χS χT om om₁ h1 h1' _ hf g h
  have b := GlobalTheory.FinPl.VLast.Transport.weilRep_rankZeroWittEmbedding_valueAtZero D ψ S S₀ T e χS' χT' om om₂ h2 h2' _ hf g h
  have hw : (fun w => Φ (wittCoreRestrictionHom e T (e.ext0 T w))) = Φ := by
    funext w; rw [HypDec.matrixExtendByZero_apply, wittCoreRestrictionHom_apply, Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one]
  rw [hw] at a b
  rw [← a, ← b]

end GlobalTheory.FinPl.VLast.KernPf

namespace GlobalTheory.FinPl.VLast.KernPf

set_option maxHeartbeats 2000000 in

theorem main : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : OffDat d k ι), d.Base → PinOff o → ∀ (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (χS χT : (AE D)ˣ →* Circle) (omT : Om (D.sp.X (j + 1)) D.sp.X'), IsWeilDatumO d.c.ψ _ _ χS χT (d.pT j h).ω → IsWeilDatumO d.c.ψ _ _ χS χT omT → ∀ (φ : GA D (D.sp.X j) → ℂ) (Ξ : WO (d.bes j 0 h).V₀ (D.sp.X (j + 1)) → ℂ) (Φ : WO (D.sp.X (j + 1)) D.sp.X' → ℂ), IsThetaFunO d.c.ψ _ _ Ξ → IsThetaFunO d.c.ψ _ _ Φ → ∀ F : GA D D.sp.X' → ℂ, smallQ d j h (d.sBF j 0 h).om₀ omT φ Ξ Φ F = ∫ h' in d.top.fd, F h' * biLift (d.k j).om (d.k (j + 1)).om (d.x j).vol (d.x (j + 1)).vol φ (lastBi (d.bes j 0 h).o (d.oT (j + 1 + 1) h) (o.τ j h) Ξ Φ) ((d.oT (j + 1 + 1) h).emb (h', 1)) ∂d.top.ν := by
  intro D u d k _ _ _ _ ι o _ hP j h χS χT omT hpT homT φ Ξ Φ hΞ hΦ F
  obtain ⟨χA, χz, χS', χT', omz, omT₀, omz'', hV, homa, homz, homX, homT₀, hpT', homz'', -⟩ := hP.weilLast j h
  have hstd : IsStdChar D d.c.ψ (-1) := hpT.std

  have hT : ∀ g h', omT (g, h') Φ 0 = omT₀ (g, h') Φ 0 := fun g h' =>
    om_core_eq_rankZero d.c.ψ (d.jac j 0 h).d χS χT χS' χT' (d.pT j h).ω omT omT₀ hpT homT hpT' homT₀ Φ hΦ g h'
  have hom₁ : IsWeilDatumO d.c.ψ _ _ (χA * χz) (d.sBF j 0 h).χW (d.sBF j 0 h).om₀ := by
    rw [← hV]; exact (d.sBF j 0 h).weil₀
  have hτ := (hP.tau j h).1
  obtain ⟨-, key⟩ := GlobalTheory.SeeLastPf.seeLast D d.c.ψ (d.bes j 0 h).V₀ (D.sp.X j) (d.bes j 0 h).L (D.sp.X (j + 1))
    (D.sp.X (j + 1 + 1)) D.sp.X' d.Lz (d.bes j 0 h).o (d.oT (j + 1 + 1) h) (o.τ j h) (d.bes j 0 h).line.1
    (lastLine_rank d) hτ χA χz (d.sBF j 0 h).χW χS' χT' (d.sBF j 0 h).om₀ (d.k j).om omz (d.k (j + 1)).om omT₀ omz''
    hom₁ homa homz homX homT₀ homz'' Ξ Φ hΞ hΦ
  have hC := GlobalTheory.LastBiTheta.isBiTheta_lastBi D d.c.ψ hstd (d.bes j 0 h).V₀ (D.sp.X j) (d.bes j 0 h).L (D.sp.X (j + 1))
    (D.sp.X (j + 1 + 1)) D.sp.X' d.Lz (d.bes j 0 h).o (d.oT (j + 1 + 1) h) (o.τ j h) hτ Ξ Φ hΞ hΦ
  obtain ⟨-, -, hcomm, -⟩ := GlobalTheory.SeeSaw.biAct_all D d.c.ψ (D.sp.X j) (D.sp.X (j + 1)) (D.sp.X (j + 1 + 1)) χA
    (d.sBF j 0 h).χW χS' (χT' * χz⁻¹) (d.k j).om (d.k (j + 1)).om homa homX _ hC
  have pt : ∀ h' g h₀, omT (g, h') Φ 0 * (φ h₀ * (d.sBF j 0 h).om₀ ((d.bes j 0 h).o.emb (h₀, 1), g) Ξ 0) =
      φ h₀ * (d.k (j + 1)).om (g, (d.oT (j + 1 + 1) h).emb (h', 1)) (fun v => (d.k j).om (h₀, g)
        (fun u => lastBi (d.bes j 0 h).o (d.oT (j + 1 + 1) h) (o.τ j h) Ξ Φ u v) 0) 0 := by
    intro h' g h₀
    rw [hT, mul_left_comm, key h₀ g h', hcomm]
    rfl
  unfold smallQ biLift
  congr 1
  funext h'
  congr 1
  congr 1
  funext g
  rw [← integral_const_mul]
  congr 1
  funext h₀
  exact pt h' g h₀

end GlobalTheory.FinPl.VLast.KernPf
