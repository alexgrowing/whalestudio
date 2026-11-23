import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSourceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CplxOfFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockVacAtOfReads
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsONFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompAtMtMul

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.RealCompact

theorem realM_tauE {D : D7} (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (ρ : D.what₂.Tau) :
    realM θ w (tauE D ρ) = compAt θ ρ w := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [realM, dif_pos h, ← GlobalTheory.SmoothForms.RealPts.tauE_injective D h.choose_spec]

theorem mat_frMove {D : D7} (θ : InfFam D) (W : HSp D) (X : Data D.host.E W.rank) (k : GA D W)
    (x : Frame X.Ψ W.rank) (ρ : D.what₂.Tau) (τ : X.Ψ) (h : τ.1 = tauE D ρ) :
    mat (frMove θ W rfl X k x) τ = compAt θ ρ (Formalism.L2.Theta.mt W k) * mat x τ := by
  rw [← realM_tauE, ← h]
  rfl

theorem isONFr_frMove {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (X : Data D.host.E W.rank)
    (hX : IsMod W rfl X) (k : GA D W) (x : Frame X.Ψ W.rank) (hx : IsONFr X x) :
    IsONFr X (frMove θ W rfl X k x) := by
  intro τ
  obtain ⟨ρ, hρ⟩ := (hX.psi τ.1).1 τ.2
  have hu : (compAt θ ρ (Formalism.L2.Theta.mt W k))ᴴ * gramAt D W ρ * compAt θ ρ (Formalism.L2.Theta.mt W k) = gramAt D W ρ :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W k ρ
  have hG : X.Gm.map τ.1 = -(gramAt D W ρ)ᵀ := by
    rw [hX.model.1, hρ]
    ext a b
    exact map_neg (tauE D ρ) _
  have e : ∀ y : Matrix (Fin W.rank) (Fin W.rank) ℂ, FD.gram τ.1 X.Gm y = -(yᴴ * gramAt D W ρ * y)ᵀ := by
    intro y
    have e0 : FD.gram τ.1 X.Gm y = yᵀ * (X.Gm.map τ.1 * yᴴᵀ) := by
      ext a b
      simp only [FD.gram, hermC, FD.col, of_apply, mul_apply, transpose_apply, map_apply, Finset.mul_sum, mul_assoc,
        conjTranspose_apply, RCLike.star_def]
    rw [e0, hG, transpose_mul, transpose_mul, Matrix.neg_mul, Matrix.mul_neg]
  rw [mat_frMove θ W X k x ρ τ hρ, ← hx τ, e, e, conjTranspose_mul]
  congr 2
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_assoc]

theorem om_compact_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ k ∈ GinfC W, (∀ τ, s τ * compAt θ τ (Formalism.L2.Theta.mt W k) = compAt θ τ (Formalism.L2.Theta.mt W k) * s τ) → Reads θ V W hr X bas idx (om (1, k) f) (mu k • φ) (frMove θ W hr X k x) := by
  intro D ψ θ V W χV χW om hP mu hmu r g hr X bas idx hX hS x s hx hs f φ hf hR k hk hks
  subst hr
  have hstd := hP.weil.std
  obtain ⟨cW, cV, -⟩ := GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x s
    hx hs
  have hvac := GlobalTheory.AdTh.FockVac.isFockVacAt_of_reads D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x s
    hx hs f φ hf hR
  choose a ha using hP.expV
  choose b hb using hP.expW
  obtain ⟨n, hn⟩ := hP.even
  choose p hp hd using fun τ => GlobalTheory.VacuumCharacter.detPlus_one (n := 0) (s τ) (cW τ).1
  have hom := GlobalTheory.T.vacuum_character_positive_definite_source D ψ θ V W χV χW om hP.weil hP.inf hP.sigV hP.sigW s cV cW _ _ ha hb
    (fun τ => a τ + n) (fun τ => a τ - n) (fun τ => -(p τ + b τ))
    (fun τ => by rw [hn]; push_cast; ring) (fun τ => by rw [hn]; push_cast; ring)
    (fun τ => by rw [hp]; push_cast; ring) f hf hvac 1 (one_mem _) k hk hks
  have hx' := isONFr_frMove hP.inf W X hX k x hx
  have hs' : IsInvOf W rfl X (frMove θ W rfl X k x) s := fun ρ τ h => by
    have e1 : s ρ * mat x τ = -(mat x τ * sgnM X) := hs ρ τ h
    show s ρ * _ = _
    rw [mat_frMove θ W X k x ρ τ h, ← Matrix.mul_assoc, hks, Matrix.mul_assoc, e1, Matrix.mul_neg, Matrix.mul_assoc]
  have h2 := GlobalTheory.AdTh.reads_two_frames D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x _ s hx hx' hs hs'
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt W k)) (fun ρ τ h => mat_frMove θ W X k x ρ τ h) f φ hR
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.VacuumCharacter.exists_root hP.inf W
    (fun τ => (GlobalTheory.SmoothForms.RealPts.gramAt_unit W τ).ne_zero) k hk
  have hmk : mu k = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt W k)).det ^ a τ := by rw [hmu.2 k y hy, hyv χV a ha]
  have h3 := fun c : ℂ => (GlobalTheory.AdTh.reads_linear_injective D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS
    _ hx' _ _ _ _ h2 h2).1 c 0
  simp only [zero_smul, add_zero] at h3
  rw [hom]
  convert h3 _ using 1
  rw [smul_smul, hmk, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have d2 := (hd τ 1 _ (hks τ)).2
  have h0 : (compAt θ τ (Formalism.L2.Theta.mt W k)).det ≠ 0 := by
    have := congrArg Matrix.det (GlobalTheory.UnitaryChar.compAt_mt_mul θ W τ k k⁻¹)
    rw [mul_inv_cancel, GlobalTheory.UnitaryChar.compAt_mt_one, det_one, det_mul] at this
    exact left_ne_zero_of_mul_eq_one this.symm
  have hn2 : V.rank / 2 = n := by omega
  rw [d2] at h0
  rw [GlobalTheory.UnitaryChar.compAt_mt_one, det_one, _root_.one_zpow, mul_one, hn2]
  conv_lhs => rw [d2]
  have hA := left_ne_zero_of_mul h0
  have hB := right_ne_zero_of_mul h0
  generalize ((1 / 2 : ℂ) • (1 + s τ) * compAt θ τ (Formalism.L2.Theta.mt W k) + (1 / 2 : ℂ) • (1 - s τ)).det = A at hA ⊢
  generalize ((1 / 2 : ℂ) • (1 - s τ) * compAt θ τ (Formalism.L2.Theta.mt W k) + (1 / 2 : ℂ) • (1 + s τ)).det = B at hB ⊢
  rw [mul_zpow, zpow_add₀ hA, zpow_sub₀ hB, zpow_natCast, zpow_natCast, div_pow]
  have := pow_ne_zero n hA
  have := pow_ne_zero n hB
  field_simp

end GlobalTheory.AdTh.RealCompact
