import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.I0M
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramEqOfInst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarEqHostConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedFrameGramOrth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoCptXZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalIffSecondModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RangeBesselAnisotropicEmbeddingEqSecondModelSubgStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHypDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CexpTwoPiINegInvNatSmulAddStar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Unscaled

variable {D : D7}

def rescale {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (μ : D.host.E) (hμ : μ ≠ 0) : HypDec S S₀ ρ where
  e := μ • d.e
  e' := (star μ)⁻¹ • d.e'
  i₀ := d.i₀
  ee := by simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, d.ee, smul_zero]
  e'e' := by simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, d.e'e', smul_zero]
  e'e := by
    simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, d.e'e, smul_smul, star_inv₀, star_star,
      mul_inv_cancel₀ hμ, one_smul]
  iso := d.iso
  i₀e := by simp only [Matrix.mul_smul, d.i₀e, smul_zero]
  i₀e' := by simp only [Matrix.mul_smul, d.i₀e', smul_zero]
  rank_add := d.rank_add

end GlobalTheory.Core.Mi.Unscaled

namespace GlobalTheory.Core.Mi

open GlobalTheory.Core.SBesEx GlobalTheory.Core.Mi.Unscaled in

theorem exists_sBes_scaled_dual : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀), IdE X → IsStdChar D ψ (-1) → ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∀ (μ : D.host.E) (vA : Vol (D.sp.X 0)), μ ≠ 0 → ∃ B : SBes X h u ψ (D.sp.X 0), B.Adapted tr.wt ∧ B.vA = vA ∧ (∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) ∧ (∀ k (a : Fin D.R.rS), B.d.e k a = μ * lam ^ (D.R.rS - (a : ℕ)) * X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) ∧ ∀ k (a : Fin D.R.rS), B.d.e' k a = (star (μ * lam ^ (D.R.rS - (a : ℕ))))⁻¹ * X.ιE (X.fR a (Fin.cast (rank_eq X h) k)) := by
  intro D X h u ψ F₀ tr hE hψ
  obtain ⟨lam, hlam, hP⟩ := GlobalTheory.Core.Mi.tiepsi_sign D X h u ψ hE hψ
  have hg : ((X.B.g : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.Pf.modulus_g_ne_zero X)
  have hl0 : lam ≠ 0 := by
    rcases hlam with hl | hl <;> rw [hl]
    · exact hg
    · exact neg_ne_zero.2 hg
  refine ⟨lam, hlam, fun μ vA hμ => ?_⟩
  obtain ⟨L, t, ht, hL1, hz0, hLg⟩ := GlobalTheory.RankOneLine.exists_line D X u
  obtain ⟨⟨V₀, o⟩⟩ := GlobalTheory.OrthSumExists.exists_orthDec D (D.sp.X 0) L
  obtain ⟨d₀, hde, hde', hdi⟩ := GlobalTheory.Core.SBesEx.exists_hypDec D X h u F₀ tr t lam ht hl0 (GlobalTheory.Core.SBesEx.cY_isom D X h hE)
    (GlobalTheory.Core.Mi.transported_frame_gram_orth D X u F₀ tr) L hL1 hLg V₀ o
  have hcard : Fintype.card (Fin L.rank) = 1 := by rw [Fintype.card_fin, hL1]
  have hz₀ : d₀.i₀ *ᵥ vecB o (zeta L) = t • cY X h (X.zu u) := by
    rw [vecB, Matrix.mulVec_mulVec, hdi, i0M, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, o.qA_iB, o.qB_iB,
      Matrix.mul_zero, zero_add, Matrix.mul_one]
    funext k
    simp only [Matrix.mulVec, dotProduct, zM, zeta, mul_one, Finset.sum_const, Finset.card_univ, hcard, one_smul,
      Pi.smul_apply, smul_eq_mul]
  have hline₀ : IsLineVec L (zeta L) := by
    refine ⟨hL1, ?_⟩
    simp only [zeta, hLg, dotProduct, Matrix.mulVec, Pi.star_apply, star_one, one_mul, mul_one, Finset.sum_const,
      Finset.card_univ, hcard, one_smul]
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 ht) ht) hz0
  have ht' : μ * t⁻¹ ≠ 0 := mul_ne_zero hμ (inv_ne_zero ht)
  set d := rescale d₀ (μ * t⁻¹) ht' with hd
  set ζ : Fin L.rank → D.host.E := (μ * t⁻¹) • zeta L with hζ
  have hline : IsLineVec L ζ := by
    refine ⟨hline₀.1, ?_⟩
    rw [hζ, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    exact mul_ne_zero (star_ne_zero.2 ht') (mul_ne_zero ht' hline₀.2)
  have hde1 : d.e = eM X h μ lam := by
    funext k a
    show ((μ * t⁻¹) • d₀.e) k a = _
    rw [hde]
    simp only [Matrix.smul_apply, eM, scl, smul_eq_mul]
    field_simp
  have hde1' : d.e' = e'M X h μ lam := by
    funext k a
    show ((star (μ * t⁻¹))⁻¹ • d₀.e') k a = _
    rw [hde']
    simp only [Matrix.smul_apply, e'M, scl, smul_eq_mul, star_mul', star_inv₀, inv_inv, mul_inv]
    have hst : star t ≠ 0 := star_ne_zero.2 ht
    field_simp
  have hz : d.i₀ *ᵥ vecB o ζ = μ • cY X h (X.zu u) := by
    show d₀.i₀ *ᵥ (o.iB *ᵥ ((μ * t⁻¹) • zeta L)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← vecB, hz₀, smul_smul, inv_mul_cancel_right₀ ht]
  refine ⟨SBes.mk V₀ L d o ζ hline (GlobalTheory.Unf.DefCpt.coCpt_X_zero D) vA
    (GlobalTheory.Unf.Inhab.nonempty_volN d).some (GlobalTheory.T.mem_flagUnipotentRadical_iff_secondModel D X h u μ lam hμ hl0 hE V₀ d hde1)
    (GlobalTheory.T.range_besselAnisotropicEmbedding_eq_secondModelSubgroup D X h u μ lam hμ hl0 hE V₀ L d o ζ hline hde1 hde1' hz)
    (hP μ hμ V₀ L d o ζ hde1 hde1' hz), ?_, rfl, ?_, ?_, ?_⟩
  · intro k j
    show (d₀.i₀ * o.iA) k j = _
    rw [hdi, i0M, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, o.qA_iA, o.qB_iA, Matrix.mul_zero, add_zero,
      Matrix.mul_one]
    rfl
  · intro k
    show (d.i₀ *ᵥ vecB o ζ) k = _
    rw [hz]
    rfl
  · intro k a
    show d.e k a = _
    rw [hde1]
    rfl
  · intro k a
    show d.e' k a = _
    rw [hde1']
    rfl

theorem exists_sBes_unscaled_dual : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀), IdE X → IsStdChar D ψ (-1) → ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∃ B : SBes X h u ψ (D.sp.X 0), B.Adapted tr.wt ∧ (∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) ∧ (∀ k (a : Fin D.R.rS), B.d.e k a = lam ^ (D.R.rS - (a : ℕ)) * X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) ∧ ∀ k (a : Fin D.R.rS), B.d.e' k a = (star (lam ^ (D.R.rS - (a : ℕ))))⁻¹ * X.ιE (X.fR a (Fin.cast (rank_eq X h) k)) := by
  intro D X h u ψ F₀ tr hE hψ
  obtain ⟨lam, hlam, hB⟩ := exists_sBes_scaled_dual D X h u ψ F₀ tr hE hψ
  obtain ⟨B, hA, -, hz, he, he'⟩ := hB 1 (GlobalTheory.Unf.Inhab.nonempty_vol _).some one_ne_zero
  simp only [one_mul] at hz he he'
  exact ⟨lam, hlam, B, hA, hz, he, he'⟩

theorem exists_sBes_unscaled : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀), IdE X → IsStdChar D ψ (-1) → ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∃ B : SBes X h u ψ (D.sp.X 0), B.Adapted tr.wt ∧ (∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) ∧ ∀ k (a : Fin D.R.rS), B.d.e k a = lam ^ (D.R.rS - (a : ℕ)) * X.ιE (X.eR a (Fin.cast (rank_eq X h) k)) := by
  intro D X h u ψ F₀ tr hE hψ
  obtain ⟨lam, hlam, B, hA, hz, he, -⟩ := exists_sBes_unscaled_dual D X h u ψ F₀ tr hE hψ
  exact ⟨lam, hlam, B, hA, hz, he⟩

end GlobalTheory.Core.Mi

end
