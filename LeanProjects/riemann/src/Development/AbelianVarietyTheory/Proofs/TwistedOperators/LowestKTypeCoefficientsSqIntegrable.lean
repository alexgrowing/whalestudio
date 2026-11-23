import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasLevW
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.SubmatrixMemUJsetIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarUpqHasOmegaDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealCoefSq

section Frame

variable {p q n : ℕ}

def conjMul (L : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ) (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (hBL : B * L = 1)
    (hLB : L * B = 1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ ≃* Matrix (Fin n) (Fin n) ℂ where
  toFun X := L * X * B
  invFun Y := B * Y * L
  left_inv X := by
    show B * (L * X * B) * L = X
    rw [show B * (L * X * B) * L = (B * L) * X * (B * L) by simp only [Matrix.mul_assoc], hBL]; simp
  right_inv Y := by
    show L * (B * Y * L) * B = Y
    rw [show L * (B * Y * L) * B = (L * B) * Y * (L * B) by simp only [Matrix.mul_assoc], hLB]; simp
  map_mul' X Y := by
    show L * (X * Y) * B = L * X * B * (L * Y * B)
    rw [show L * X * B * (L * Y * B) = L * X * (B * L) * Y * B by simp only [Matrix.mul_assoc], hBL]
    simp only [Matrix.mul_one, Matrix.mul_assoc]

def unitsConj (L : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ) (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (hBL : B * L = 1)
    (hLB : L * B = 1) : GL (Fin p ⊕ Fin q) ℂ ≃ₜ* (Matrix (Fin n) (Fin n) ℂ)ˣ where
  toMulEquiv := Units.mapEquiv (conjMul L B hBL hLB)
  continuous_toFun := Units.continuous_map (f := (conjMul L B hBL hLB).toMonoidHom)
    (show Continuous fun X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ => L * X * B from
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  continuous_invFun := Units.continuous_map (f := (conjMul L B hBL hLB).symm.toMonoidHom)
    (show Continuous fun Y : Matrix (Fin n) (Fin n) ℂ => B * Y * L from
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

def frameInv (ε : Fin n → Bool) (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ :=
  Formalism.REAL.Jm ε * Bᴴ * Formalism.UG.Jpq p q

theorem Jpq_conjTranspose : (Formalism.UG.Jpq p q)ᴴ = Formalism.UG.Jpq p q := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

variable {ε : Fin n → Bool} {B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ}

theorem frameInv_mul (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε) : frameInv ε B * B = 1 := by
  simp only [frameInv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Bᴴ, hB, Formalism.REAL.Jm_mul_self]

theorem mul_frameInv (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε) (hn : p + q = n) : B * frameInv ε B = 1 := by
  have e : Fin n ≃ Fin p ⊕ Fin q := (finCongr hn.symm).trans finSumFinEquiv.symm
  exact (Matrix.mul_eq_one_comm_of_equiv e).1 (frameInv_mul hB)

theorem frameInv_herm (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε) (hn : p + q = n) :
    (frameInv ε B)ᴴ * Formalism.REAL.Jm ε * frameInv ε B = Formalism.UG.Jpq p q := by
  have h1 := mul_frameInv hB hn
  have : (frameInv ε B)ᴴ * Formalism.REAL.Jm ε * frameInv ε B =
      Formalism.UG.Jpq p q * (B * frameInv ε B) := by
    simp only [frameInv, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jpq_conjTranspose,
      Formalism.REAL.Jm_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), Formalism.REAL.Jm_mul_self, Matrix.one_mul]
  rw [this, h1, Matrix.mul_one]

theorem inUJ_conj (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε) (hn : p + q = n)
    {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) :
    Formalism.REAL.inUJ ε (frameInv ε B * g * B) := by
  show (frameInv ε B * g * B)ᴴ * Formalism.REAL.Jm ε * (frameInv ε B * g * B) = Formalism.REAL.Jm ε
  calc (frameInv ε B * g * B)ᴴ * Formalism.REAL.Jm ε * (frameInv ε B * g * B)
      = Bᴴ * (gᴴ * ((frameInv ε B)ᴴ * Formalism.REAL.Jm ε * frameInv ε B) * g) * B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [frameInv_herm hB hn, hg, hB]

theorem upq_conj (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε) (hn : p + q = n)
    {y : Matrix (Fin n) (Fin n) ℂ} (hy : Formalism.REAL.inUJ ε y) :
    (B * y * frameInv ε B)ᴴ * Formalism.UG.Jpq p q * (B * y * frameInv ε B) = Formalism.UG.Jpq p q := by
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  calc (B * y * frameInv ε B)ᴴ * Formalism.UG.Jpq p q * (B * y * frameInv ε B)
      = (frameInv ε B)ᴴ * (yᴴ * (Bᴴ * Formalism.UG.Jpq p q * B) * y) * frameInv ε B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.UG.Jpq p q := by rw [hB, hy', frameInv_herm hB hn]

def frameEquiv (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε)
    (hn : p + q = n) : UpqT p q ≃ₜ* Formalism.REAL.UJ ε where
  toFun g := ⟨unitsConj (frameInv ε B) B (mul_frameInv hB hn) (frameInv_mul hB) (g : Formalism.UG.Upq p q).1,
    inUJ_conj hB hn (g : Formalism.UG.Upq p q).2⟩
  invFun k := (⟨(unitsConj (frameInv ε B) B (mul_frameInv hB hn) (frameInv_mul hB)).symm k.1,
    upq_conj hB hn k.2⟩ : Formalism.UG.Upq p q)
  left_inv g := Subtype.ext ((unitsConj _ _ _ _).symm_apply_apply _)
  right_inv k := Subtype.ext ((unitsConj _ _ _ _).apply_symm_apply _)
  map_mul' g k := Subtype.ext (map_mul (unitsConj _ _ _ _) _ _)
  continuous_toFun := ((unitsConj _ _ _ _).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((unitsConj _ _ _ _).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem umat_frameEquiv (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε) (hn : p + q = n) (b : UpqT p q) :
    umat (frameEquiv B hB hn b) = frameInv ε B * UpqT.mat b * B := rfl

end Frame

section Haar

variable {p q n : ℕ} {ε : Fin n → Bool} {B B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ}

theorem frameEquiv_conj (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε)
    (hB' : B'ᴴ * Formalism.UG.Jpq p q * B' = Formalism.REAL.Jm ε) (hn : p + q = n) :
    ∃ u : Formalism.REAL.UJ ε, ∀ b, frameEquiv B' hB' hn b = u * frameEquiv B hB hn b * u⁻¹ := by
  have hu : Formalism.REAL.inUJ ε (frameInv ε B' * B) := by
    show (frameInv ε B' * B)ᴴ * Formalism.REAL.Jm ε * (frameInv ε B' * B) = Formalism.REAL.Jm ε
    calc (frameInv ε B' * B)ᴴ * Formalism.REAL.Jm ε * (frameInv ε B' * B)
        = Bᴴ * ((frameInv ε B')ᴴ * Formalism.REAL.Jm ε * frameInv ε B') * B := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [frameInv_herm hB' hn, hB]
  have hw : Formalism.REAL.inUJ ε (frameInv ε B * B') := by
    show (frameInv ε B * B')ᴴ * Formalism.REAL.Jm ε * (frameInv ε B * B') = Formalism.REAL.Jm ε
    calc (frameInv ε B * B')ᴴ * Formalism.REAL.Jm ε * (frameInv ε B * B')
        = B'ᴴ * ((frameInv ε B)ᴴ * Formalism.REAL.Jm ε * frameInv ε B) * B' := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [frameInv_herm hB hn, hB']
  have huw : Formalism.REAL.indefiniteUnitaryMk ε _ hu * Formalism.REAL.indefiniteUnitaryMk ε _ hw = 1 := by
    apply Formalism.REAL.indefinite_unitary_ext
    rw [Subgroup.coe_mul, Units.val_mul, Formalism.REAL.indefiniteUnitaryMk_val, Formalism.REAL.indefiniteUnitaryMk_val, Subgroup.coe_one,
      Units.val_one]
    rw [show frameInv ε B' * B * (frameInv ε B * B') = frameInv ε B' * (B * frameInv ε B) * B' by
      simp only [Matrix.mul_assoc], mul_frameInv hB hn, Matrix.mul_one, frameInv_mul hB']
  refine ⟨Formalism.REAL.indefiniteUnitaryMk ε _ hu, fun b => ?_⟩
  rw [inv_eq_of_mul_eq_one_right huw]
  apply Formalism.REAL.indefinite_unitary_ext
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, Formalism.REAL.indefiniteUnitaryMk_val,
    Formalism.REAL.indefiniteUnitaryMk_val]
  change frameInv ε B' * UpqT.mat b * B' = frameInv ε B' * B * (frameInv ε B * UpqT.mat b * B) * (frameInv ε B * B')
  rw [show frameInv ε B' * B * (frameInv ε B * UpqT.mat b * B) * (frameInv ε B * B') =
      frameInv ε B' * (B * frameInv ε B) * UpqT.mat b * (B * frameInv ε B) * B' by simp only [Matrix.mul_assoc],
    mul_frameInv hB hn, Matrix.mul_one, Matrix.mul_one]

theorem map_frameEquiv (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε)
    (hB' : B'ᴴ * Formalism.UG.Jpq p q * B' = Formalism.REAL.Jm ε) (hn : p + q = n) (ν : Measure (UpqT p q)) (c : NNReal)
    (hc : ν.map (frameEquiv B hB hn) = (c : ENNReal) • Formalism.REAL.muG ε) :
    ν.map (frameEquiv B' hB' hn) = (c : ENNReal) • Formalism.REAL.muG ε := by
  haveI : BorelSpace (UpqT p q) := ⟨rfl⟩
  obtain ⟨u, hu⟩ := frameEquiv_conj hB hB' hn
  have hm : Measurable (frameEquiv B hB hn) := (frameEquiv B hB hn).continuous.measurable
  have e : (frameEquiv B' hB' hn : UpqT p q → Formalism.REAL.UJ ε) =
      (fun g => g * u⁻¹) ∘ (fun g => u * g) ∘ frameEquiv B hB hn := funext fun b => by
    simp only [Function.comp_apply, hu]
  rw [e, ← Measure.map_map (measurable_mul_const _) ((measurable_const_mul _).comp hm),
    ← Measure.map_map (measurable_const_mul _) hm, hc, Measure.map_smul, Measure.map_smul,
    map_mul_left_eq_self, Formalism.REAL.indefinite_unitary_unimodular n ε u⁻¹]

theorem sq_of_isFdeg {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure (Formalism.REAL.UJ ε)}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ} (h : IsFdeg μ σ d) (v : H) (hv : ‖v‖ = 1) :
    Integrable (fun g => ‖coefOn σ v v g‖ ^ 2) μ ∧ ∫ g, ‖coefOn σ v v g‖ ^ 2 ∂μ = 1 / d := by
  obtain ⟨-, h⟩ := h
  obtain ⟨h1, h2⟩ := h v v v v
  have e1 : (fun g : Formalism.REAL.UJ ε => coefOn σ v v g * star (coefOn σ v v g)) =
      fun g => (((‖coefOn σ v v g‖ ^ 2 : ℝ)) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e1] at h1 h2
  refine ⟨by have h3 := h1.re; simp only [RCLike.re_to_complex, Complex.ofReal_re] at h3; exact h3, ?_⟩
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, hv] at h2
  apply Complex.ofReal_injective
  rw [h2]
  push_cast
  ring

end Haar

section Model

open GlobalTheory.AdelicScalar

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → SPar}

theorem frame_herm (M : DSModel W S) {Fr : Frames W} (hFr : IsFrames W Fr) (ρ : D.what₂.Tau) :
    (Fr ρ * (M.fr ρ)⁻¹)ᴴ * Formalism.UG.Jpq (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 * (Fr ρ * (M.fr ρ)⁻¹) =
      Formalism.REAL.Jm (M.ε ρ) := by
  have hd : IsUnit (M.fr ρ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  calc (Fr ρ * (M.fr ρ)⁻¹)ᴴ * Formalism.UG.Jpq (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 * (Fr ρ * (M.fr ρ)⁻¹)
      = ((M.fr ρ)⁻¹)ᴴ * ((Fr ρ)ᴴ * Formalism.UG.Jpq (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 * Fr ρ) * (M.fr ρ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr ρ)⁻¹)ᴴ * ((M.fr ρ)ᴴ * Formalism.REAL.Jm (M.ε ρ) * M.fr ρ) * (M.fr ρ)⁻¹ := by rw [hFr ρ, M.fr_gram ρ]
    _ = (M.fr ρ * (M.fr ρ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε ρ) * (M.fr ρ * (M.fr ρ)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (M.ε ρ) := by rw [Matrix.mul_nonsing_inv _ hd]; simp

theorem rep_realMat (M : DSModel W S) {Fr : Frames W} (hFr : IsFrames W Fr) (ρ : D.what₂.Tau)
    (hn : (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) (b : Upq W ρ) :
    M.rep ρ (realMat W Fr ρ b) = M.σ ρ (umat (frameEquiv (Fr ρ * (M.fr ρ)⁻¹) (frame_herm M hFr ρ) hn b)) := by
  rw [umat_frameEquiv]
  unfold DSModel.rep realMat conjFrame frameInv
  congr 1
  have hd : IsUnit (M.fr ρ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  have hG : (gramAt D W ρ)⁻¹ = (M.fr ρ)⁻¹ * Formalism.REAL.Jm (M.ε ρ) * ((M.fr ρ)⁻¹)ᴴ := by
    apply Matrix.inv_eq_right_inv
    rw [← M.fr_gram ρ]
    calc (M.fr ρ)ᴴ * Formalism.REAL.Jm (M.ε ρ) * M.fr ρ * ((M.fr ρ)⁻¹ * Formalism.REAL.Jm (M.ε ρ) * ((M.fr ρ)⁻¹)ᴴ)
        = (M.fr ρ)ᴴ * Formalism.REAL.Jm (M.ε ρ) * (M.fr ρ * (M.fr ρ)⁻¹) * Formalism.REAL.Jm (M.ε ρ) * ((M.fr ρ)⁻¹)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = (M.fr ρ)ᴴ * (Formalism.REAL.Jm (M.ε ρ) * Formalism.REAL.Jm (M.ε ρ)) * ((M.fr ρ)⁻¹)ᴴ := by
          rw [Matrix.mul_nonsing_inv _ hd]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = ((M.fr ρ)⁻¹ * M.fr ρ)ᴴ := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one, Matrix.conjTranspose_mul]
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ hd, Matrix.conjTranspose_one]
  rw [hG, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (M.fr ρ) ((M.fr ρ)⁻¹), Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]

theorem exists_coef_sq (M : DSModel W S) (ρ : D.what₂.Tau)
    (hn : (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : Measure (Upq W ρ), Lev.IsMinf mR →
      ∀ v : M.H ρ, ‖v‖ = 1 →
        Integrable (fun b => ‖⟪v, M.rep ρ (realMat W Fr ρ b) v⟫_ℂ‖ ^ 2) mR ∧
          ∫ b, ‖⟪v, M.rep ρ (realMat W Fr ρ b) v⟫_ℂ‖ ^ 2 ∂mR = δ := by
  classical
  haveI := (GlobalTheory.UpqTopology.upq_lcsc (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2).1
  haveI : BorelSpace (Upq W ρ) := ⟨rfl⟩
  by_cases h0 : ∃ Fr : Frames W, IsFrames W Fr ∧ ∃ mR : Measure (Upq W ρ), Lev.IsMinf mR
  swap
  · exact ⟨1, one_pos, fun Fr hFr mR hmR => absurd ⟨Fr, hFr, mR, hmR⟩ h0⟩
  obtain ⟨Fr₀, hFr₀, mR₀, hmR₀⟩ := h0
  haveI := hmR₀.1
  haveI : (mR₀.map (frameEquiv _ (frame_herm M hFr₀ ρ) hn)).IsHaarMeasure :=
    (frameEquiv _ (frame_herm M hFr₀ ρ) hn).isHaarMeasure_map mR₀
  have hc := Measure.isMulLeftInvariant_eq_smul (mR₀.map (frameEquiv _ (frame_herm M hFr₀ ρ) hn))
    (Formalism.REAL.muG (M.ε ρ))
  have hcpos := Measure.haarScalarFactor_pos_of_isHaarMeasure (mR₀.map (frameEquiv _ (frame_herm M hFr₀ ρ) hn))
    (Formalism.REAL.muG (M.ε ρ))
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ (M.ε ρ) (M.lam ρ) (M.H ρ) (M.σ ρ) (M.ds ρ) _ hcpos
  refine ⟨1 / d, one_div_pos.2 hd.1, fun Fr hFr mR hmR v hv => ?_⟩
  obtain rfl : mR = mR₀ := GlobalTheory.LevelMeasure.isMinf_unique hmR₀ hmR
  have e2 := map_frameEquiv (frame_herm M hFr₀ ρ) (frame_herm M hFr ρ) hn mR _ hc
  set Φ := frameEquiv _ (frame_herm M hFr ρ) hn
  have hme : MeasurableEmbedding Φ := Φ.toHomeomorph.measurableEmbedding
  have hk : (fun b => ‖⟪v, M.rep ρ (realMat W Fr ρ b) v⟫_ℂ‖ ^ 2) =
      (fun g => ‖coefOn (ε := M.ε ρ) (M.σ ρ) v v g‖ ^ 2) ∘ Φ := funext fun b => by
    simp only [Function.comp_apply, rep_realMat M hFr ρ hn b]
    rfl
  obtain ⟨h1, h2⟩ := sq_of_isFdeg hd v hv
  rw [← e2] at h1 h2
  rw [hk]
  exact ⟨hme.integrable_map_iff.1 h1, by rw [← h2, hme.integral_map]; rfl⟩

end Model

theorem lowestKType_coefficients_sq_integrable : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.Hk3.Core R F → RealLowestKTypeCoeffSquareIntegrable R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i σ ρ
  have hn : ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = (Wc D i).rank :=
    (GlobalTheory.AdelicScalar.sig_add i ρ).trans (Formalism.IndefR.FWT.rank_Wc i).symm
  obtain ⟨δ, hδ, h⟩ := exists_coef_sq (R.MW i σ) ρ hn
  exact ⟨δ, hδ, fun Fr hFr mR hmR e he => h Fr hFr mR hmR _ he⟩

end GlobalTheory.RealCoefSq
