import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAtSumLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.CoreSum

variable {D : D7}

theorem orthogonalSumAuxiliaryVectors_gramProjection_retraction {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (hiso : (frameMat B A d.ι)ᴴ * B.gram * frameMat B A d.ι = A.gram) (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E) :
    (A.gram⁻¹ * ((frameMat B A d.ι)ᴴ * B.gram)) *ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = y := by
  have h1 : A.gram⁻¹ * ((frameMat B A d.ι)ᴴ * B.gram) * frameMat B A d.ι = 1 := by
    rw [Matrix.mul_assoc, hiso, Matrix.nonsing_inv_mul _ (gram_isUnit_det A)]
  have h2 : A.gram⁻¹ * ((frameMat B A d.ι)ᴴ * B.gram) * d.a = 0 := by
    have := d.perp
    rw [cT_sig] at this
    rw [Matrix.mul_assoc, this, Matrix.mul_zero]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h2, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

theorem orthogonalSumAuxiliaryVectors_middleCoefficient_eq {A B : HSp D} {c : ℕ} {ε : D.host.E} (hε : ε ≠ 0) (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c)
    (hp : p.1 + p.1 + 1 = c) (u : Fin c → D.host.E) (t : D.host.E) (e : d.a *ᵥ u = d.a *ᵥ Pi.single p t) : u p = t := by
  have g := d.gram
  rw [cT_sig] at g
  have e2 := congrArg (fun w => ((d.a)ᴴ * B.gram) *ᵥ w) e
  simp only [Matrix.mulVec_mulVec, g] at e2
  have e3 := congrFun e2 p
  have key : ∀ w : Fin c → D.host.E, (antiDiagonalSignGramMatrix c ε *ᵥ w) p = ε * w p := by
    intro w
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single p]
    · simp only [antiDiagonalSignGramMatrix]
      rw [if_pos hp]
      simp
    · intro q _ hq
      have : ¬ (p.1 + q.1 + 1 = c) := fun h' => hq (Fin.ext (by omega))
      simp only [antiDiagonalSignGramMatrix]
      rw [if_neg this, zero_mul]
    · simp
  rw [key, key, Pi.single_eq_same] at e3
  exact mul_left_cancel₀ hε e3

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem besselCoreVertexLattice_eq_orthDecSumLattice (F : Frames G) (hF : Std F) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) :
    lat0 F ρ h = GlobalTheory.Core.Rk.SumBox.sumLatO (F.oB ρ h) (G.Λ (.core (2 * ρ + 2)))
      (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  have lat2 : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat (2 * ρ + 2) (by omega) h
  have hstair : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) ⟨ρ, by omega⟩ =
      G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹ := by
    unfold stairId
    rw [show 2 * ρ + 2 - 1 - ρ = ρ + 1 by omega]
  have hM := hF.aB ρ h
  have hz := hF.zB' ρ h
  ext x
  simp only [lat0, Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
    GlobalTheory.Core.Rk.SumBox.mem_sumLatO]
  rw [lat2]
  constructor
  · rintro ⟨y, hy, u, hu, hx⟩
    have hiso2 : (frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι)ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram *
        frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι = (G.V (.core (2 * ρ + 2))).gram := by
      rw [← hM, Matrix.conjTranspose_mul, ← (F.oB ρ h).isoA, ← (F.dB ρ h).iso]
      simp only [Matrix.mul_assoc]
    have hQ : (G.V (.core (2 * ρ + 2))).gram⁻¹ * ((frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι)ᴴ *
        (G.V (.grid (2 * ρ + 2) 0)).gram) * (F.dB ρ h).i₀ = (F.oB ρ h).qA := by
      rw [← hM, Matrix.conjTranspose_mul, OrthDec.qA, ← (F.dB ρ h).iso]
      simp only [Matrix.mul_assoc]
    have hqA : (F.oB ρ h).qA *ᵥ x = y := by
      rw [← hQ, ← Matrix.mulVec_mulVec, hx, orthogonalSumAuxiliaryVectors_gramProjection_retraction _ hiso2]
    have hline := F.line 0
    have hr : (negSp F.Lz).rank = 1 := hline.1
    let i0 : Fin (negSp F.Lz).rank := ⟨0, by rw [hr]; omega⟩
    have hsub : ∀ j : Fin (negSp F.Lz).rank, j = i0 := fun j => Fin.ext (by have := j.isLt; show j.1 = 0; omega)
    have hζ0 : F.ζ 0 i0 ≠ 0 := by
      intro h0
      apply hline.2
      have : F.ζ 0 = 0 := funext fun j => by rw [hsub j]; exact h0
      rw [this]
      simp
    have hqB : (F.oB ρ h).qB *ᵥ x = (((F.oB ρ h).qB *ᵥ x) i0 / F.ζ 0 i0) • F.ζ 0 := by
      funext j
      rw [hsub j, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hζ0]
    have hsplit : (F.oB ρ h).iA *ᵥ ((F.oB ρ h).qA *ᵥ x) + (F.oB ρ h).iB *ᵥ ((F.oB ρ h).qB *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, (F.oB ρ h).iA_qA_add, Matrix.one_mulVec]
    have hx2 : (F.dB ρ h).i₀ *ᵥ x = frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι *ᵥ y +
        (G.colDec (2 * ρ + 2) (by omega) h).a *ᵥ
          Pi.single ⟨ρ, by omega⟩ (((F.oB ρ h).qB *ᵥ x) i0 / F.ζ 0 i0) := by
      conv_lhs => rw [← hsplit, hqA, hqB]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul, hz]
      congr 1
      funext i
      simp only [Matrix.mulVec_single, Matrix.col_apply, MulOpposite.smul_eq_mul_unop, Pi.smul_apply, smul_eq_mul,
        MulOpposite.unop_op]
      ring
    have ha := add_left_cancel (hx.symm.trans hx2)
    have hc := GlobalTheory.AscFin.CoreSum.orthogonalSumAuxiliaryVectors_middleCoefficient_eq (neg_ne_zero.2 one_ne_zero) _ ⟨ρ, by omega⟩ (by simp; omega) u _ ha
    have hcJ := hu ⟨ρ, by omega⟩
    rw [hc, hstair] at hcJ
    refine ⟨(F.oB ρ h).qA *ᵥ x, hqA ▸ hy, (F.oB ρ h).qB *ᵥ x, ?_, hsplit⟩
    rw [hqB]
    exact Submodule.subset_span ⟨_, hcJ, F.ζ 0, Submodule.mem_span_singleton_self _, rfl⟩
  · rintro ⟨y, hy, b, hb, rfl⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
    refine Submodule.add_mem _ ⟨y, hy, 0, fun p => (stairId _ _ _ p).val.zero_mem, by simp⟩ ?_
    induction hb using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, hs, w, hw, rfl⟩ := hz
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      refine ⟨0, Submodule.zero_mem _, Pi.single ⟨ρ, by omega⟩ (r • s), fun p => ?_, ?_⟩
      · by_cases hp : p = ⟨ρ, by omega⟩
        · subst hp
          rw [Pi.single_eq_same, hstair]
          exact Submodule.smul_mem _ r hs
        · rw [Pi.single_eq_of_ne hp]
          exact (stairId _ _ _ p).val.zero_mem
      · rw [Matrix.mulVec_zero, zero_add, ← algebraMap_smul D.host.E r (F.ζ 0), Matrix.mulVec_smul, Matrix.mulVec_smul, hz]
        funext i
        rw [Algebra.smul_def r s]
        simp only [Matrix.mulVec_single, Matrix.col_apply, MulOpposite.smul_eq_mul_unop, Pi.smul_apply, smul_eq_mul,
          MulOpposite.unop_op]
        ring
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hz hz'
    | smul r z _ hz =>
      rw [← algebraMap_smul D.host.E r z, Matrix.mulVec_smul, algebraMap_smul]
      exact Submodule.smul_mem _ r hz

theorem besselCoreVertexLattice_splitsAlongOrthDecomposition : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), OrthAt (F.oB ρ h) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2)))
      (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) v := by
  intro D T L sc G F hF ρ h v
  rw [besselCoreVertexLattice_eq_orthDecSumLattice F hF ρ h]
  exact GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v

end GlobalTheory.AscFin.CoreSum
