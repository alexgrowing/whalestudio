import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibQ

section Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def mulVecHomeo {t : ℕ} (w : GL (Fin t) k) : (Fin t → k) ≃ₜ (Fin t → k) where
  toFun v := (w : Matrix (Fin t) (Fin t) k).mulVec v
  invFun v := ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v
  left_inv v := by
    show ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec ((w : Matrix (Fin t) (Fin t) k).mulVec v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv v := by
    show (w : Matrix (Fin t) (Fin t) k).mulVec (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem smInt_transform {t : ℕ} [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)]
    (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (Φ Ψ : (Fin t → k) → X) (B : X →ₗ[ℂ] Y) (A : Y →ₗ[ℂ] Y) (w : GL (Fin t) k)
    (lΦ : IsLocallyConstant Φ) (cΦ : HasCompactSupport Φ)
    (lΨ : IsLocallyConstant Ψ) (cΨ : HasCompactSupport Ψ)
    (h : ∀ v, B (Φ v) = A (B (Ψ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v)))) :
    B (smInt μ Φ) = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A (B (smInt μ Ψ)) := by
  have lG : IsLocallyConstant (B ∘ Ψ) := lΨ.comp B
  have cG : HasCompactSupport (B ∘ Ψ) := cΨ.comp_left (map_zero B)
  have lGL : IsLocallyConstant ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹)) := lG.comp_continuous (mulVecHomeo w⁻¹).continuous
  have cGL : HasCompactSupport ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹)) := cG.comp_homeomorph (mulVecHomeo w⁻¹)
  calc B (smInt μ Φ) = smInt μ (B ∘ Φ) := (SmIntEl.smInt_linear μ B lΦ cΦ).symm
    _ = smInt μ (A ∘ ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹))) := congrArg (smInt μ) (funext h)
    _ = A (smInt μ ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹))) := SmIntEl.smInt_linear μ A lGL cGL
    _ = A (((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • smInt μ (B ∘ Ψ)) :=
        congrArg A (GlobalTheory.T.smooth_integral_linear_change k t μ w (B ∘ Ψ) lG cG)
    _ = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A (smInt μ (B ∘ Ψ)) := map_smul A _ _
    _ = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A (B (smInt μ Ψ)) :=
        congrArg (fun z => ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A z) (SmIntEl.smInt_linear μ B lΨ cΨ)

end Abstract

section Group

variable (k : Type) [Field k]

theorem point_eq (i t : ℕ) (q g : GL (Fin (i + t)) k) (y : Fin (i + t) → k) (x : Fin i → k) (u : Fin t → k)
    (hx : ((q⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t u) :
    uM k (i + t) y * levi k (i + t) (q * g) =
      levi k (i + t) q * uM k (i + t) (topV k i t x) * (uM k (i + t) (midV k i t u) * levi k (i + t) g) := by
  have h := levi_mul_uM k (i + t) q⁻¹ y
  rw [hx, uM_add, map_inv] at h
  have h2 : uM k (i + t) y =
      levi k (i + t) q * (uM k (i + t) (topV k i t x) * uM k (i + t) (midV k i t u) * (levi k (i + t) q)⁻¹) :=
    inv_mul_eq_iff_eq_mul.mp h
  calc uM k (i + t) y * levi k (i + t) (q * g)
      = levi k (i + t) q * (uM k (i + t) (topV k i t x) * uM k (i + t) (midV k i t u) * (levi k (i + t) q)⁻¹) *
          (levi k (i + t) q * levi k (i + t) g) := by rw [map_mul, ← h2]
    _ = _ := by group

end Group

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem clT_extTensor (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (a : GL (Fin i) k) (x : Fin i → k) (w : GL (Fin t) k) (z : V ⊗[ℂ] W) :
    clT τ W (extTensor τ σ (levi k i a * uM k i x, w) z) =
      extTensor (psiMinus k τ) σ (a, w) (clT τ W z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v u =>
    have e : (twKer τ (MirUin k i) 1).mkQ (τ (uM k i x) v) = (twKer τ (MirUin k i) 1).mkQ v := by
      refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨uM k i x, uM_mem k i x⟩, v, ?_⟩)
      simp
    have e2 : (twKer τ (MirUin k i) 1).mkQ (τ (levi k i a * uM k i x) v) =
        psiMinus k τ a ((twKer τ (MirUin k i) 1).mkQ v) := by
      rw [← e, map_mul]
      rfl
    simp only [clT, extTensor_tmul, LinearMap.rTensor_tmul]
    rw [e2]

theorem fibV_mul (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (q : Qp k i t) (g : GL (Fin (i + t)) k) (v u : Fin t → k) (x : Fin i → k)
    (hx : (((q : GL (Fin (i + t)) k)⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec (midV k i t v) =
      topV k i t x + midV k i t u) :
    fibV f ((q : GL (Fin (i + t)) k) * g) v =
      extTensor τ σ (levi k i (qBlocks k i t q).1 * uM k i x, (qBlocks k i t q).2) (fibV f g u) := by
  obtain ⟨m1, p1⟩ := GlobalTheory.T.levi_block_mem_parabolic k i t q
  obtain ⟨m2, p2⟩ := GlobalTheory.T.unipotent_top_mem_parabolic k i t x
  have key := f.1.1.2 ((⟨_, m1⟩ : HPG k i t) * ⟨_, m2⟩) (uM k (i + t) (midV k i t u) * levi k (i + t) g)
  have e : pgProj k i t ((⟨_, m1⟩ : HPG k i t) * ⟨_, m2⟩) =
      (levi k i (qBlocks k i t q).1 * uM k i x, (qBlocks k i t q).2) := by
    rw [map_mul, p1, p2]
    simp
  calc fibV f ((q : GL (Fin (i + t)) k) * g) v
      = f.1.1.1 (levi k (i + t) (q : GL (Fin (i + t)) k) * uM k (i + t) (topV k i t x) *
          (uM k (i + t) (midV k i t u) * levi k (i + t) g)) :=
        congrArg f.1.1.1 (point_eq k i t _ g _ x u hx)
    _ = extTensor τ σ (pgProj k i t ((⟨_, m1⟩ : HPG k i t) * ⟨_, m2⟩)) (fibV f g u) := key
    _ = _ := congrArg (fun y => extTensor τ σ y (fibV f g u)) e

end Rep

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (q : Qp k i t) (g : GL (Fin (i + t)) k), fibInt μ f ((q : GL (Fin (i + t)) k) * g) = qRep τ σ q (fibInt μ f g) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ f q g
  have h1 := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ f ((q : GL (Fin (i + t)) k) * g)
  have h2 := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ f g
  have hpt : ∀ v, clT τ W (fibV f ((q : GL (Fin (i + t)) k) * g) v) =
      extTensor (psiMinus k τ) σ ((qBlocks k i t q).1, (qBlocks k i t q).2)
        (clT τ W (fibV f g ((((qBlocks k i t q).2⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v))) := by
    intro v
    obtain ⟨x, hx⟩ := GlobalTheory.T.mulVec_mid_block_decomp k i t q⁻¹ v
    have hb : (qBlocks k i t q⁻¹).2 = (qBlocks k i t q).2⁻¹ := by
      rw [map_inv, Prod.snd_inv]
    rw [hb] at hx
    have e := fibV_mul τ σ f q g v _ x hx
    exact (congrArg (clT τ W) e).trans (clT_extTensor τ σ _ x _ _)
  exact smInt_transform μ _ _ (clT τ W)
    (extTensor (psiMinus k τ) σ ((qBlocks k i t q).1, (qBlocks k i t q).2)) (qBlocks k i t q).2
    h1.1 h1.2 h2.1 h2.2 hpt

end GlobalTheory.CompanionTheory.BZPsiPG.FibQ

end
