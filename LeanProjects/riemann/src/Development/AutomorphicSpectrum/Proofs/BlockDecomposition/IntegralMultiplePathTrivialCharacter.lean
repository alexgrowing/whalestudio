import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRs
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum.Level

variable {D : D7} {r : ℕ}

def eFin (D : D7) : AF D.host.F := 1 - GlobalTheory.FinTranslate.eInf D

theorem eFin_mul (D : D7) (x : AF D.host.F) : eFin D * x = pairA D.host.F 0 (sndA D.host.F x) := by
  show ((1 : Ainf D.host.F × Af D.host.F) - (1, 0)) * (x : Ainf D.host.F × Af D.host.F) =
    ((0 : Ainf D.host.F), (x : Ainf D.host.F × Af D.host.F).2)
  refine Prod.ext ?_ ?_
  · show ((1 : Ainf D.host.F) - 1) * x.1 = 0
    rw [sub_self, zero_mul]
  · show ((1 : Af D.host.F) - 0) * x.2 = x.2
    rw [sub_zero, one_mul]

theorem finPart_eInf (D : D7) : finPart D (GlobalTheory.FinTranslate.eInf D • (1 : AE D)) = 0 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (GlobalTheory.FinTranslate.eInf D ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul]
  exact TensorProduct.zero_tmul _ _

theorem infPart_eInf (D : D7) : infPart D (GlobalTheory.FinTranslate.eInf D • (1 : AE D)) = 1 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      (GlobalTheory.FinTranslate.eInf D ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem rs_one {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) :
    rs σ 1 = GlobalTheory.FinTranslate.eInf D • (1 : AE D) := by
  refine sub_eq_zero.mp (hσ.ext _ ?_ ?_)
  · rw [map_sub, finPart_eInf, sub_zero]
    exact hσ.fin _
  · intro τ
    rw [map_sub, map_sub, infPart_eInf, map_one]
    simp only [rs, hσ.comp]
    simp

theorem diff_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) :
    ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1).1 = eFin D • a.1.map (incA D) := by
  show GlobalTheory.MixModel.rat a.1 - rs σ 1 • a.1.map (incA D) = eFin D • a.1.map (incA D)
  rw [rs_one hσ, smul_one_smul, eFin, sub_smul, one_smul]
  rfl

def S (V : HSp D) (A : Mx D r r) (y : Mx D V.rank r) : AF D.host.F :=
  halfTr (Matrix.trace (HMul.hMul A (inner V y y) : Mx D r r))

theorem halfTr_smul (c : AF D.host.F) (x : AE D) : halfTr (c • x) = c * halfTr x := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_smul, smul_eq_mul]
  ring

theorem halfTr_nsmul (n : ℕ) (x : AE D) : halfTr (n • x) = n • halfTr x := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA]
  rw [map_nsmul]
  simp only [nsmul_eq_mul]
  ring

theorem halfTr_add (x x' : AE D) : halfTr (x + x') = halfTr x + halfTr x' := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_add]
  ring

theorem halfTr_zero : halfTr (0 : AE D) = 0 := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_zero, mul_zero]

theorem halfTr_trace_nsmul (n : ℕ) (M B : Mx D r r) :
    halfTr (Matrix.trace (HMul.hMul (n • M) B : Mx D r r)) = n • halfTr (Matrix.trace (HMul.hMul M B : Mx D r r)) := by
  rw [Matrix.smul_mul, Matrix.trace_smul, halfTr_nsmul]

theorem pow_eq_one_of_compact {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    {C : Set (Af F)} (hC : IsCompact C) : ∃ N : ℕ, 0 < N ∧ ∀ c ∈ C, ψ (pairA F 0 c) ^ N = 1 := by
  obtain ⟨N1, hN1, hK⟩ := GlobalTheory.CompanionTheory.SW.Core.AfTop.exists_mul_mem_Oh_of_isCompact F C hC
  obtain ⟨N2, hN2, hU⟩ :=
    GlobalTheory.CompanionTheory.SW.Core.AfTop.exists_mul_Oh_subset F _ (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  refine ⟨N2 * N1, Nat.mul_pos hN2 hN1, fun c hc => ?_⟩
  have h1 : ψ (pairA F 0 ((N2 : Af F) * ((N1 : Af F) * c))) = 1 := hU _ (hK c hc)
  have h2 : (N2 * N1) • pairA F 0 c = pairA F 0 ((N2 : Af F) * ((N1 : Af F) * c)) := by
    show (N2 * N1) • ((0 : Ainf F), c) = ((0 : Ainf F), (N2 : Af F) * ((N1 : Af F) * c))
    rw [Prod.smul_mk, smul_zero, ← mul_assoc, ← Nat.cast_mul, ← nsmul_eq_mul]
  rw [← AddChar.map_nsmul_eq_pow, h2, h1]

private theorem supp_lemma_5 {θ : InfFam D} {m n : ℕ} {φ : Mx D m n → ℂ} (hφ : φ ∈ schwartzA θ m n) :
    ∃ K : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsCompact K ∧
      ∀ y, φ y ≠ 0 → (fun i j => finPart D (y i j)) ∈ K := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine ⟨tsupport g, (show IsLocallyConstant g ∧ HasCompactSupport g from hg).2, fun y hy => subset_tsupport g ?_⟩
    exact right_ne_zero_of_mul hy
  | zero => exact ⟨∅, isCompact_empty, fun y hy => (hy rfl).elim⟩
  | add x y _ _ hx hy =>
    obtain ⟨K1, hK1, h1⟩ := hx
    obtain ⟨K2, hK2, h2⟩ := hy
    refine ⟨K1 ∪ K2, hK1.union hK2, fun z hz => ?_⟩
    by_cases hxz : x z = 0
    · right
      apply h2
      simpa [hxz] using hz
    · left
      exact h1 z hxz
  | smul a x _ hx =>
    obtain ⟨K, hK, h⟩ := hx
    refine ⟨K, hK, fun y hy => h y ?_⟩
    intro h0
    apply hy
    simp [h0]

private theorem continuous_sigRf_lemma_7 : Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig) := by
  let f : (Af D.host.F ⊗[D.host.F] D.host.E) →ₗ[Af D.host.F] (Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig
      map_add' := map_add _
      map_smul' := fun c z => by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul]
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
  exact IsModuleTopology.continuous_of_linearMap f

private theorem trace_bc_lemma_8 (z : AE D) :
    sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) =
      Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero] <;> rfl
  | tmul a e =>
    have h1 : (a ⊗ₜ[D.host.F] e : AE D) = a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : finPart D (a ⊗ₜ[D.host.F] e) = sndA D.host.F a • ((1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [Formalism.L2.Theta.finPart]
    rw [h2, h1]
    simp only [map_smul, GlobalTheory.CompanionTheory.HermPoisson.trace_one_tmul', smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem level_pow {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (A : Mx D r r)
    {θ : InfFam D} {φ : Mx D V.rank r → ℂ} (hφ : φ ∈ schwartzA θ V.rank r) :
    ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (eFin D * S V A y) ^ N = 1 := by
  obtain ⟨K, hK, hKy⟩ := supp_lemma_5 hφ
  let Φ : (Fin V.rank → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) → Af D.host.F := fun w =>
    algebraMap D.host.F (Af D.host.F) (1 / 2) *
      Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
        (Matrix.trace (A.map (finPart D) *
          (((Matrix.of w).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig))ᵀ *
            ((GlobalTheory.MixModel.gA V).map (finPart D) * Matrix.of w))))
  have hΦ : Continuous Φ := by
    have hσc := continuous_sigRf_lemma_7 (D := D)
    have htr : Continuous (Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)) := by fun_prop
    have hof : Continuous (fun w : Fin V.rank → Fin r → Af D.host.F ⊗[D.host.F] D.host.E => Matrix.of w) :=
      continuous_id
    exact continuous_const.mul (htr.comp (Continuous.matrix_trace (continuous_const.matrix_mul
      ((hof.matrix_map hσc).matrix_transpose.matrix_mul (continuous_const.matrix_mul hof)))))
  have hS : ∀ y : Mx D V.rank r, sndA D.host.F (S V A y) = Φ (fun i j => finPart D (y i j)) := by
    intro y
    have hM : (HMul.hMul A (inner V y y) : Mx D r r).map (finPart D) =
        A.map (finPart D) * (((Matrix.of fun i j => finPart D (y i j)).map
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig))ᵀ *
          ((GlobalTheory.MixModel.gA V).map (finPart D) * Matrix.of fun i j => finPart D (y i j))) := by
      ext i j
      simp [Matrix.mul_apply, GlobalTheory.MixModel.adj, GlobalTheory.StdUnn.inner, map_sum, GlobalTheory.CompanionTheory.WSum.finPart_cA]
    have ht : ∀ M : Mx D r r, finPart D (Matrix.trace M) = Matrix.trace (M.map (finPart D)) := by
      intro M
      simp [Matrix.trace, map_sum]
    show sndA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) *
      Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul A (inner V y y) : Mx D r r))) = _
    rw [map_mul, AlgHom.commutes, trace_bc_lemma_8, ht, hM]
  obtain ⟨N, hN, hC⟩ := pow_eq_one_of_compact hψ (hK.image hΦ)
  refine ⟨N, hN, fun y hy => ?_⟩
  rw [eFin_mul, hS y]
  exact hC _ ⟨_, hKy y hy, rfl⟩

theorem level : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) (φ : Mx D V.rank r → ℂ), φ ∈ schwartzA θ V.rank r → ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (halfTr (Matrix.trace (HMul.hMul (N • ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1)).1 (inner V y y) : Mx D r r))) = 1 := by
  intro D r V ψ hψ θ σ hσ a φ hφ
  obtain ⟨N, hN, hy⟩ := level_pow hψ V (a.1.map (incA D)) hφ
  refine ⟨N, hN, fun y hy0 => ?_⟩
  rw [AddSubgroup.coe_nsmul, diff_eq hσ a, halfTr_trace_nsmul, Matrix.smul_mul, Matrix.trace_smul, halfTr_smul,
    AddChar.map_nsmul_eq_pow]
  exact hy y hy0

end GlobalTheory.CompanionTheory.WSum.Level
