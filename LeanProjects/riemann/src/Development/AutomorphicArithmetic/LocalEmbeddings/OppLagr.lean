import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix

noncomputable section
namespace GlobalTheory.OppLagr
open scoped TensorProduct

theorem omA_invT {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (ν α : kˣ →* ℂˣ) (g : GL A k) (h : GL D k) (Ψ : Matrix A D k → ℂ) :
    GlobalTheory.SplitFlip.omA ν α⁻¹ (GlobalTheory.SplitFlip.invT g) (GlobalTheory.SplitFlip.invT h) Ψ = GlobalTheory.SplitFlip.omB ν α g h Ψ := by
  funext Y
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitFlip.omB, GlobalTheory.SplitFlip.gdet_invT, map_inv, inv_inv,
    MonoidHom.inv_apply, GlobalTheory.SplitFlip.apow_inv, neg_div, neg_neg, GlobalTheory.SplitFlip.invT_invT, GlobalTheory.SplitFlip.invT_inv_val]

theorem conj_eq_invT {k : Type} [Field k] {n : ℕ} (b P G G' : GL (Fin n) k) (J : Matrix (Fin n) (Fin n) k) (s : k)
    (hU : G.1ᵀ * J * G'.1 = J) (hP : P.1 = s • (b.1ᵀ * J)) :
    P * G' * P⁻¹ = GlobalTheory.SplitFlip.invT (b⁻¹ * G * b) := by
  symm
  apply inv_mul_eq_one.mp
  apply Units.ext
  rw [Units.val_mul, GlobalTheory.SplitFlip.invT_inv_val, Units.val_one]
  have h1 : (b⁻¹).1ᵀ * P.1 = s • J := by
    rw [hP, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  calc (b⁻¹ * G * b).1ᵀ * (P * G' * P⁻¹).1 = b.1ᵀ * (G.1ᵀ * ((b⁻¹).1ᵀ * P.1) * G'.1) * (P⁻¹).1 := by
        simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = P.1 * (P⁻¹).1 := by
        rw [h1, Matrix.mul_smul, Matrix.smul_mul, hU, Matrix.mul_smul, Matrix.smul_mul, hP, Matrix.smul_mul]
    _ = 1 := Units.mul_inv P

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  have hNN : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ) *
      Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
    rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  have hN : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) :=
    ⟨⟨_, _, hNN, hNN⟩, rfl⟩
  have h1 := Matrix.rank_of_isUnit _ hN
  have h2 : (Aᵀ * M * A.map star).rank ≤ M.rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [hA, h1] at h2
  simp only [Fintype.card_sum, Fintype.card_fin, hrs] at h2
  have h3 : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := M.rank_le_width
    simp only [Matrix.rank, Fintype.card_fin] at h2 this
    rw [Module.finrank_fin_fun]; omega
  have hu : IsUnit M := (Matrix.mulVec_surjective_iff_isUnit).mp (LinearMap.range_eq_top.mp h3)
  exact ((Matrix.isUnit_iff_isUnit_det M).mp hu).ne_zero

end GlobalTheory.OppLagr

namespace GlobalTheory.OppLagr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conj_conj (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem comp_comp (h : IsCMExt F E σ) {K : Type} [Ring K] [Algebra F K] (t : E →ₐ[F] K) : (t.comp σ).comp σ = t :=
  AlgHom.ext fun x => by simp [conj_conj h]

theorem exists_anti (h : IsCMExt F E σ) : ∃ ξ : E, ξ ≠ 0 ∧ σ ξ = -ξ := by
  by_contra hc
  push_neg at hc
  have hfix : ∀ x, σ x = x := fun x => by
    by_contra hne
    exact hc (x - σ x) (sub_ne_zero.mpr (Ne.symm hne)) (by rw [map_sub, conj_conj h]; ring)
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 τ x
    rw [hfix] at this
    exact this.symm
  have hc' := h.2.1.isComplex (InfinitePlace.mk τ)
  rw [← InfinitePlace.not_isReal_iff_isComplex] at hc'
  exact hc' (InfinitePlace.isReal_mk_iff.mpr hreal)

theorem exists_isQuad (h : IsCMExt F E σ) : ∃ ξ : AE F E, IsQuad (cA σ) ξ := by
  obtain ⟨ξ, hξ0, hξ⟩ := exists_anti h
  have hli : LinearIndependent F ![(1 : E), ξ] := by
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    simp only [Algebra.smul_def, mul_one] at hsu
    have h2 := congrArg σ hsu
    simp only [map_add, map_mul, AlgHom.commutes, hξ, map_zero] at h2
    have h3 : algebraMap F E u * ξ = 0 := by linear_combination (hsu - h2) / 2
    have hu : u = 0 := (map_eq_zero (algebraMap F E)).mp ((mul_eq_zero.mp h3).resolve_right hξ0)
    subst hu
    refine ⟨(map_eq_zero (algebraMap F E)).mp (by simpa using hsu), rfl⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ i, b i = ![(1 : E), ξ] i := fun i => by simp [b]
  refine ⟨(1 : AF F) ⊗ₜ[F] ξ, ⟨?_, ?_, ⟨Algebra.TensorProduct.basis (AF F) b, ?_, ?_⟩⟩⟩
  · refine ⟨⟨(1 : AF F) ⊗ₜ[F] ξ, (1 : AF F) ⊗ₜ[F] ξ⁻¹, ?_, ?_⟩, rfl⟩ <;>
      simp [Algebra.TensorProduct.tmul_mul_tmul, hξ0, ← Algebra.TensorProduct.one_def]
  · simp [cA, Algebra.TensorProduct.map_tmul, hξ, TensorProduct.tmul_neg]
  · rw [Algebra.TensorProduct.basis_apply, hb]; rfl
  · rw [Algebra.TensorProduct.basis_apply, hb]; rfl

end GlobalTheory.OppLagr

namespace GlobalTheory.OppLagr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem chrW_comp (h : IsCMExt F E σ) (χ : Chr F E) {m : ℕ}
    (hχ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    chrW χ (t.comp σ) = (chrW χ t)⁻¹ := by
  obtain ⟨ξ, hξ⟩ := exists_isQuad h
  ext x
  let L := GlobalTheory.SplitGLLift.liftPair (v := v) h t
  have key : ∀ p q : Fv F v × Fv F v, p + q + p * q = 0 → (1 + L p) * (1 + L q) = 1 := by
    intro p q hpq
    have := congrArg L hpq
    rw [map_add, map_add, map_mul, map_zero] at this
    linear_combination this
  have hx1 : ((x : Fv F v) - 1, (0 : Fv F v)) + (((x⁻¹ : (Fv F v)ˣ) : Fv F v) - 1, 0) +
      ((x : Fv F v) - 1, (0 : Fv F v)) * (((x⁻¹ : (Fv F v)ˣ) : Fv F v) - 1, 0) = 0 := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_mul, Prod.fst_zero]; linear_combination Units.mul_inv x
    · simp
  have hx2 : (((x⁻¹ : (Fv F v)ˣ) : Fv F v) - 1, (0 : Fv F v)) + ((x : Fv F v) - 1, (0 : Fv F v)) +
      (((x⁻¹ : (Fv F v)ˣ) : Fv F v) - 1, 0) * ((x : Fv F v) - 1, (0 : Fv F v)) = 0 := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_mul, Prod.fst_zero]; linear_combination Units.mul_inv x
    · simp
  let z : (AE F E)ˣ := ⟨1 + L ((x : Fv F v) - 1, 0), 1 + L (((x⁻¹ : (Fv F v)ˣ) : Fv F v) - 1, 0), key _ _ hx1, key _ _ hx2⟩
  have hzt : Units.map (piW t).toMonoidHom z = x := by
    ext
    simp [z, L, GlobalTheory.SplitGLLift.piW_liftPair]
  have hzc : piW (t.comp σ) (z : AE F E) = 1 := by
    simp [z, L, GlobalTheory.SplitGLLift.piW_comp_liftPair]
  have hzA : At (evFin F v) ((z : AE F E) - 1) := by
    simpa [z, L] using GlobalTheory.SplitGLLift.at_liftPair h t ((x : Fv F v) - 1, 0)
  let z' : (AE F E)ˣ := Units.map (cA σ : AE F E →* AE F E) z
  have hz'v : (z' : AE F E) = 1 + L (0, (x : Fv F v) - 1) := by
    simp [z', z, L, GlobalTheory.SplitGLLift.cA_liftPair]
  have hz't : Units.map (piW (t.comp σ)).toMonoidHom z' = x := by
    ext
    simp [hz'v, L, GlobalTheory.SplitGLLift.piW_comp_liftPair]
  have hz'c : piW ((t.comp σ).comp σ) (z' : AE F E) = 1 := by
    rw [comp_comp h, hz'v]
    simp [L, GlobalTheory.SplitGLLift.piW_liftPair]
  have hz'A : At (evFin F v) ((z' : AE F E) - 1) := by
    simpa [hz'v, L] using GlobalTheory.SplitGLLift.at_liftPair h t (0, (x : Fv F v) - 1)
  have e1 := GlobalTheory.ChrLocal.chrW_piW_eq F E σ h χ v t z hzA hzc
  have e2 := GlobalTheory.ChrLocal.chrW_piW_eq F E σ h χ v (t.comp σ) z' hz'A hz'c
  rw [hzt] at e1
  rw [hz't] at e2
  rw [MonoidHom.inv_apply, e1, e2, ResEtaPow.map_conj hξ hχ z, map_inv]

end GlobalTheory.OppLagr

namespace GlobalTheory.OppLagr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_map_ne_zero {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (hJ : J.det ≠ 0) {K : Type} [Field K] [Algebra F K]
    (t : E →ₐ[F] K) : (J.map t).det ≠ 0 := by
  have : (J.map t).det = t J.det := (AlgHom.map_det t J).symm
  rw [this]
  exact (map_ne_zero t).mpr hJ

theorem det_ne_zero_herm {B : Base F E} {m : ℕ} {X : Spc F E m} {r s : ℕ} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain w := Classical.arbitrary (InfinitePlace F)
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  rw [show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det (B.emb w).1 X.J).symm, h0, map_zero]

theorem det_ne_zero_skew {B : Base F E} {m : ℕ} {X : Spc F E m} {r s : ℕ} (hX : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain w := Classical.arbitrary (InfinitePlace F)
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  rw [Matrix.det_smul, show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det (B.emb w).1 X.J).symm, h0, map_zero, mul_zero]

end GlobalTheory.OppLagr
