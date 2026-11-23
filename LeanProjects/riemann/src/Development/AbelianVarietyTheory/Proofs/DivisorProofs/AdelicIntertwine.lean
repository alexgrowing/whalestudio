import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsJacMapZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitIdele

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

end GlobalTheory.SplitIdele

namespace GlobalTheory.SplitIdele
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
  push Not at hc
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

end GlobalTheory.SplitIdele

namespace GlobalTheory.SplitIdele
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

end GlobalTheory.SplitIdele

namespace GlobalTheory.SplitIdele
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

end GlobalTheory.SplitIdele

namespace GlobalTheory.SplitIdele

section Adelic

open Matrix GlobalTheory.SplitGLLift GlobalTheory.KSplit
open GlobalTheory.Div.CoordOpp (piW_cA incM_map_piW unit_map)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem eq_zero_of_at (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {z : AE F E} (hz : At (evFin F v) z) (h1 : piW t z = 0)
    (h2 : piW (t.comp σ) z = 0) : z = 0 := by
  obtain ⟨a1, a2⟩ := at_evFin_iff.1 hz
  refine GlobalTheory.Doubling.adele_ext (fun w => by rw [a1, map_zero]) fun w => ?_
  by_cases e : w = v
  · subst e
    exact split_ext h t (by rw [map_zero, map_zero]; exact h1) (by rw [map_zero, map_zero]; exact h2)
  · rw [a2 w e, map_zero]

theorem adelic_intertwine (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {D I : Type} [Fintype D] [DecidableEq D] [Fintype I]
    [DecidableEq I] {g : Matrix D D (AE F E)} {P : Matrix D I E} {N : Matrix I I (AE F E)} (hg : At (evFin F v) (g - 1))
    (hN : At (evFin F v) (N - 1)) (h1 : g.map (piW t) * P.map t = P.map t * N.map (piW t))
    (h2 : g.map (piW (t.comp σ)) * P.map (t.comp σ) = P.map (t.comp σ) * N.map (piW (t.comp σ))) :
    g * incM F P = incM F P * N := by
  have hz : At (evFin F v) (g * incM F P - incM F P * N) := fun u hu => by
    rw [show g * incM F P - incM F P * N = (g - 1) * incM F P - incM F P * (N - 1) by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel,
      smul_sub, ← Matrix.smul_mul, ← Matrix.mul_smul, hg u hu, hN u hu, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  have k : ∀ τ : E →ₐ[F] Fv F v, g.map (piW τ) * P.map τ = P.map τ * N.map (piW τ) → ∀ i j,
      piW τ ((g * incM F P - incM F P * N) i j) = 0 := fun τ e i j => by
    rw [← incM_map_piW, ← Matrix.map_mul, ← Matrix.map_mul] at e
    rw [Matrix.sub_apply, map_sub, sub_eq_zero]
    exact congrFun (congrFun e i) j
  rw [← sub_eq_zero]
  ext i j
  exact eq_zero_of_at h t (fun u hu => congrFun (congrFun (hz u hu) i) j) (k _ h1 i j) (k _ h2 i j)

def idl (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) : (Fv F v)ˣ × (Fv F v)ˣ →* (AE F E)ˣ :=
  (Units.map (oneAdd (liftPair h t))).comp MulEquiv.prodUnits.symm.toMonoidHom

theorem idl_val (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) :
    (idl h t (x, y) : AE F E) = 1 + liftPair h t ((x : Fv F v) - 1, (y : Fv F v) - 1) := rfl

theorem piW_idl (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) : piW t (idl h t (x, y) : AE F E) = x := by
  rw [idl_val, map_add, map_one, piW_liftPair, add_sub_cancel]

theorem piW_comp_idl (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) :
    piW (t.comp σ) (idl h t (x, y) : AE F E) = y := by
  rw [idl_val, map_add, map_one, piW_comp_liftPair, add_sub_cancel]

theorem at_idl (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) :
    At (evFin F v) ((idl h t (x, y) : AE F E) - 1) := by
  rw [idl_val, add_sub_cancel_left]; exact at_liftPair h t _

theorem chr_idl (h : IsCMExt F E σ) (χ : Chr F E) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) :
    (χ (idl h t (x, y)) : ℂ) = (chrW χ t x : ℂ) * (chrW χ (t.comp σ) y : ℂ) := by
  have e1 := GlobalTheory.ChrLocal.chrW_piW_eq F E σ h χ v t (idl h t (x, 1)) (at_idl h t _ _) (piW_comp_idl h t _ _)
  have e2 := GlobalTheory.ChrLocal.chrW_piW_eq F E σ h χ v (t.comp σ) (idl h t (1, y)) (at_idl h t _ _)
    (by rw [GlobalTheory.SplitIdele.comp_comp h]; exact piW_idl h t _ _)
  rw [show Units.map (piW t).toMonoidHom (idl h t (x, 1)) = x from Units.ext (piW_idl h t _ _)] at e1
  rw [show Units.map (piW (t.comp σ)).toMonoidHom (idl h t (1, y)) = y from Units.ext (piW_comp_idl h t _ _)] at e2
  rw [e1, e2, show (x, y) = (x, 1) * (1, y) by simp, map_mul, map_mul, Circle.coe_mul]
  rfl

theorem absE_idl (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) :
    (absE F E (idl h t (x, y)) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) x * GlobalTheory.SplitWeil.nabs (Fv F v) y := by
  have hN : ∀ z : Fv F v ⊗[F] E, Algebra.norm (Fv F v) z = splitProj t z * splitProj (t.comp σ) z := fun z => by
    have := congrArg (splitProj t) (GlobalTheory.Doubling.algebraMap_norm_eq h z)
    rw [AlgHom.commutes, map_mul, ← splitProj_comp] at this
    exact this
  rw [absE_of_mem (v := v) (mem_idelesAt.2 (at_idl h t x y)), GlobalTheory.Doubling.absEv_apply, coe_nnnorm, hN, norm_mul,
    ← ((GlobalTheory.CompletionNorm.norm_nabs_valuation F v).1 x).1, ← ((GlobalTheory.CompletionNorm.norm_nabs_valuation F v).1 y).1]
  exact congrArg₂ (fun p q : Fv F v => ‖p‖ * ‖q‖) (piW_idl h t x y) (piW_comp_idl h t x y)

theorem char_idl (h : IsCMExt F E σ) (χ : Chr F E) {m : ℕ}
    (hχ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) (a : ℕ) :
    (χ (idl h t (x, y⁻¹)) : ℂ) * (((absE F E (idl h t (x, y⁻¹)) : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) =
      (chrW χ t x : ℂ) * GlobalTheory.SplitFlip.apow x ((a : ℂ) / 2) * ((chrW χ t y : ℂ) * GlobalTheory.SplitFlip.apow y (-(a : ℂ) / 2)) := by
  rw [chr_idl, absE_idl, GlobalTheory.SplitIdele.chrW_comp h χ hχ, MonoidHom.inv_apply, map_inv, inv_inv, ← GlobalTheory.SplitWeil.nabs_mul,
    Complex.ofReal_cpow (GlobalTheory.SplitWeil.nabs_pos _ _).le, neg_div, ← GlobalTheory.SplitFlip.apow_inv]
  have := GlobalTheory.SplitFlip.apow_mul x y⁻¹ ((a : ℂ) / 2)
  rw [GlobalTheory.SplitFlip.apow] at this
  push_cast
  rw [this]
  ring

end Adelic

end GlobalTheory.SplitIdele

end
