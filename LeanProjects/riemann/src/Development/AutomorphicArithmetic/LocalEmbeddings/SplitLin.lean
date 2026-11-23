import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsJacMapZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentMapsForThetaTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSplittingPairIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelDoubleSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingIwasawaDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactConjugateExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryIntertwinesStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix

noncomputable section Helpers
namespace GlobalTheory.SplitLin.OppLagr
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

end GlobalTheory.SplitLin.OppLagr

namespace GlobalTheory.SplitLin.OppLagr
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

end GlobalTheory.SplitLin.OppLagr

namespace GlobalTheory.SplitLin.OppLagr
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

end GlobalTheory.SplitLin.OppLagr

namespace GlobalTheory.SplitLin.OppLagr
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

end GlobalTheory.SplitLin.OppLagr

end Helpers

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitLin.JacGeom

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
    (by rw [GlobalTheory.SplitLin.OppLagr.comp_comp h]; exact piW_idl h t _ _)
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
  rw [chr_idl, absE_idl, GlobalTheory.SplitLin.OppLagr.chrW_comp h χ hχ, MonoidHom.inv_apply, map_inv, inv_inv, ← GlobalTheory.SplitWeil.nabs_mul,
    Complex.ofReal_cpow (GlobalTheory.SplitWeil.nabs_pos _ _).le, neg_div, ← GlobalTheory.SplitFlip.apow_inv]
  have := GlobalTheory.SplitFlip.apow_mul x y⁻¹ ((a : ℂ) / 2)
  rw [GlobalTheory.SplitFlip.apow] at this
  push_cast
  rw [this]
  ring

end Adelic

end GlobalTheory.SplitLin.JacGeom
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Matrix Kronecker

noncomputable section

namespace GlobalTheory.SplitLin.DblSiegelScal

open Matrix MeasureTheory

section Algebra

variable {K : Type} [CommRing K] {β : Type} [Fintype β] [DecidableEq β]

theorem det_of_diag {a b c d T : Matrix β β K}
    (h : fromBlocks a b c d * (diagCols β : Matrix (β ⊕ β) β K) = (diagCols β : Matrix (β ⊕ β) β K) * T) :
    (fromBlocks a b c d).det = T.det * (d - b).det := by
  simp only [diagCols, fromRows_mul, fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.one_mul, fromRows_ext_iff] at h
  have h6 : fromBlocks a b c d * fromBlocks 1 0 1 1 =
      fromBlocks 1 0 1 1 * (fromBlocks T b 0 (d - b) : Matrix (β ⊕ β) (β ⊕ β) K) := by
    simp [fromBlocks_multiply, h.1, h.2]
  simpa [det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁] using congrArg det h6

theorem adj_diag {P P' : Matrix (β ⊕ β) (β ⊕ β) K} {J T : Matrix β β K} (hJ : IsUnit J.det) (hP : IsUnit P.det)
    (hU : Pᵀ * fromBlocks J 0 0 (-J) * P' = fromBlocks J 0 0 (-J))
    (h : P * (diagCols β : Matrix (β ⊕ β) β K) = (diagCols β : Matrix (β ⊕ β) β K) * T) :
    ∃ T' : Matrix β β K, P' * (diagCols β : Matrix (β ⊕ β) β K) = (diagCols β : Matrix (β ⊕ β) β K) * T' ∧
      P.det * T'.det = T.det := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, P = fromBlocks a b c d := ⟨_, _, _, _, (fromBlocks_toBlocks P).symm⟩
  have hd := det_of_diag h
  have hT : IsUnit T.det := isUnit_of_mul_isUnit_left (hd ▸ hP)
  have h3 := congrArg (· * (diagCols β : Matrix (β ⊕ β) β K)) hU
  simp only [Matrix.mul_assoc] at h3
  obtain ⟨u, w, huw⟩ : ∃ u w, P' * (diagCols β : Matrix (β ⊕ β) β K) = fromRows u w := ⟨_, _, (fromRows_toRows _).symm⟩
  rw [huw] at h3 ⊢
  simp only [diagCols, fromBlocks_transpose, fromRows_mul, fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.one_mul,
    Matrix.zero_mul, add_zero, zero_add, fromRows_ext_iff, Matrix.neg_mul, Matrix.mul_neg] at h h3 ⊢
  have e : Tᵀ * J * (u - w) = 0 := by
    have e1 : Tᵀ * (J * u) = aᵀ * (J * u) + bᵀ * (J * u) := by rw [← h.1, transpose_add, Matrix.add_mul]
    have e2 : Tᵀ * (J * w) = cᵀ * (J * w) + dᵀ * (J * w) := by rw [← h.2, transpose_add, Matrix.add_mul]
    rw [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_sub, e1, e2]
    refine Eq.trans ?_ ((congrArg₂ (· + ·) h3.1 h3.2).trans (add_neg_cancel J))
    abel
  have hu : IsUnit (Tᵀ * J) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_mul, det_transpose]; exact hT.mul hJ)
  obtain rfl : u = w := sub_eq_zero.1 (hu.mul_right_eq_zero.1 e)
  refine ⟨u, ⟨rfl, rfl⟩, ?_⟩
  have h4 : (d - b)ᵀ * J * u = J := by
    rw [transpose_sub, Matrix.mul_assoc, Matrix.sub_mul]
    refine Eq.trans ?_ ((congrArg Neg.neg h3.2).trans (neg_neg J))
    abel
  have h5 : (d - b).det * u.det = 1 := by
    have := congrArg det h4
    rw [det_mul, det_mul, det_transpose] at this
    exact hJ.mul_left_cancel (by linear_combination this)
  rw [hd, mul_assoc, h5, mul_one]

theorem mul_diagCols {α : Type} (z : Matrix α β K) : z * (diagCols β : Matrix (β ⊕ β) β K)ᵀ = fromCols z z := by
  rw [diagCols, transpose_fromRows, mul_fromCols, transpose_one, Matrix.mul_one]

theorem diagCols_map {L : Type} [CommRing L] (f : K →+* L) :
    (diagCols β : Matrix (β ⊕ β) β K).map f = diagCols β := by
  ext (i | i) j <;> by_cases hij : i = j <;> simp [diagCols, hij]

theorem symp_dbl_diag {R : Type} [CommRing R] [Algebra R K] (c : K →ₐ[R] K) {α : Type} [Fintype α] [DecidableEq α] (ξ : K)
    (JA : Matrix α α K) (JB : Matrix β β K) (x₁ x₂ z : Matrix α β K) :
    symp (R := R) c ξ JA (dbl JB) (fromCols x₁ x₂) (fromCols z z) = symp (R := R) c ξ JA JB (x₁ - x₂) z := by
  unfold symp
  congr 2
  unfold hTens
  simp only [dbl, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, Matrix.sub_apply, sub_mul,
    Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem pairing_mul {α : Type} [Fintype α] (A : Matrix α α K) (Y : Matrix α β K) (B : Matrix β β K) (P : Matrix α β K) :
    ∑ k, ∑ l, (A * Y * B) k l * P k l = ∑ k, ∑ l, Y k l * (Aᵀ * P * Bᵀ) k l := by
  have e : ∀ M Q : Matrix α β K, ∑ k, ∑ l, M k l * Q k l = Matrix.trace (M * Qᵀ) := by
    intro M Q
    simp [Matrix.trace, Matrix.mul_apply]
  rw [e, e, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    show A * Y * B * Pᵀ = A * (Y * B * Pᵀ) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, Matrix.transpose_transpose]

theorem exists_factor {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ι : V →ₗ[ℂ] V')
    (S : Submodule ℂ V) (h : Set.InjOn ι S) (l : V →ₗ[ℂ] ℂ) : ∃ m : V' →ₗ[ℂ] ℂ, ∀ φ ∈ S, m (ι φ) = l φ := by
  obtain ⟨g, hg⟩ := (ι.domRestrict S).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 fun x y e => Subtype.ext (h x.2 y.2 e))
  exact ⟨l ∘ₗ S.subtype ∘ₗ g, fun φ hφ => congrArg (fun x : S => l x) (LinearMap.congr_fun hg ⟨φ, hφ⟩)⟩

end Algebra

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem form_comp_invT [Invertible (2 : k)] (ψ : AddChar k ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (m : (Matrix α (β ⊕ β) k → ℂ) →ₗ[ℂ] ℂ)
    (htr : ∀ C : Matrix α β k, ∀ f ∈ SB (Matrix α (β ⊕ β) k), m (fun Y => f (Y + fromCols C C)) = m f)
    (hmu : ∀ D : Matrix α β k, ∀ f ∈ SB (Matrix α (β ⊕ β) k),
      m (fun Y => ψ (∑ i, ∑ j, (Y.toCols₁ - Y.toCols₂) i j * D i j) * f Y) = m f)
    (g : GL (β ⊕ β) k) (T : GL β k)
    (h : g.val * (diagCols β : Matrix (β ⊕ β) β k) = (diagCols β : Matrix (β ⊕ β) β k) * T.val)
    {f : Matrix α (β ⊕ β) k → ℂ} (hf : f ∈ SB (Matrix α (β ⊕ β) k)) :
    m (fun Y => f (Y * (GlobalTheory.SplitFlip.invT g).val)) =
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet T) (Fintype.card α : ℂ) * m f := by
  let σ : α × β ≃ α × β := Equiv.refl _
  let e : Matrix α (β ⊕ β) k ≃ₜ (α × β ⊕ α × β → k) :=
    { toEquiv := (flat (dblNum σ)).toEquiv
      continuous_toFun := continuous_pi fun q => (continuous_id (X := Matrix α (β ⊕ β) k)).matrix_elem _ _
      continuous_invFun := continuous_matrix fun i j => continuous_apply ((dblNum σ).symm (i, j)) }
  have he : ∀ X Y : Matrix α β k, e (fromCols X Y) = Sum.elim (flat σ X) (flat σ Y) := flat_fromCols σ
  have s1 : ∀ φ ∈ SB (α × β ⊕ α × β → k), (fun Y => φ (e Y)) ∈ SB (Matrix α (β ⊕ β) k) := fun φ hφ =>
    ⟨hφ.1.comp_continuous e.continuous, hφ.2.comp_homeomorph e⟩
  have s2 : ∀ f ∈ SB (Matrix α (β ⊕ β) k), (fun x => f (e.symm x)) ∈ SB (α × β ⊕ α × β → k) := fun f hf =>
    ⟨hf.1.comp_continuous e.symm.continuous, hf.2.comp_homeomorph e.symm⟩
  let l := m ∘ₗ LinearMap.funLeft ℂ ℂ e
  have hl0 : ∀ f, l (fun x => f (e.symm x)) = m f := fun f =>
    congrArg m (funext fun Y => congrArg f (e.symm_apply_apply Y))
  have hl : ∀ x y : α × β → k, ∀ φ ∈ SB (α × β ⊕ α × β → k),
      l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ := by
    intro x y φ hφ
    obtain ⟨C, rfl⟩ := (flat σ).surjective x
    obtain ⟨D, rfl⟩ := (flat σ).surjective y
    have s3 : (fun Y => φ (e (Y + fromCols C C))) ∈ SB (Matrix α (β ⊕ β) k) :=
      ⟨(s1 φ hφ).1.comp_continuous (continuous_add_const _), (s1 φ hφ).2.comp_homeomorph (Homeomorph.addRight _)⟩
    refine Eq.trans ?_ ((hmu D _ s3).trans (htr C _ (s1 φ hφ)))
    refine congrArg m (funext fun Y => ?_)
    obtain ⟨Y₁, Y₂, rfl⟩ : ∃ Y₁ Y₂, Y = fromCols Y₁ Y₂ := ⟨_, _, (fromCols_toCols Y).symm⟩
    have ea : e (fromCols Y₁ Y₂ + fromCols C C) = e (fromCols Y₁ Y₂) + e (fromCols C C) := rfl
    show schr ψ _ φ (e _) = _
    rw [ea, he, he, schr]
    congr 2
    simp only [toCols₁_fromCols, toCols₂_fromCols, sumElim_dotProduct_sumElim, dotProduct_neg, add_neg_cancel, mul_zero,
      add_zero, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, ← sub_eq_add_neg]
    simp only [dotProduct, Fintype.sum_prod_type]
    rfl
  let G : Matrix (α × β) (α × β) k := (1 : Matrix α α k) ⊗ₖ (T⁻¹).val
  have hG : G.det = ((GeneralLinearGroup.det T)⁻¹ ^ Fintype.card α : kˣ) := by
    rw [det_kronecker, det_one, one_pow, one_mul, ← map_inv, Units.val_pow_eq_pow_val]
    rfl
  let g₀ : GL (α × β) k := GeneralLinearGroup.mkOfDetNeZero G (hG ▸ Units.ne_zero _)
  have hg : GeneralLinearGroup.det g₀ = (GeneralLinearGroup.det T)⁻¹ ^ Fintype.card α := Units.ext hG
  have hgx : ∀ X : Matrix α β k, g₀.val.mulVec (flat σ X) = flat σ (X * (T⁻¹).valᵀ) := by
    intro X
    funext q
    show ∑ q', G q q' * X q'.1 q'.2 = (X * (T⁻¹).valᵀ) q.1 q.2
    rw [Fintype.sum_prod_type, mul_apply]
    simp [G, kroneckerMap_apply, one_apply, mul_comm]
  have h1 : (g⁻¹).val * (diagCols β : Matrix (β ⊕ β) β k) = (diagCols β : Matrix (β ⊕ β) β k) * (T⁻¹).val := by
    have := congrArg (fun N => (g⁻¹).val * N * (T⁻¹).val) h
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
    rw [this, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  let R : Matrix α (β ⊕ β) k ≃ₜ Matrix α (β ⊕ β) k :=
    { toFun := fun Y => Y * (GlobalTheory.SplitFlip.invT g).val
      invFun := fun Y => Y * ((GlobalTheory.SplitFlip.invT g)⁻¹).val
      left_inv := fun Y => by simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun Y => by simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  have hf' : (fun Y => f (Y * (GlobalTheory.SplitFlip.invT g).val)) ∈ SB (Matrix α (β ⊕ β) k) :=
    ⟨hf.1.comp_continuous R.continuous, hf.2.comp_homeomorph R⟩
  have key := diag_invariant_comp ψ hψ hψ1 l hl g₀ (s2 _ hf) (s2 _ hf') (fun x => by
    obtain ⟨X, rfl⟩ := (flat σ).surjective x
    rw [hgx, ← he, ← he, e.symm_apply_apply, e.symm_apply_apply, ← mul_diagCols, ← mul_diagCols,
      GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, Matrix.mul_assoc, ← transpose_mul, ← transpose_mul, h1])
  rw [hl0 f, hl0 (fun Y => f (Y * (GlobalTheory.SplitFlip.invT g).val)), hg] at key
  rw [← key, ← mul_assoc, GlobalTheory.SplitFlip.apow, Complex.cpow_natCast, GlobalTheory.SplitWeil.nabs]
  have hpos : (0 : ℝ) < distribHaarChar k (GeneralLinearGroup.det T) := distribHaarChar_pos (A := k)
  have hne : ((distribHaarChar k (GeneralLinearGroup.det T) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  simp only [map_pow, map_inv, NNReal.coe_pow, NNReal.coe_inv, Complex.ofReal_pow, Complex.ofReal_inv]
  rw [← mul_pow, mul_inv_cancel₀ hne, one_pow, one_mul]

end Local

section Adelic

open GlobalTheory.SplitGLLift GlobalTheory.SplitLin.JacGeom GlobalTheory.DblScal
open GlobalTheory.Div.CoordOpp (piW_cA incM_map_piW)
open scoped GlobalTheory.VacAny

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem exists_rest_ne (κ : Type) [Fintype κ] (v : Pl F) :
    ∃ R : (κ ⊕ κ → AF F) → ℂ, (∀ φ ∈ SB (κ ⊕ κ → Fv F v), Rest (evFin F v) φ R) ∧
      ∃ φ ∈ SB (κ ⊕ κ → Fv F v), GlobalTheory.DiagForm.lDiag F κ (tens (evFin F v) φ R) ≠ 0 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.DiagForm.exists_lDiag_ne (F := F) (κ := κ)
  rw [GlobalTheory.WeylSpan.schA_eq_span_pure] at hΦ
  refine h0 ((Submodule.span_le (p := LinearMap.ker (GlobalTheory.DiagForm.lDiag F κ))).2 ?_ hΦ)
  rintro _ ⟨f, φs, h1, h2, rfl⟩
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs h2
  have := hne r (fun φ hφ => ⟨hr, ?_⟩) (φs v) (h1 v)
  · rwa [hrt, Function.update_eq_self] at this
  · rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ h2)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact h1 w

theorem exists_lift (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {α β : Type} (P₀ P₁ : Matrix α β (Fv F v)) :
    ∃ u : Matrix α β (AE F E), At (evFin F v) u ∧ u.map (piW t) = P₀ ∧ u.map (piW (t.comp σ)) = P₁ :=
  ⟨of fun i j => liftPair h t (P₀ i j, P₁ i j), fun a ha => Matrix.ext fun _ _ => at_liftPair h t _ a ha,
    Matrix.ext fun _ _ => piW_liftPair h t _, Matrix.ext fun _ _ => piW_comp_liftPair h t _⟩

omit [NumberField E] in

theorem at_det {β : Type} [Fintype β] [DecidableEq β] {N : Matrix β β (AE F E)} (h : At (evFin F v) (N - 1)) :
    At (evFin F v) (N.det - 1) := by
  intro a ha
  let I : Ideal (AE F E) := LinearMap.ker (LinearMap.lsmul (AE F E) (AE F E) (algebraMap (AF F) (AE F E) a))
  have hI : ∀ z, z ∈ I ↔ a • z = 0 := fun z => by
    rw [Algebra.smul_def]; rfl
  have e : (Ideal.Quotient.mk I).mapMatrix N = (Ideal.Quotient.mk I).mapMatrix 1 :=
    Matrix.ext fun i j => Ideal.Quotient.eq.2 ((hI _).2 (congrFun (congrFun (h a ha) i) j))
  rw [← hI, ← Ideal.Quotient.eq, RingHom.map_det, e, map_one, det_one, map_one]

theorem exists_siegel (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hJ : IsUnit (J.map t).det) (c : GL (Fin d) (Fv F v)) {p : UD σ J} (hp : p ∈ UDAt σ J (evFin F v))
    {T : Matrix (Fin d) (Fin d) (Fv F v)}
    (hT : (locMatD t c p).val * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * T) :
    ∃ (T₀ : GL (Fin d) (Fv F v)) (y : (Fv F v)ˣ) (N : GL (Fin d) (AE F E)), T₀.val = T ∧
      (p : GL (Fin d ⊕ Fin d) (AE F E)).val * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * N.val ∧
      GeneralLinearGroup.det N = idl h t (GlobalTheory.SplitFlip.gdet T₀, y⁻¹) ∧
      GlobalTheory.SplitFlip.gdet (locMatD t c p) = GlobalTheory.SplitFlip.gdet T₀ * y := by
  set P := (p : GL (Fin d ⊕ Fin d) (AE F E)).val with hP
  have hPu : IsUnit P.det := Matrix.isUnits_det_units _
  have hc : (dsum c).val * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * c.val := by
    simp [dsum, diagCols, fromBlocks_mul_fromRows, fromRows_mul]
  have hl : (locMatD t c p).val = ((dsum c)⁻¹).val * P.map (piW t) * (dsum c).val := rfl
  have h1 : P.map (piW t) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * (c.val * T * (c⁻¹).val) := by
    have := congrArg (fun Z => (dsum c).val * Z * (c⁻¹).val) hT
    simp only [hl, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, hc] at this
    rw [Matrix.mul_assoc (P.map _), hc, Matrix.mul_assoc, Matrix.mul_assoc _ c.val, Units.mul_inv, Matrix.mul_one] at this
    simpa only [Matrix.mul_assoc] using this
  have hU : (P.map (piW t))ᵀ * fromBlocks (J.map t) 0 0 (-J.map t) * P.map (piW (t.comp σ)) =
      fromBlocks (J.map t) 0 0 (-J.map t) := by
    have := congrArg (fun M => M.map (piW t)) (show Pᵀ * dbl (incM F J) * P.map (cA σ) = dbl (incM F J) from p.2)
    have e1 : (dbl (incM F J)).map (piW t) = fromBlocks (J.map t) 0 0 (-J.map t) := by
      rw [← incM_map_piW]
      ext (i | i) (j | j) <;> simp [dbl]
    have e2 : (P.map (cA σ)).map (piW t) = P.map (piW (t.comp σ)) := Matrix.ext fun i j => piW_cA σ t _
    simpa only [Matrix.map_mul, Matrix.transpose_map, e1, e2] using this
  have hd : ∀ τ : E →ₐ[F] Fv F v, ∀ {β : Type} [Fintype β] [DecidableEq β] (Z : Matrix β β (AE F E)),
      (Z.map (piW τ)).det = piW τ Z.det := fun τ _ _ _ Z => (RingHom.map_det _ _).symm
  obtain ⟨T', h2, h3⟩ := adj_diag hJ (hd t P ▸ hPu.map _) hU h1
  obtain ⟨u, hu, hu1, hu2⟩ := exists_lift h t (c.val * T * (c⁻¹).val - 1) (T' - 1)
  have m1 : (1 + u).map (piW t) = c.val * T * (c⁻¹).val := by
    rw [Matrix.map_add _ (map_add _), hu1, Matrix.map_one _ (map_zero _) (map_one _), add_sub_cancel]
  have m2 : (1 + u).map (piW (t.comp σ)) = T' := by
    rw [Matrix.map_add _ (map_add _), hu2, Matrix.map_one _ (map_zero _) (map_one _), add_sub_cancel]
  have hu' : At (evFin F v) (1 + u - 1) := by rwa [add_sub_cancel_left]
  have hΔ : ∀ τ : E →ₐ[F] Fv F v, (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E).map τ = diagCols (Fin d) :=
    fun τ => diagCols_map (τ : E →+* Fv F v)
  have hN := adelic_intertwine h t (g := P) (P := (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E)) hp hu'
    (by rw [m1, hΔ]; exact h1) (by rw [m2, hΔ]; exact h2)
  rw [show incM F (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) = diagCols (Fin d) from
    diagCols_map (inclR (F := F) (E := E) (AF F) : E →+* AE F E)] at hN
  have hNu : IsUnit (1 + u).det := by
    have := hN
    rw [← fromBlocks_toBlocks P] at this
    have e := det_of_diag this
    rw [fromBlocks_toBlocks] at e
    exact isUnit_of_mul_isUnit_left (e ▸ hPu)
  have dT : (c.val * T * (c⁻¹).val).det = T.det := det_units_conj c T
  have hTu : IsUnit T.det := by rw [← dT, ← m1, hd]; exact hNu.map _
  have hT'u : IsUnit T'.det := by rw [← m2, hd]; exact hNu.map _
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hTu).unit, hT'u.unit⁻¹, ((Matrix.isUnit_iff_isUnit_det _).2 hNu).unit, rfl, hN,
    Units.ext ?_, ?_⟩
  · rw [inv_inv, ← sub_eq_zero]
    refine eq_zero_of_at h t (fun a ha => ?_) ?_ ?_
    · rw [← sub_sub_sub_cancel_right _ _ 1, smul_sub, at_idl h t _ _ a ha, sub_zero]
      exact at_det hu' a ha
    · rw [map_sub, piW_idl, sub_eq_zero]
      exact (hd t (1 + u)).symm.trans (by rw [m1, dT]; rfl)
    · rw [map_sub, piW_comp_idl, sub_eq_zero]
      exact (hd (t.comp σ) (1 + u)).symm.trans (by rw [m2]; rfl)
  · refine eq_mul_inv_of_mul_eq (Units.ext ?_)
    show (locMatD t c p).val.det * T'.det = T.det
    rw [hl, det_units_conj', h3, dT]

theorem psi_symp (h : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (t : E →ₐ[F] Fv F v) {n d : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {K : Matrix (Fin d) (Fin d) E} (hJ : ∀ i j, σ (J j i) = J i j) (hK : ∀ i j, σ (K j i) = -K i j)
    {x z : Matrix (Fin n) (Fin d) (AE F E)} (hx : At (evFin F v) x) (hz : z.map (piW t) = 0) :
    ψ (symp (cA σ) (-1) (incM F J) (incM F K) x z) = GlobalTheory.LatVac.psiAt ψ v
      (∑ i, ∑ j, (x.map (piW t)) i j * (-(J.map t * z.map (piW (t.comp σ)) * (K.map t)ᵀ)) i j) := by
  have hA : At (evFin F v) (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F K) x z) := by
    intro a ha
    have h0 : ∀ i j, a • x i j = 0 := fun i j => congrFun (congrFun (hx a ha) i) j
    rw [symp, ← map_smul, ← mul_smul_comm, hTens]
    simp only [Finset.smul_sum, ← smul_mul_assoc, h0, zero_mul, Finset.sum_const_zero, mul_zero, map_zero]
  rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ hA]
  show GlobalTheory.LatVac.psiAt ψ v (evFin F v _) = _
  rw [GlobalTheory.LinCoords.splitTrace' h v t J K hJ hK x z hx, hz]
  simp

end Adelic

open GlobalTheory.DblScal GlobalTheory.SplitLin.JacGeom
open scoped GlobalTheory.VacAny

theorem scalar_siegel : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        (∃ T : Matrix (Fin d) (Fin d) (Fv F v),
          ((GlobalTheory.DblScal.locMatD t c p).val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) *
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * T) →
        cd p = (chrW χX t (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) : ℂ) *
          GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) (-(n : ℂ) / 2) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hdd hW hloc ιd hι cd hcd p hp ⟨T, hT⟩
  have hcm : IsCMExt F E σ := hP.base.cm
  have hstd := hP.base.std
  have hX : IsUnit (X.J.map t).det :=
    isUnit_iff_ne_zero.2 (GlobalTheory.SplitLin.OppLagr.det_map_ne_zero (GlobalTheory.SplitLin.OppLagr.det_ne_zero_herm hP.herm) t)
  have hK : IsUnit (W.J.map t).det :=
    isUnit_iff_ne_zero.2 (GlobalTheory.SplitLin.OppLagr.det_map_ne_zero (GlobalTheory.SplitLin.OppLagr.det_ne_zero_skew hP.skew) t)
  obtain ⟨R, hR, φ₀, hφ₀, h0⟩ := exists_rest_ne (Fin n × Fin d) v
  let lam : ((Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ := GlobalTheory.DiagForm.lDiag F (Fin n × Fin d) ∘ₗ
    { toFun := fun φ => tens (evFin F v) φ R
      map_add' := fun _ _ => funext fun _ => add_mul _ _ _
      map_smul' := fun _ _ => funext fun _ => mul_assoc _ _ _ }
  have hlam : ∀ φ, lam φ = GlobalTheory.DiagForm.lDiag F (Fin n × Fin d) (tens (evFin F v) φ R) := fun _ => rfl
  obtain ⟨m, hm⟩ := exists_factor ιd _ hι.bij.injOn lam
  have hinv : ∀ z : Matrix (Fin n) (Fin d) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
      GlobalTheory.DiagForm.lDiag F _ (dd.rho B.ψ (fromCols z z) Φ) = GlobalTheory.DiagForm.lDiag F _ Φ := fun z Φ hΦ => by
    rw [Darboux.rho, hdd z z, GlobalTheory.DiagForm.lDiag_schr B.ψ _ _ hΦ]
  have hat : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → At (evFin F v) (fromCols z z) := fun z hz a ha => by
    ext i (j | j) <;> exact congrFun (congrFun (hz a ha) i) j
  have hrho : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      ∃ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (dd.rho B.ψ (fromCols z z)) φ φ₁ ∧
        m (ιd φ₁) = m (ιd φ) := fun z hz φ hφ => by
    have h1 := GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo dd v (fromCols z z)) φ hφ
    have h2 := GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ (hat z hz) φ
    refine ⟨_, h1, h2, ?_⟩
    rw [hm _ h1, hm _ hφ, hlam, hlam, ← h2 R (hR φ hφ), hinv z _ (hR φ hφ).2]
  have hco : ∀ Y₁ Y₂ : Matrix (Fin n) (Fin d) (Fv F v),
      (b⁻¹).val * fromCols (b.val * Y₁ * c.valᵀ) (b.val * Y₂ * c.valᵀ) * ((dsum c)⁻¹).valᵀ = fromCols Y₁ Y₂ := by
    intro Y₁ Y₂
    have e : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), (b⁻¹).val * (b.val * Y * c.valᵀ) * (c⁻¹).valᵀ = Y := fun Y => by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul,
        Units.inv_mul, transpose_one, Matrix.mul_one]
    rw [show ((dsum c)⁻¹).val = fromBlocks (c⁻¹).val 0 0 (c⁻¹).val from rfl, mul_fromCols, fromBlocks_transpose, fromCols_mul_fromBlocks, transpose_zero, Matrix.mul_zero, Matrix.mul_zero,
      add_zero, zero_add, e, e]
  have htr : ∀ C : Matrix (Fin n) (Fin d) (Fv F v), ∀ f ∈ SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)),
      m (fun Y => f (Y + fromCols C C)) = m f := by
    intro C f hf
    obtain ⟨φ, hφ, rfl⟩ := hι.bij.surjOn hf
    obtain ⟨z, hz, z1, z2⟩ := exists_lift hcm t (b.val * C * c.valᵀ) 0
    obtain ⟨φ₁, hφ₁, ha, e⟩ := hrho z hz φ hφ
    rw [← e]
    refine congrArg m (funext fun Y => ?_)
    rw [hι.trans _ (hat z hz) (by rw [fromCols_map, z2, fromCols_zero]) φ hφ φ₁ hφ₁ ha Y, fromCols_map, z1, hco]
  have hmu : ∀ D : Matrix (Fin n) (Fin d) (Fv F v), ∀ f ∈ SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)),
      m (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, (Y.toCols₁ - Y.toCols₂) i j * D i j) * f Y) = m f := by
    intro D f hf
    obtain ⟨φ, hφ, rfl⟩ := hι.bij.surjOn hf
    obtain ⟨z, hz, z1, z2⟩ := exists_lift hcm t 0
      (-((X.J.map t)⁻¹ * ((b⁻¹).valᵀ * D * (c⁻¹).val) * ((W.J.map t)⁻¹)ᵀ))
    obtain ⟨φ₁, hφ₁, ha, e⟩ := hrho z hz φ hφ
    rw [← e]
    refine congrArg m (funext fun Y => ?_)
    obtain ⟨Y₁, Y₂, rfl⟩ : ∃ Y₁ Y₂, Y = fromCols Y₁ Y₂ := ⟨_, _, (fromCols_toCols Y).symm⟩
    obtain ⟨x₁, hx₁, a1, a2⟩ := exists_lift hcm t (b.val * Y₁ * c.valᵀ) 0
    obtain ⟨x₂, hx₂, b1, b2⟩ := exists_lift hcm t (b.val * Y₂ * c.valᵀ) 0
    have hx : At (evFin F v) (fromCols x₁ x₂) := fun a ha => by
      ext i (j | j)
      exacts [congrFun (congrFun (hx₁ a ha) i) j, congrFun (congrFun (hx₂ a ha) i) j]
    have key := hι.mult _ (hat z hz) (by rw [fromCols_map, z1, fromCols_zero]) φ hφ φ₁ hφ₁ ha _ hx
      (by rw [fromCols_map, a2, b2, fromCols_zero])
    rw [fromCols_map, a1, b1, hco, symp_dbl_diag, psi_symp hcm B.ψ t hP.herm.herm hP.skew.skew
      (fun a ha => by rw [smul_sub, hx₁ a ha, hx₂ a ha, sub_zero]) z1, Matrix.map_sub _ (map_sub _), a1, b1, z2,
      ← Matrix.sub_mul, ← Matrix.mul_sub, pairing_mul] at key
    rw [key, toCols₁_fromCols, toCols₂_fromCols]
    have e2 : b.valᵀ * -(X.J.map t * -((X.J.map t)⁻¹ * ((b⁻¹).valᵀ * D * (c⁻¹).val) * ((W.J.map t)⁻¹)ᵀ) * (W.J.map t)ᵀ) *
        c.valᵀᵀ = D := by
      rw [Matrix.mul_neg (X.J.map t), Matrix.neg_mul, neg_neg, transpose_transpose, ← Matrix.mul_assoc (X.J.map t),
        ← Matrix.mul_assoc (X.J.map t), Matrix.mul_nonsing_inv _ hX, Matrix.one_mul, Matrix.mul_assoc _ _ (W.J.map t)ᵀ,
        ← transpose_mul, Matrix.mul_nonsing_inv _ hK, transpose_one, Matrix.mul_one, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← transpose_mul, Units.inv_mul, transpose_one, Matrix.one_mul, Matrix.mul_assoc,
        Units.inv_mul, Matrix.mul_one]
    rw [e2]
  obtain ⟨T₀, y, N, rfl, hN, hdet, hp'⟩ := exists_siegel hcm t hK c hp hT
  obtain ⟨φ₁, hφ₁, ha⟩ := hloc p hp φ₀ hφ₀
  have k1 := hW.2.2 _ GlobalTheory.DiagForm.lDiag_adm (fun z Φ hΦ => by rw [mul_diagCols]; exact hinv z Φ hΦ) p N hN _
    (hR φ₀ hφ₀).2
  rw [ha R (hR φ₀ hφ₀), GlobalTheory.ModuNorm.modu_norm_eq_absE F E hcm.1, hdet, Fintype.card_fin,
    char_idl hcm χX hP.resX, ← hlam, ← hlam, ← hm _ hφ₁, hcd p hp φ₀ hφ₀ φ₁ hφ₁ ha, map_smul,
    form_comp_invT _ (GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v) (GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v) m htr hmu _ T₀ hT
      (hι.bij.mapsTo hφ₀), hm _ hφ₀, Fintype.card_fin, smul_eq_mul, ← mul_assoc] at k1
  have k2 := mul_right_cancel₀ h0 k1
  refine mul_right_cancel₀ (GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet T₀) (n : ℂ)) ?_
  have k3 := GlobalTheory.SplitFlip.apow_add (GlobalTheory.SplitFlip.gdet T₀) (-(n : ℂ) / 2) n
  rw [show -(n : ℂ) / 2 + n = n / 2 by ring] at k3
  rw [k2, hp', map_mul, Units.val_mul, GlobalTheory.SplitFlip.apow_mul, k3]
  ring

end GlobalTheory.SplitLin.DblSiegelScal

end

end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.DblScal in
theorem GlobalTheory.SplitLin.scalW_main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ h ∈ UAt σ W (evFin F v), κ h = (chrW χX t (GlobalTheory.SplitFlip.gdet (locMat t c h)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t c h)) (-(n : ℂ) / 2) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c ι hι κ hκ h hh
  obtain ⟨⟨-, dd, omd, hdc, hws, hbox⟩, -, -⟩ := hP.weil
  have hspl := hws.2.1
  have hloc := GlobalTheory.T.double_splitting_pair_identity hPr F E σ B n d X W M χX χW om r s r' s' hP dd omd hspl v
  obtain ⟨ιd, hιd, hprod⟩ := GlobalTheory.T.linear_model_double_splitting hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c ι hι dd hdc
  obtain ⟨cd, hcd⟩ := GlobalTheory.T.double_scaling_local_identity hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hspl hloc ιd hιd
  obtain ⟨χd, hχd⟩ := GlobalTheory.T.double_scaling_local_equivariance hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hspl hloc ιd hιd cd hcd
  obtain ⟨gd, hgd⟩ := exists_diag_one h
  have hgdAt : gd ∈ UDAt σ W.J (evFin F v) := by
    intro u hu
    change u • (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) - 1) = 0
    have h1 : u • (mat h - 1) = 0 := hh u hu
    rw [hgd, fromBlocks_sub_one, Matrix.fromBlocks_smul, h1]
    simp
  have e1 : κ h = cd gd := GlobalTheory.T.linear_model_compact_equivariance hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c ι hι κ hκ dd omd hdc hspl
    (fun g gd' hg φ₁ hφ₁ φ₂ hφ₂ => hbox g gd' hg φ₁ hφ₁ φ₂ hφ₂) hloc ιd hιd hprod cd hcd h hh gd hgd
  obtain ⟨p, hpAt, hp⟩ := GlobalTheory.T.double_scaling_iwasawa_decomposition F E σ B n d X W M χX χW om r s r' s' hP v t c (fixDiag (locMat t c h))
  have e5 := GlobalTheory.SplitLin.DblSiegelScal.scalar_siegel hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hdc hws hloc ιd hιd cd hcd p hpAt
    ⟨1, by rw [hp]; exact fixDiag_diag _⟩
  rw [hp, gdet_fixDiag] at e5
  have f1 : cd gd = χd (GlobalTheory.SplitFlip.gdet (locMat t c h)) := by rw [hχd gd hgdAt, gdet_locMatD_diag t c h gd hgd]
  have f2 : cd p = χd (GlobalTheory.SplitFlip.gdet (locMat t c h)) := by rw [hχd p hpAt, hp, gdet_fixDiag]
  rw [e1, f1, ← f2]
  exact e5

end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.SplitLin.om_linW_split : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) (locMat t b g) (locMat t c h) (ι φ) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t b c ι hι g hg h hh φ hφ φ₁ hφ₁ hA
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' hp v
  have oneX : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by
    show u • (mat (1 : UA σ X.J) - 1) = 0
    simp [mat]
  have oneW : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := fun u _ => by
    show u • (mat (1 : UA σ W.J) - 1) = 0
    simp [mat]
  have hspl := hp.weil.isUSplitting
  obtain ⟨φ', ⟨hφ', hA'⟩, -⟩ := hex 1 oneX h hh φ hφ
  obtain ⟨φ'', ⟨hφ'', hA''⟩, -⟩ := hex g hg 1 oneW φ' hφ'
  have hcomp : Acts (evFin F v) (om (g, h)) φ φ'' := by
    intro R hR
    have e : om (g, h) = om (g, 1) * om (1, h) := by rw [← map_mul]; simp
    have hR' : Rest (evFin F v) φ' R := ⟨hR.1, by rw [← hA' R hR]; exact hspl.pres (1, h) _ hR.2⟩
    rw [e, Module.End.mul_apply, hA' R hR, hA'' R hR']
  have e1 : φ₁ = φ'' := (hex g hg h hh φ hφ).unique ⟨hφ₁, hA⟩ ⟨hφ'', hcomp⟩
  obtain ⟨κW, hW⟩ := GlobalTheory.T.linear_model_unitary_conjugate hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι
  obtain ⟨κX, hX⟩ := GlobalTheory.T.linear_model_compact_conjugate_exists hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι
  have sW := GlobalTheory.SplitLin.scalW_main hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι κW hW h hh
  have sX := GlobalTheory.T.linear_model_unitary_intertwines hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι κX hX g hg
  rw [e1, hX g hg φ' hφ' φ'' hφ'' hA'', hW h hh φ hφ φ' hφ' hA', sW, sX]
  funext Y
  simp only [GlobalTheory.SplitFlip.omA, Pi.smul_apply, smul_eq_mul, Fintype.card_fin, MonoidHom.inv_apply,
    Units.val_inv_eq_inv_val, inv_inv, Matrix.mul_assoc]
  ring

end

section
open scoped Matrix
open GlobalTheory.SplitLin.OppLagr in

theorem GlobalTheory.SplitLin.OppLagr.act_linBar : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinBar B.ψ t b c ι →
    ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omB (chrW χW t) (chrW χX t) (locMat t b g) (locMat t c h) (ι φ) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c ι hι g hg h hh φ hφ φ₁ hφ₁ hA
  have hcm : IsCMExt F E σ := hP.base.cm
  have hJX : (X.J.map t).det ≠ 0 := det_map_ne_zero (det_ne_zero_herm hP.herm) t
  have hJW : (W.J.map t).det ≠ 0 := det_map_ne_zero (det_ne_zero_skew hP.skew) t
  have hb : b.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  have hc : c.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp c.isUnit).ne_zero
  let P : GL (Fin n) (Fv F v) := Matrix.nonsingInvUnit (-(b.1ᵀ * X.J.map t)) (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_neg, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero hb hJX)))
  let Q : GL (Fin d) (Fv F v) := Matrix.nonsingInvUnit (c.1ᵀ * W.J.map t) (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hc hJW))
  have hPv : P.1 = -(b.1ᵀ * X.J.map t) := rfl
  have hQv : Q.1 = c.1ᵀ * W.J.map t := rfl
  have hW2 : M.IsLinW B.ψ (t.comp σ) P⁻¹ Q⁻¹ ι := by
    unfold Model.IsLinW
    unfold Model.IsLinBar at hι
    rw [comp_comp hcm]
    convert hι using 2
    funext u
    simp only [inv_inv, hPv, hQv, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_assoc]
  have key := GlobalTheory.SplitLin.om_linW_split hPr F E σ B n d X W M χX χW om r s r' s' hP v (t.comp σ) P⁻¹ Q⁻¹ ι hW2 g hg h hh φ hφ φ₁ hφ₁ hA
  have eg : locMat (t.comp σ) P⁻¹ g = GlobalTheory.SplitFlip.invT (locMat t b g) := by
    change P⁻¹⁻¹ * _ * P⁻¹ = GlobalTheory.SplitFlip.invT (b⁻¹ * _ * b)
    rw [inv_inv]
    exact conj_eq_invT b P _ _ (X.J.map t) (-1) (GlobalTheory.Div.CoordOpp.unit_map σ g t) (by rw [hPv, neg_one_smul])
  have eh : locMat (t.comp σ) Q⁻¹ h = GlobalTheory.SplitFlip.invT (locMat t c h) := by
    change Q⁻¹⁻¹ * _ * Q⁻¹ = GlobalTheory.SplitFlip.invT (c⁻¹ * _ * c)
    rw [inv_inv]
    exact conj_eq_invT c Q _ _ (W.J.map t) 1 (GlobalTheory.Div.CoordOpp.unit_map σ h t) (by rw [hQv, one_smul])
  rw [key, eg, eh, chrW_comp hcm χW hP.resW, chrW_comp hcm χX hP.resX, inv_inv, omA_invT]

end
