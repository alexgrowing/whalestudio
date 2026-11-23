import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RealPar.SqInt

variable {p q n : ℕ}

def reixHom {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (e : a ≃ b) :
    Matrix a a ℂ →* Matrix b b ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.toMonoidHom

theorem reixHom_apply {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (e : a ≃ b)
    (g : Matrix a a ℂ) : reixHom e g = Matrix.reindex e e g := rfl

theorem continuous_reixHom {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (e : a ≃ b) :
    Continuous (reixHom e) :=
  continuous_id.matrix_reindex e e

def covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) : T.G →* Formalism.REAL.UJ ε :=
  ((Units.map (reixHom e)).comp T.cov).codRestrict (Formalism.REAL.UJ ε) fun x => h.cov_mem T x

theorem umat_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    umat (covU h T x) = Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) := rfl

theorem continuous_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    Continuous (covU h T) :=
  Continuous.subtype_mk (((continuous_reixHom e).units_map _).comp (continuous_fst.comp T.emb.continuous)) _

theorem surjective_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    Function.Surjective (covU h T) := by
  intro g
  obtain ⟨x, hx⟩ := h.cov_surj T (g := umat g) g.2
  exact ⟨x, Subtype.ext (Units.ext hx)⟩

theorem isClosedEmbedding_emb (T : GrpData p q) :
    Topology.IsClosedEmbedding (fun x : T.G => (T.cov x, T.sq x)) := by
  refine ⟨T.emb, ?_⟩
  have : Set.range (fun x : T.G => (T.cov x, T.sq x)) =
      {z : GL (Ix p q) ℂ × ℂˣ | (z.1 : Mat p q)ᴴ * Jm p q * z.1 = Jm p q} ∩
        {z | (z.2 : ℂ) ^ 2 = (z.1 : Mat p q).det} := by
    ext ⟨g, w⟩
    constructor
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact ⟨T.cov_mem x, T.sq_sq x⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨x, hx, -⟩ := T.bij g h1 w h2
      exact ⟨x, Prod.ext hx.1 hx.2⟩
  rw [this]
  have c1 : Continuous fun z : GL (Ix p q) ℂ × ℂˣ => (z.1 : Mat p q) := Units.continuous_val.comp continuous_fst
  have c2 : Continuous fun z : GL (Ix p q) ℂ × ℂˣ => (z.2 : ℂ) := Units.continuous_val.comp continuous_snd
  exact (isClosed_eq ((c1.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul c1) continuous_const).inter
    (isClosed_eq (c2.pow 2) c1.matrix_det)

theorem norm_sq_eq_one {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    ‖(T.sq x : ℂ)‖ = 1 := by
  have h1 := (mem_Upq _).1 (T.cov_mem x)
  have hJ : (Jm p q).det ≠ 0 := by
    have : (Matrix.reindex e e (Jm p q)).det * (Matrix.reindex e e (Jm p q)).det = 1 := by
      rw [h.reindex_Jm, ← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]
    rw [Matrix.det_reindex_self] at this
    exact left_ne_zero_of_mul_eq_one this
  have h2 := congrArg (fun A => ‖Matrix.det A‖) h1
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, ← T.sq_sq x, norm_pow] at h2
  have h3 : ‖(T.sq x : ℂ)‖ ^ 4 = 1 := by
    apply mul_right_cancel₀ (norm_ne_zero_iff.2 hJ)
    rw [one_mul]
    conv_rhs => rw [← h2]
    ring
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h3

theorem isProperMap_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    IsProperMap (covU h T) := by
  refine isProperMap_iff_isCompact_preimage.2 ⟨continuous_covU h T, fun K hK => ?_⟩
  have hS : IsCompact ((Units.val : ℂˣ → ℂ) ⁻¹' Metric.sphere 0 1) := by
    refine (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff ?_).2 (isCompact_sphere 0 1)
    intro z hz
    have : z ≠ 0 := by rintro rfl; simp at hz
    exact ⟨Units.mk0 z this, rfl⟩
  have hK' : IsCompact ((fun g : Formalism.REAL.UJ ε => (Units.map (reixHom e.symm) g.1 : GL (Ix p q) ℂ)) '' K) :=
    hK.image (((continuous_reixHom e.symm).units_map _).comp continuous_subtype_val)
  refine ((isClosedEmbedding_emb T).isCompact_preimage (hK'.prod hS)).of_isClosed_subset
    (hK.isClosed.preimage (continuous_covU h T)) fun x hx => ⟨⟨covU h T x, hx, Units.ext ?_⟩, ?_⟩
  · change Matrix.reindex e.symm e.symm (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q)) = _
    simp
  · simpa using norm_sq_eq_one h T x

theorem isHaarMeasure_map_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    (T.haar.map (covU h T)).IsHaarMeasure :=
  Measure.isHaarMeasure_map T.haar (covU h T) (continuous_covU h T) (surjective_covU h T)
    (isProperMap_iff_tendsto_cocompact.1 (isProperMap_covU h T)).2

theorem isSqIntOn_of_factors : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T)
    (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → IsSqIntOn ε σ := by
  intro p q n e ε T R σ h hF v w
  have hc : coefOn (ε := ε) σ v w ∘ covU h T = fun g => inner ℂ w (R.U.π g v) := by
    funext x
    simp only [Function.comp, coefOn, umat_covU, hF x]
  have hc1 : Continuous fun g => (inner ℂ w (R.U.π g v) : ℂ) := continuous_const.inner (R.U.cont v)
  have hq := (isProperMap_covU h T).isClosedMap.isQuotientMap (continuous_covU h T) (surjective_covU h T)
  have hc2 : Continuous (coefOn (ε := ε) σ v w) := hq.continuous_iff.2 (hc ▸ hc1)
  haveI := isHaarMeasure_map_covU h T
  rw [Measure.isMulLeftInvariant_eq_smul (Formalism.REAL.muG ε) (T.haar.map (covU h T))]
  refine MemLp.smul_measure ?_ ENNReal.coe_ne_top
  rw [memLp_map_measure_iff hc2.aestronglyMeasurable (continuous_covU h T).measurable.aemeasurable, hc,
    memLp_two_iff_integrable_sq_norm hc1.aestronglyMeasurable]
  exact (R.schur v w).1

end GlobalTheory.RealPar.SqInt

end
