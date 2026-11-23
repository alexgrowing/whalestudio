import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeOfLocalMatrixFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramFrameEmbeddingMatrixNormOfVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDeterminantLineTwoHermitianLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqLeOfNoShortVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalBasisLatticeOfInverseAdelicMatrixFamiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantSmulStandardBasisInverseFramesStatement

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.LocMatSlope

variable {K : Type} [Field K] [NumberField K]

theorem exists_locBasis {n : ℕ} (A : HeightOneSpectrum (𝓞 K) → Matrix (Fin n) (Fin n) K) (hA : IsAdelic A)
    (P : HeightOneSpectrum (𝓞 K)) : ∃ s : 𝓞 K, s ∉ P.asIdeal ∧
      GlobalTheory.PtDeg.LocBasis P (locLat A) (fun j => (s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) :=
  GlobalTheory.T.exists_localBasis_lattice_of_inverse_adelicMatrixFamily K n A hA P

theorem det_gramPl [StarRing K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (eqv : ι ≃ Fin n)
    (Y : (K →+* ℂ) → Matrix ι ι ℂ) (hY : ∀ σ, (Y σ).det ≠ 0) (t : K) (v : InfinitePlace K) :
    (Formalism.HN.gramPl (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v
      (fun k => t • (Pi.single (eqv.symm k) 1 : ι → K))).det.re =
      ‖v.embedding t‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 :=
  GlobalTheory.T.gramDeterminant_smul_standardBasis_inverse_frames K ι n eqv Y hY t v

theorem smul_single_mem {ι : Type} [Fintype ι] [DecidableEq ι] (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K)
    (d : 𝓞 K) (hd : ∀ w, IntAt w ((d : K) • A w)) (i : ι) : (d : K) • (Pi.single i 1 : ι → K) ∈ locLat A := by
  intro w j
  have : (A w *ᵥ ((d : K) • (Pi.single i 1 : ι → K))) j = ((d : K) • A w) j i := by
    simp [Matrix.mulVec_smul, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  rw [this]; exact hd w j i

theorem isAdelic_reindex {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n)
    {A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K} (hA : IsAdelic A) :
    IsAdelic (fun w => Matrix.reindex e e (A w)) := by
  refine ⟨fun w => by simpa [Matrix.det_reindex_self] using hA.1 w, hA.2.subset fun w hw h => hw ?_⟩
  have hi : ∀ (M : Matrix ι ι K), IntAt w M → IntAt w (Matrix.reindex e e M) :=
    fun M hM i j => by simpa using hM (e.symm i) (e.symm j)
  refine ⟨hi _ h.1, ?_⟩
  show IntAt w (Matrix.reindex e e (A w))⁻¹
  rw [Matrix.inv_reindex]
  exact hi _ h.2

theorem relIndex_reindex {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n)
    (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (t : K) :
    (Submodule.span (𝓞 K) (Set.range fun k => t • (Pi.single (e.symm k) 1 : ι → K))).toAddSubgroup.relIndex
        (locLat A).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range fun k => t • (Pi.single k 1 : Fin n → K))).toAddSubgroup.relIndex
        (locLat (fun w => Matrix.reindex e e (A w))).toAddSubgroup := by
  let φ : (ι → K) ≃ₗ[𝓞 K] (Fin n → K) := LinearEquiv.funCongrLeft (𝓞 K) K e.symm
  have hφ : ∀ x, φ x = fun k => x (e.symm k) := fun x => rfl
  have hmv : ∀ (M : Matrix ι ι K) (x : ι → K), Matrix.reindex e e M *ᵥ φ x = φ (M *ᵥ x) := by
    intro M x
    rw [hφ, hφ, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv M _ e.symm e.symm]
    ext k
    simp [Function.comp_def]
  have h1 : (Submodule.span (𝓞 K) (Set.range fun k => t • (Pi.single (e.symm k) 1 : ι → K))).map
      (φ : (ι → K) →ₗ[𝓞 K] (Fin n → K)) = Submodule.span (𝓞 K) (Set.range fun k => t • (Pi.single k 1 : Fin n → K)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext k
    simp only [Function.comp_apply, LinearEquiv.coe_coe, hφ]
    funext j
    simp [Pi.single_apply, e.symm_apply_eq, eq_comm]
  have h2 : (locLat A).map (φ : (ι → K) →ₗ[𝓞 K] (Fin n → K)) = locLat (fun w => Matrix.reindex e e (A w)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ w i
      rw [LinearEquiv.coe_coe, hmv, hφ]
      exact hx w (e.symm i)
    · intro hy
      refine ⟨φ.symm y, fun w i => ?_, by simp⟩
      have := hy w (e i)
      rw [show y = φ (φ.symm y) by simp, hmv, hφ] at this
      simpa using this
  rw [← h1, ← h2, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  exact (AddSubgroup.relIndex_map_map_of_injective _ _ φ.injective).symm

theorem vAdd_mul_inv_pow {P : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∉ P.asIdeal) (x : K) (n : ℕ) :
    vAdd P (x * ((s : K) ^ n)⁻¹) = vAdd P x := by
  have h1 : P.valuation K (s : K) = 1 := by
    rw [show ((s : K)) = algebraMap (𝓞 K) K s from rfl, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff]
    exact hs
  unfold vAdd
  rw [map_mul, map_inv₀, map_pow, h1, one_pow, inv_one, mul_one]

theorem log_relIndex {n : ℕ} (A : HeightOneSpectrum (𝓞 K) → Matrix (Fin n) (Fin n) K) (hA : IsAdelic A)
    (t : 𝓞 K) (ht : t ≠ 0) (hmem : ∀ i, (t : K) • (Pi.single i 1 : Fin n → K) ∈ locLat A) :
    (Function.support fun w => (vAdd w ((t : K) ^ n * (A w).det) : ℝ)).Finite ∧
      ∑ᶠ w, (vAdd w ((t : K) ^ n * (A w).det) : ℝ) * lw K w =
        Real.log ((Submodule.span (𝓞 K) (Set.range fun i => (t : K) • (Pi.single i 1 : Fin n → K))).toAddSubgroup.relIndex
          (locLat A).toAddSubgroup : ℝ) / finrank ℚ K := by
  classical
  choose s hs hB using fun P => exists_locBasis A hA P
  have hL := GlobalTheory.LocMatLat.isLattice_locLat K (Fin n) A hA
  have htK : (t : K) ≠ 0 := by simpa using ht
  have hw : ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K (locLat A) (fun i => (t : K) • (Pi.single i 1 : Fin n → K)) := by
    refine ⟨hmem, ?_, fun x _ => ?_⟩
    · have := (Pi.basisFun K (Fin n)).linearIndependent.units_smul (fun _ => Units.mk0 (t : K) htK)
      convert this using 1
      all_goals first
        | rfl
        | (funext i; simp [Pi.basisFun_apply])
    · have hx : x = ∑ i, (x i / t) • ((t : K) • (Pi.single i 1 : Fin n → K)) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply, smul_smul, div_mul_cancel₀ _ htK]
        rw [Algebra.smul_def, show algebraMap (𝓞 K) K t = (t : K) from rfl, mul_div_cancel₀ _ htK]
      rw [SetLike.mem_coe, hx]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcomb : ∀ (P : HeightOneSpectrum (𝓞 K)) (i : Fin n), (t : K) • (Pi.single i 1 : Fin n → K) =
      ∑ j, (Matrix.of fun i j => (t : K) / (s P : K) * A P j i) i j •
        ((s P : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
    intro P i
    have hsK : (s P : K) ≠ 0 := by
      intro h0
      apply hs P
      have : s P = 0 := by simpa using h0
      rw [this]; exact P.asIdeal.zero_mem
    have hcol : ∑ j, A P j i • (Pi.single j 1 : Fin n → K) = A P *ᵥ Pi.single i 1 := by
      funext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    have e1 : ∀ j, (Matrix.of fun i j => (t : K) / (s P : K) * A P j i) i j •
        ((s P : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) =
        (A P)⁻¹ *ᵥ (((t : K) * A P j i) • (Pi.single j 1 : Fin n → K)) := by
      intro j
      rw [Matrix.mulVec_smul, smul_smul, Matrix.of_apply]
      congr 1
      field_simp
    simp only [e1]
    rw [← Matrix.mulVec_sum]
    simp only [← smul_smul]
    rw [← Finset.smul_sum, hcol, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (Ne.isUnit (hA.1 P)), Matrix.one_mulVec]
  obtain ⟨hf, h⟩ := GlobalTheory.LatDetDeg.index_formula hL.fg hw _ _ hB hcomb
  have hv : ∀ P, vAdd P (Matrix.of fun i j => (t : K) / (s P : K) * A P j i).det =
      vAdd P ((t : K) ^ n * (A P).det) := by
    intro P
    have : (Matrix.of fun i j => (t : K) / (s P : K) * A P j i) = ((t : K) / (s P : K)) • (A P)ᵀ := by
      ext i j; simp
    rw [this, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin, div_pow, div_eq_mul_inv, mul_right_comm,
      vAdd_mul_inv_pow (hs P)]
  simp only [hv] at hf h
  exact ⟨hf, h⟩

end GlobalTheory.LocMatSlope

open GlobalTheory.LocMatSlope in

theorem GlobalTheory.LocMatSlope.slope_sq_locLat : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type)
    [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K)
    (Y : (K →+* ℂ) → Matrix ι ι ℂ), IsAdelic A → (∀ σ, (Y σ).det ≠ 0) →
    (∀ σ, ‖(Y ((starRingEnd ℂ).comp σ)).det‖ = ‖(Y σ).det‖) →
    slope_sq (matNorm Y) (locLat A) = 2 * detDeg A Y / (Fintype.card ι : ℝ) := by
  intro K _ _ _ ι _ _ _ A Y hA hY hconj
  classical
  letI : StarRing K := starRingOfComm
  set n := Fintype.card ι with hn
  set eqv : ι ≃ Fin n := Fintype.equivFin ι with heqv
  have hL := GlobalTheory.LocMatLat.isLattice_locLat K ι A hA
  have hG := (GlobalTheory.T.isGramFrame_embeddingMatrixNormOfVector K ι Y hY).1
  rw [slope_sq_eq hG hL.fg]
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.LocMatLat.exists_denom A (hA.2.subset fun w hw h => hw h.1)
  have hdK : (d : K) ≠ 0 := by simpa using hd0
  set e : Fin n → ι → K := fun k => (d : K) • (Pi.single (eqv.symm k) 1 : ι → K) with he
  have hli : LinearIndependent K e := by
    have := ((Pi.basisFun K ι).linearIndependent.comp eqv.symm eqv.symm.injective).units_smul
      (fun _ => Units.mk0 (d : K) hdK)
    convert this using 1
    all_goals first
      | rfl
      | (funext k; simp [he, Pi.basisFun_apply])
  have hle : Submodule.span (𝓞 K) (Set.range e) ≤ locLat A :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact smul_single_mem A d hd _)
  have hrk : Formalism.HN.rkK (locLat A) = n := by
    unfold Formalism.HN.rkK
    rw [hL.span_eq_top, finrank_top, Module.finrank_fintype_fun_eq_card]
  have hL0 : locLat A ≠ ⊥ := by
    intro h0
    have h := hL.span_eq_top
    rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at h
    exact bot_ne_top h
  have hX : ∀ v : InfinitePlace K, IsUnit ((Y v.embedding)⁻¹).det := fun v => (hG v).1
  obtain ⟨-, hmu, -⟩ := Formalism.HN.size_maximal_slope K (ι → K) ι (Pi.basisFun K ι) _ hX _ hL.fg hL0
  have hpos := (Formalism.HN.place_lattice_structure K (ι → K) ι (Pi.basisFun K ι) _ hX _ hL.fg).2.2
  obtain ⟨hg1, hg2⟩ := Formalism.HN.height_gram_determinant K (ι → K) ι (Pi.basisFun K ι) _ hX n e hli
  have hht := hg2 (locLat A) hL.fg hle hrk
  rw [hg1] at hht
  have hA' := isAdelic_reindex eqv hA
  obtain ⟨hfin, hidx⟩ := log_relIndex (fun w => Matrix.reindex eqv eqv (A w)) hA' d hd0
    (fun i => smul_single_mem (fun w => Matrix.reindex eqv eqv (A w)) d
      (fun w i j => by simpa using hd w (eqv.symm i) (eqv.symm j)) i)
  rw [← relIndex_reindex eqv A (d : K)] at hidx
  simp only [Matrix.det_reindex_self] at hfin hidx
  set H := Formalism.HN.ht (Pi.basisFun K ι) (fun v ↦ (Y v.embedding)⁻¹) (locLat A) with hH
  set I : ℕ := (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex (locLat A).toAddSubgroup with hI
  have hidx' : ∑ᶠ w, (vAdd w ((d : K) ^ n * (A w).det) : ℝ) * lw K w = Real.log (I : ℝ) / finrank ℚ K := hidx
  have hdet : ∀ v : InfinitePlace K, (Formalism.HN.gramPl (Pi.basisFun K ι) (fun v ↦ (Y v.embedding)⁻¹) v e).det.re =
      ‖v.embedding (d : K)‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 := fun v => det_gramPl eqv Y hY (d : K) v
  have hdv : ∀ v : InfinitePlace K, 0 < ‖v.embedding (d : K)‖ := fun v => norm_pos_iff.2 ((map_ne_zero _).2 hdK)
  have hYv : ∀ v : InfinitePlace K, 0 < ‖(Y v.embedding).det‖ := fun v => norm_pos_iff.2 (hY _)
  have hfac : ∀ v : InfinitePlace K, 0 < ‖v.embedding (d : K)‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 :=
    fun v => mul_pos (pow_pos (hdv v) _) (pow_pos (hYv v) _)
  simp only [hdet] at hht
  have hprod : 0 < ∏ v : InfinitePlace K, ‖v.embedding (d : K)‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 :=
    Finset.prod_pos fun v _ => hfac v
  have hIpos : (0 : ℝ) < I := by
    rcases Nat.eq_zero_or_pos I with h | h
    · rw [h, Nat.cast_zero, mul_zero] at hht; linarith
    · exact_mod_cast h
  have hlogH : Real.log H = 2 * n * (∑ v : InfinitePlace K, Real.log ‖v.embedding (d : K)‖) +
      2 * (∑ v : InfinitePlace K, Real.log ‖(Y v.embedding).det‖) - Real.log I := by
    have h1 := congrArg Real.log hht
    rw [Real.log_mul hpos.ne' hIpos.ne', Real.log_prod (fun v _ => (hfac v).ne')] at h1
    have h2 : ∀ v : InfinitePlace K, Real.log (‖v.embedding (d : K)‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2) =
        2 * n * Real.log ‖v.embedding (d : K)‖ + 2 * Real.log ‖(Y v.embedding).det‖ := fun v => by
      rw [Real.log_mul (pow_pos (hdv v) _).ne' (pow_pos (hYv v) _).ne', Real.log_pow, Real.log_pow]
      push_cast; ring
    simp only [h2, Finset.sum_add_distrib, ← Finset.mul_sum] at h1
    linarith
  have hsd : ∑ σ : K →+* ℂ, Real.log ‖σ (d : K)‖ = 2 * ∑ v : InfinitePlace K, Real.log ‖v.embedding (d : K)‖ :=
    GlobalTheory.SlopeMink.sum_embeddings_eq_two_mul (fun σ => Real.log ‖σ (d : K)‖) (fun σ => by
      simp [RingHom.comp_apply, Complex.norm_conj])
  have hsY : ∑ σ : K →+* ℂ, Real.log ‖(Y σ).det‖ = 2 * ∑ v : InfinitePlace K, Real.log ‖(Y v.embedding).det‖ :=
    GlobalTheory.SlopeMink.sum_embeddings_eq_two_mul (fun σ => Real.log ‖(Y σ).det‖) (fun σ => by simp only [hconj])
  have hnum := lineDeg_num hdK
  unfold lineDeg at hnum
  have hsplit : ∀ w, (vAdd w ((d : K) ^ n * (A w).det) : ℝ) = n * (vAdd w (d : K) : ℝ) + (vAdd w (A w).det : ℝ) :=
    fun w => by
      rw [GlobalTheory.LatDetDeg.vAdd_mul' w (pow_ne_zero _ hdK) (hA.1 w), GlobalTheory.LatDetDeg.vAdd_pow' w hdK]
      push_cast; ring
  have hfd := finite_vAdd (K := K) hdK
  have hfdet : (Function.support fun w => (vAdd w (A w).det : ℝ)).Finite := by
    refine (hfin.union hfd).subset fun w h => ?_
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
    apply h
    have := hsplit w
    rw [hc.1, hc.2] at this
    show (vAdd w (A w).det : ℝ) = 0
    linarith
  have hsum : ∑ᶠ w, (vAdd w ((d : K) ^ n * (A w).det) : ℝ) * lw K w =
      n * ∑ᶠ w, (vAdd w (d : K) : ℝ) * lw K w + ∑ᶠ w, (vAdd w (A w).det : ℝ) * lw K w := by
    have e1 : ∀ w, (vAdd w ((d : K) ^ n * (A w).det) : ℝ) * lw K w =
        (n : ℝ) * ((vAdd w (d : K) : ℝ) * lw K w) + (vAdd w (A w).det : ℝ) * lw K w := fun w => by
      rw [hsplit]; ring
    simp only [e1]
    rw [finsum_add_distrib ((fin_mul hfd _).subset (Function.support_mul_subset_right _ _)) (fin_mul hfdet _),
      ← mul_finsum]
  have hD : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by exact_mod_cast Formalism.HN.sizeMu_finrank_eq K
  have hF : (0 : ℝ) < Formalism.HN.nPl K := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  rw [hmu]
  unfold Formalism.HN.size
  rw [Real.log_rpow hpos, hrk, hlogH]
  unfold detDeg lineDeg
  rw [hsY]
  rw [hsum, hD] at hidx'
  rw [hsd, hD] at hnum
  set Sa := ∑ v : InfinitePlace K, Real.log ‖v.embedding (d : K)‖
  set Sb := ∑ v : InfinitePlace K, Real.log ‖(Y v.embedding).det‖
  set V := ∑ᶠ w, (vAdd w (A w).det : ℝ) * lw K w
  set W := ∑ᶠ w, (vAdd w (d : K) : ℝ) * lw K w
  set F := (Formalism.HN.nPl K : ℝ)
  have hW : W = 2 * Sa / (2 * F) := by linarith
  have hlogI : Real.log I = 2 * F * (n * W + V) := by
    field_simp at hidx'
    linarith
  rw [hlogI, hW, hD]
  field_simp
  ring
