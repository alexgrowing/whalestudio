import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.GelfandTransference.EnergyIdentity
import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.ExistsStarMulSelf

open NumberField NumberField.InfinitePlace Module Matrix

noncomputable section

namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings

abbrev Amb (K : Type) [Field K] [NumberField K] (n : ℕ) : Type :=
  EuclideanSpace ℝ (InfinitePlace K × Fin n × Fin 2)

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def fc (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x : Fin n → K) : Fin n → ℂ :=
  (Xf v)⁻¹ *ᵥ (fun i => v.embedding (x i))

def mkE (c : InfinitePlace K → Fin n → ℂ) : Amb K n :=
  WithLp.toLp 2 (fun p => if p.2.2 = 0 then (c p.1 p.2.1).re else (c p.1 p.2.1).im)

theorem sum_ulift_finset_fin_two_expand (g : Fin 2 → ℝ) : ∑ k, g k = g 0 + g 1 := Fin.sum_univ_two g

theorem inner_mkE (a c : InfinitePlace K → Fin n → ℂ) :
    inner ℝ (mkE a) (mkE c) = ∑ v, ∑ i, (star (a v i) * c v i).re := by
  simp only [mkE, PiLp.inner_apply, PiLp.toLp_apply, Fintype.sum_prod_type, sum_ulift_finset_fin_two_expand]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]
  ring

theorem norm_sq_mkE (c : InfinitePlace K → Fin n → ℂ) :
    ‖mkE c‖ ^ 2 = ∑ v, ∑ i, ‖c v i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_mkE]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

variable [StarRing K]

theorem realize_eq (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x = mkE (fun v => fc Xf v x) := by
  ext p
  have h : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) p.1 x = fun i => p.1.embedding (x i) := by
    funext i
    unfold Formalism.HermitianLatticesTheory.vecAt
    simp
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, Formalism.HermitianLatticesTheory.fcoord, mkE, fc, h]

def yv (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → K) : Amb K n :=
  mkE (fun v => (2 : ℂ) • ((Xf v)ᴴ *ᵥ (fun i => star (v.embedding (ξ i)))))

theorem inner_mkE_fc (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hXf : ∀ v, IsUnit (Xf v).det)
    (x ξ : Fin n → K) (v : InfinitePlace K) :
    ∑ i, (star (fc Xf v x i) * ((2 : ℂ) • ((Xf v)ᴴ *ᵥ (fun i => star (v.embedding (ξ i))))) i).re =
      2 * (v.embedding (∑ i, ξ i * x i)).re := by
  have hinv : Xf v * (Xf v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hXf v)
  have key : star (fc Xf v x) ⬝ᵥ ((Xf v)ᴴ *ᵥ fun i => star (v.embedding (ξ i))) =
      star (v.embedding (∑ i, ξ i * x i)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    unfold fc
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    simp [dotProduct, map_sum, star_sum, map_mul, mul_comm]
  have hsum : ∑ i, (star (fc Xf v x i) * ((2 : ℂ) • ((Xf v)ᴴ *ᵥ fun i => star (v.embedding (ξ i)))) i).re =
      2 * (star (fc Xf v x) ⬝ᵥ ((Xf v)ᴴ *ᵥ fun i => star (v.embedding (ξ i)))).re := by
    simp only [dotProduct, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.mul_re]
    ring
  rw [hsum, key, Complex.star_def, Complex.conj_re]

variable [IsTotallyComplex K]

private theorem trace_re_lemma (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ v : InfinitePlace K, 2 * (v.embedding a).re := by
  classical
  have h1 : ((Algebra.trace ℚ K a : ℚ) : ℂ) = ∑ σ : K →+* ℂ, σ a := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ) (x := a)
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ : K →+* ℂ => σ a)
      (fun τ : K →ₐ[ℚ] ℂ => τ a) (fun σ => rfl)]
    simpa using h
  have h2 : ∑ σ : K →+* ℂ, σ a = ∑ v : InfinitePlace K, (((2 * (v.embedding a).re : ℝ)) : ℂ) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun σ => InfinitePlace.mk σ)]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hne : NumberField.ComplexEmbedding.conjugate v.embedding ≠ v.embedding := by
      intro h
      have hr : v.IsReal :=
        InfinitePlace.isReal_iff.mpr (NumberField.ComplexEmbedding.isReal_iff.mpr h)
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex v)) hr
    have hset : Finset.univ.filter (fun σ => InfinitePlace.mk σ = v) =
        {v.embedding, NumberField.ComplexEmbedding.conjugate v.embedding} := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro h
        rw [← InfinitePlace.mk_embedding v, InfinitePlace.mk_eq_iff] at h
        rcases h with h | h
        · exact Or.inl h
        · right
          rw [← h]
          ext x
          simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
      · rintro (h | h)
        · rw [h]
          exact InfinitePlace.mk_embedding v
        · rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    rw [hset, Finset.sum_pair hne.symm, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h1, h2, Complex.ofReal_sum]

theorem inner_yv (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hXf : ∀ v, IsUnit (Xf v).det)
    (x ξ : Fin n → K) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x) (yv Xf ξ) =
      ((Algebra.trace ℚ K (∑ i, ξ i * x i) : ℚ) : ℝ) := by
  rw [realize_eq]
  unfold yv
  rw [inner_mkE, trace_re_lemma]
  exact Finset.sum_congr rfl fun v _ => inner_mkE_fc Xf hXf x ξ v

end Formalism.L2.Geo.Rec.DualLatticeEmbeddings

open NumberField NumberField.InfinitePlace Module Matrix

noncomputable section

namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem nPl_mul_two [IsTotallyComplex K] : Fintype.card (InfinitePlace K) * 2 = finrank ℚ K := by
  rw [NumberField.IsTotallyComplex.finrank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
  ring

theorem finrank_amb [IsTotallyComplex K] : finrank ℝ (Amb K n) = finrank ℚ K * n := by
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    ← nPl_mul_two]
  ring

theorem exists_int_smul_mem (X : Submodule (𝓞 K) (Fin n → K))
    (hX : Submodule.span K (X : Set (Fin n → K)) = ⊤) (v : Fin n → K) :
    ∃ N : ℤ, N ≠ 0 ∧ N • v ∈ X := by
  classical
  have hv : v ∈ Submodule.span K (X : Set (Fin n → K)) := by rw [hX]; trivial
  obtain ⟨m, f, g, hg⟩ := (Submodule.mem_span_set' (R := K)).1 hv
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [← hg, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  let r : 𝓞 K := ⟨y • f i, hi⟩
  have hr : y • (f i • (g i : Fin n → K)) = r • (g i : Fin n → K) := by
    rw [← algebraMap_smul K r, ← smul_assoc]
    rfl
  rw [hr]
  exact X.smul_mem r (g i).2

variable [StarRing K]

def Mz (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (X : Submodule (𝓞 K) (Fin n → K)) :
    Submodule ℤ (Amb K n) :=
  Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf) X

theorem mem_Mz (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (X : Submodule (𝓞 K) (Fin n → K))
    (z : Amb K n) : z ∈ Mz Xf X ↔ ∃ x ∈ X, Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x = z := by
  unfold Mz Formalism.HN.zl
  show z ∈ AddSubgroup.map _ _ ↔ _
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]

theorem discrete_Mz (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hXf : ∀ v, IsUnit (Xf v).det)
    (X : Submodule (𝓞 K) (Fin n → K)) (hfg : X.FG) : DiscreteTopology (Mz Xf X) :=
  (Formalism.HN.place_lattice_structure K (Fin n → K) (Fin n) (Pi.basisFun K (Fin n)) Xf hXf X hfg).1.2

theorem span_Mz [IsTotallyComplex K] (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hXf : ∀ v, IsUnit (Xf v).det)
    (X : Submodule (𝓞 K) (Fin n → K)) (hX : Submodule.span K (X : Set (Fin n → K)) = ⊤) :
    Submodule.span ℝ (Mz Xf X : Set (Amb K n)) = ⊤ := by
  classical
  choose N hN0 hNX using fun k : Fin n => exists_int_smul_mem X hX (Pi.basisFun K (Fin n) k)
  let c : ℤ := ∏ k, N k
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hN0 k
  have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.2 hc0
  have hli := Formalism.HN.PlaceLattice.linIndep_real (Pi.basisFun K (Fin n)) Xf hXf (c : K) hcK
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K) × Fin n) = finrank ℝ (Amb K n) := by
    rw [finrank_amb, Fintype.card_prod, ← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank,
      Fintype.card_fin]
  have htop := hli.span_eq_top_of_card_eq_finrank' hcard
  rw [eq_top_iff, ← htop]
  refine Submodule.span_mono ?_
  rintro _ ⟨⟨m, k⟩, rfl⟩
  rw [SetLike.mem_coe, mem_Mz]
  refine ⟨_, ?_, rfl⟩
  have h1 : (c : K) • (Pi.basisFun K (Fin n) k) = (∏ j ∈ Finset.univ.erase k, N j) • (N k • Pi.basisFun K (Fin n) k) := by
    rw [smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ k), Int.cast_smul_eq_zsmul]
  rw [integralBasis_apply, algebraMap_smul, h1]
  exact X.smul_mem _ (X.toAddSubgroup.zsmul_mem (hNX k) _)

end Formalism.L2.Geo.Rec.DualLatticeEmbeddings

open NumberField NumberField.InfinitePlace Module Matrix

noncomputable section

namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [StarRing K] [IsTotallyComplex K]

theorem zdual_eq_yv (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hXf : ∀ v, IsUnit (Xf v).det)
    (X : Submodule (𝓞 K) (Fin n → K)) (hX : Submodule.span K (X : Set (Fin n → K)) = ⊤)
    (y : Amb K n) (hy : y ∈ Formalism.HadamardInequality.zdual (Mz Xf X)) :
    ∃ ξ : Fin n → K, y = yv Xf ξ ∧
      ∀ x ∈ X, Algebra.trace ℚ K (∑ i, ξ i * x i) ∈ Set.range (Int.cast : ℤ → ℚ) := by
  classical
  set Rz := Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf with hRz
  let φ : (Fin n → K) →+ ℝ := AddMonoidHom.mk' (fun x => inner ℝ (Rz x) y)
    (fun a b => by simp only [map_add, inner_add_left])
  have hφ : ∀ x, φ x = inner ℝ (Rz x) y := fun x => rfl
  have hint : ∀ x ∈ X, ∃ k : ℤ, φ x = k := fun x hx => hy (Rz x) ((mem_Mz Xf X _).2 ⟨x, hx, rfl⟩)
  have hrat : ∀ v, ∃ q : ℚ, (q : ℝ) = φ v := by
    intro v
    obtain ⟨N, hN0, hNv⟩ := exists_int_smul_mem X hX v
    obtain ⟨k, hk⟩ := hint _ hNv
    rw [map_zsmul, zsmul_eq_mul] at hk
    have hN : (N : ℝ) ≠ 0 := Int.cast_ne_zero.2 hN0
    refine ⟨(k : ℚ) / N, ?_⟩
    push_cast
    rw [← hk]
    field_simp
  choose ψ0 hψ0 using hrat
  let ψa : (Fin n → K) →+ ℚ := AddMonoidHom.mk' ψ0 (fun a b => by
    have h := hψ0 (a + b)
    rw [map_add, ← hψ0 a, ← hψ0 b] at h
    exact_mod_cast h)
  let ψ : (Fin n → K) →ₗ[ℚ] ℚ := ψa.toRatLinearMap
  have hψ : ∀ v, (ψ v : ℝ) = φ v := fun v => hψ0 v
  let B := (Algebra.traceForm ℚ K).toDual (traceForm_nondegenerate ℚ K)
  let ξ : Fin n → K := fun i => B.symm (ψ ∘ₗ LinearMap.single ℚ (fun _ : Fin n => K) i)
  have hξ : ∀ i a, Algebra.trace ℚ K (ξ i * a) = ψ (Pi.single i a) := by
    intro i a
    have h := LinearMap.BilinForm.toDual_def (traceForm_nondegenerate ℚ K) (m := ξ i) (n := a)
    rw [Algebra.traceForm_apply] at h
    rw [← h]
    show (B (B.symm _)) a = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have htr : ∀ x, Algebra.trace ℚ K (∑ i, ξ i * x i) = ψ x := by
    intro x
    rw [map_sum]
    simp_rw [hξ]
    rw [← map_sum, Finset.univ_sum_single]
  refine ⟨ξ, ?_, fun x hx => ?_⟩
  · have horth : ∀ x, inner ℝ (Rz x) (y - yv Xf ξ) = 0 := by
      intro x
      rw [inner_sub_right, inner_yv Xf hXf, htr, hψ, hφ, sub_self]
    have hspan : ∀ z ∈ Submodule.span ℝ (Mz Xf X : Set (Amb K n)), inner ℝ z (y - yv Xf ξ) = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, -, rfl⟩ := (mem_Mz Xf X z).1 hz
        exact horth x
      | zero => simp
      | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
      | smul r a _ ha => rw [real_inner_smul_left, ha, mul_zero]
    have h0 := hspan (y - yv Xf ξ) (by rw [span_Mz Xf hXf X hX]; trivial)
    rw [inner_self_eq_zero, sub_eq_zero] at h0
    exact h0
  · obtain ⟨k, hk⟩ := hint x hx
    refine ⟨k, ?_⟩
    rw [htr]
    have : (ψ x : ℝ) = (k : ℝ) := by rw [hψ, hk]
    exact_mod_cast this.symm

theorem norm_sq_realize (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) :
    ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x‖ ^ 2 = ∑ v, ∑ i, ‖fc Xf v x i‖ ^ 2 := by
  rw [realize_eq, norm_sq_mkE]

theorem norm_sq_yv (cj : K → K) (hσ : ∀ (v : InfinitePlace K) z, v.embedding (cj z) = star (v.embedding z))
    (A : Matrix (Fin n) (Fin n) K) (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hfr : ∀ v, Xf v * (Xf v)ᴴ = A.map v.embedding) (ξ : Fin n → K) :
    ‖yv Xf ξ‖ ^ 2 = 4 * ∑ v : InfinitePlace K, (v.embedding (∑ i, ∑ k, ξ i * A i k * cj (ξ k))).re := by
  have hre : ∀ u : Fin n → ℂ, ∑ i, ‖u i‖ ^ 2 = (star u ⬝ᵥ u).re := by
    intro u
    simp only [dotProduct, Complex.re_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re]
  have hsm : ∀ (u : Fin n → ℂ) (i : Fin n), ‖((2 : ℂ) • u) i‖ ^ 2 = 4 * ‖u i‖ ^ 2 := by
    intro u i
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    norm_num
  unfold yv
  rw [norm_sq_mkE, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp_rw [hsm]
  rw [← Finset.mul_sum, hre]
  congr 2
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hfr v]
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul, hσ, Pi.star_apply, star_star,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
