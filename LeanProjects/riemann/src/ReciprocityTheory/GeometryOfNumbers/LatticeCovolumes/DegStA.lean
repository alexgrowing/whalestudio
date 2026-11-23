import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder Matrix

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem IsFrame.ds_spanK_eq {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    Submodule.span K (Set.range v) = Submodule.span K (E : Set V) := by
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hv.1 i)
  · exact Submodule.span_le.mpr hv.2.2

theorem IsFrame.length_eq_latticeRank {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    r = latRank K E := by
  unfold latRank
  rw [← hv.ds_spanK_eq, finrank_span_eq_card hv.2.1, Fintype.card_fin]

theorem exists_isFullRankFamily_of_fg (E : Submodule (𝓞 K) V) (hE : E.FG) :
    ∃ r, ∃ v : Fin r → V, IsFrame K E v := by
  obtain ⟨S, hS⟩ := hE
  obtain ⟨b, hbE, hspan, hli⟩ := exists_linearIndependent K (E : Set V)
  have hEle : ∀ x ∈ E, x ∈ Submodule.span K (S : Set V) := by
    intro x hx
    rw [← hS] at hx
    exact Submodule.span_le_restrictScalars (𝓞 K) K (S : Set V) hx
  have hfin : Finite b := by
    refine hli.finite_of_le_span_finite _ (S : Set V) ?_
    rintro _ ⟨x, rfl⟩
    exact hEle _ (hbE x.2)
  let _ := Fintype.ofFinite b
  refine ⟨Fintype.card b, fun i => ((Fintype.equivFin b).symm i : V), ?_, ?_, ?_⟩
  · intro i; exact hbE ((Fintype.equivFin b).symm i).2
  · exact hli.comp _ (Fintype.equivFin b).symm.injective
  · intro x hx
    have : x ∈ Submodule.span K (b : Set V) := hspan ▸ Submodule.subset_span hx
    have hr : Set.range (fun i => ((Fintype.equivFin b).symm i : V)) = b := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact ((Fintype.equivFin b).symm i).2
      · intro hy; exact ⟨Fintype.equivFin b ⟨y, hy⟩, by simp⟩
    rw [SetLike.mem_coe, hr]
    exact this

theorem IsFrame.relIndex_span_frame_ne_zero {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0 := by
  classical
  set S := Submodule.span (𝓞 K) (Set.range v) with hSdef
  set H := S.toAddSubgroup.addSubgroupOf E.toAddSubgroup with hH
  have : Module.Finite (𝓞 K) E := Module.Finite.iff_fg.mpr hE
  have : Module.Finite ℤ E := Module.Finite.trans (𝓞 K) E
  have hfg : AddGroup.FG E := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hfg' : AddGroup.FG E.toAddSubgroup := hfg
  have : Module.Finite ℤ E.toAddSubgroup := Module.Finite.iff_addGroup_fg.mpr hfg'
  have : Module.Finite ℤ (E.toAddSubgroup ⧸ H) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' H).toIntLinearMap
      (QuotientAddGroup.mk'_surjective H)
  have : Finite (E.toAddSubgroup ⧸ H) := by
    apply Module.finite_of_fg_torsion
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hv.2.2 x.2)
      obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
      have hd : ∀ i, IsIntegral ℤ (y • c i) := fun i => hy _ (Finset.mem_image_of_mem c (Finset.mem_univ i))
      let d : Fin r → 𝓞 K := fun i => ⟨y • c i, hd i⟩
      refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
      have hmem : (y • (x : V)) ∈ S := by
        have : y • (x : V) = ∑ i, d i • v i := by
          rw [← hc, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← algebraMap_smul K (d i) (v i), ← smul_assoc]
          rfl
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      show (y : ℤ) • (QuotientAddGroup.mk x : E.toAddSubgroup ⧸ H) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
      exact hmem
  exact AddSubgroup.index_ne_zero_of_finite

section
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem HermFam.ds_form_zero_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) : h.form σ x 0 = 0 := by
  have := h.add_right σ x 0 0
  rw [add_zero] at this
  linear_combination -this

theorem HermFam.ds_form_sum_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ x (∑ i ∈ s, f i) = ∑ i ∈ s, h.form σ x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.ds_form_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, ih]

theorem HermFam.ds_form_sum_left (h : HermFam K V) (σ : K →+* ℂ) (y : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ (∑ i ∈ s, f i) y = ∑ i ∈ s, h.form σ (f i) y := by
  rw [← h.conj_symm, h.ds_form_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => h.conj_symm σ y (f i)

theorem HermFam.ds_form_smul_left (h : HermFam K V) (σ : K →+* ℂ) (a : K) (x y : V) :
    h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm, h.smul_right, map_mul, h.conj_symm]

theorem HermFam.ds_gram_comb (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} (v : Fin r → V)
    (G : Matrix (Fin r) (Fin r) K) :
    h.gram σ (fun j => ∑ i, G i j • v i) = (G.map σ)ᴴ * h.gram σ v * G.map σ := by
  ext a b
  simp only [HermFam.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, h.ds_form_sum_left, h.ds_form_sum_right, h.ds_form_smul_left, h.smul_right,
    Finset.sum_mul, Complex.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem HermFam.ds_gram_det_re_pos (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) : 0 < (h.gram σ v).det.re := by
  have := (h.posDef σ r v hv).det_pos
  exact (Complex.pos_iff.mp this).1

theorem HermFam.ds_gram_comb_det_re (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} (v : Fin r → V)
    (G : Matrix (Fin r) (Fin r) K) :
    (h.gram σ (fun j => ∑ i, G i j • v i)).det.re =
      Complex.normSq (σ G.det) * (h.gram σ v).det.re := by
  rw [h.ds_gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, RingHom.map_det]
  have : star (σ.mapMatrix G).det * (h.gram σ v).det * (σ.mapMatrix G).det =
      (Complex.normSq (σ.mapMatrix G).det : ℂ) * (h.gram σ v).det := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]; ring
  rw [RingHom.mapMatrix_apply] at this ⊢
  rw [this, Complex.re_ofReal_mul]

theorem HermFam.ds_log_gram_comb (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) (G : Matrix (Fin r) (Fin r) K) (hG : G.det ≠ 0) :
    Real.log (h.gram σ (fun j => ∑ i, G i j • v i)).det.re =
      Real.log (Complex.normSq (σ G.det)) + Real.log (h.gram σ v).det.re := by
  rw [h.ds_gram_comb_det_re, Real.log_mul]
  · exact (Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hG)).ne'
  · exact (h.ds_gram_det_re_pos σ hv).ne'

end

section
variable {K : Type*} [Field K] [NumberField K]

theorem ds_prod_embeddings_eq_norm (x : K) :
    ∏ σ : K →+* ℂ, σ x = algebraMap ℚ ℂ (Algebra.norm ℚ x) := by
  rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => by simp [RingHom.equivRatAlgHom_apply])

theorem ds_sum_log_normSq_embeddings (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log (Complex.normSq (σ x)) = 2 * Real.log |(Algebra.norm ℚ x : ℝ)| := by
  rw [← Real.log_prod (fun σ _ => (Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hx)).ne'),
    ← map_prod, ds_prod_embeddings_eq_norm]
  have hn : (Algebra.norm ℚ x : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx)
  rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.normSq_ofReal, Real.log_mul hn hn,
    Real.log_abs]
  ring

end

end ReciprocityTheory.GeometryOfNumbersTheory
