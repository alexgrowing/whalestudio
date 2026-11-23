import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthLocalizedModuleEqZeroOfNotAnnihilatorLe
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent

open NumberField Module ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory.LatticeExtension

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
  {V V' : Type} [AddCommGroup V] [Module (𝓞 K) V] [AddCommGroup V'] [Module (𝓞 K) V']
  [Module (𝓞 K') V'] [IsScalarTower (𝓞 K) (𝓞 K') V'] (φ : V →ₗ[𝓞 K] V')

variable [Module K V] [IsScalarTower (𝓞 K) K V] [Module K' V'] [IsScalarTower (𝓞 K') K' V']

theorem form_eq_sum {L : Type} [Field L] {n : ℕ} (h : HermFam L (Fin n → L)) (s : L →+* ℂ) (x y : Fin n → L) :
    h.form s x y = ∑ a, ∑ b, starRingEnd ℂ (s (x a)) * s (y b) * h.form s (Pi.single a 1) (Pi.single b 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x, pi_eq_sum_univ' y]
  simp only [h.ds_form_sum_left, h.ds_form_sum_right, h.ds_form_smul_left, h.smul_right, Finset.mul_sum,
    mul_assoc]

end GlobalTheory.LatticeExtension

open NumberField Module in
open scoped nonZeroDivisors in
open scoped ComplexOrder in
variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') {n : ℕ} in
private lemma eq_sum_apply_smul_single {F : Type} [Field F] (z : Fin n → F) :
    z = ∑ a, z a • (Pi.single a 1 : Fin n → F) := by
  ext i; simp [Finset.sum_apply, Pi.single_apply]

open NumberField Module in
open scoped nonZeroDivisors in
open scoped ComplexOrder in
variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') {n : ℕ} in
private lemma hermFam_form_map_eq_of_eq_on_basis (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (h' : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K' (Fin n → K'))
    (hf : ∀ s a b, h'.form s (Pi.single a 1) (Pi.single b 1) =
      h.form (s.comp j) (Pi.single a 1) (Pi.single b 1))
    (s : K' →+* ℂ) (x y : Fin n → K) :
    h'.form s (fun i => j (x i)) (fun i => j (y i)) = h.form (s.comp j) x y := by
  conv_rhs => rw [eq_sum_apply_smul_single x, eq_sum_apply_smul_single y]
  conv_lhs => rw [eq_sum_apply_smul_single (fun i => j (x i)),
    eq_sum_apply_smul_single (fun i => j (y i))]
  simp only [_root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_sum_left, _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_sum_right, _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_smul_left,
    _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.smul_right, hf, RingHom.comp_apply]

open NumberField Module in
open scoped nonZeroDivisors in
open scoped ComplexOrder in
variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') {n : ℕ} in
private lemma hermFam_form_zero_right {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam F W) (σ : F →+* ℂ) (x : W) : h.form σ x 0 = 0 := by
  simpa using h.smul_right σ 0 x 0

open NumberField Module in
open scoped nonZeroDivisors in
open scoped ComplexOrder in
variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') {n : ℕ} in
private lemma linearIndependent_map_of_linearIndependent (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (h' : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K' (Fin n → K'))
    (hf : ∀ s a b, h'.form s (Pi.single a 1) (Pi.single b 1) =
      h.form (s.comp j) (Pi.single a 1) (Pi.single b 1))
    {r : ℕ} {v : Fin r → Fin n → K} (hv : LinearIndependent K v) :
    LinearIndependent K' (fun a i => j (v a i)) := by
  obtain ⟨s⟩ : Nonempty (K' →+* ℂ) := inferInstance
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  have hpd := h.posDef (s.comp j) r v hv
  have hx : (fun a => s (c a)) ≠ 0 := by
    obtain ⟨a, ha⟩ := hne
    intro h0
    exact ha (s.injective (by simpa using congrFun h0 a))
  have hpos := hpd.dotProduct_mulVec_pos hx
  have hz : (Matrix.of fun a b => h.form (s.comp j) (v a) (v b)).mulVec (fun a => s (c a)) = 0 := by
    ext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    simp_rw [← hermFam_form_map_eq_of_eq_on_basis j h h' hf s]
    have hsum : ∑ b, h'.form s (fun i => j (v a i)) (fun i => j (v b i)) * s (c b) =
        h'.form s (fun i => j (v a i)) (∑ b, c b • fun i => j (v b i)) := by
      rw [_root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_sum_right]
      simp [_root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.smul_right, mul_comm]
    rw [hsum, hc, hermFam_form_zero_right]
  rw [hz] at hpos
  simp at hpos

open NumberField Module in
open scoped nonZeroDivisors in
open scoped ComplexOrder in
variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') {n : ℕ} in
private lemma map_mem_span_range_map_of_mem_span {r : ℕ} {v : Fin r → Fin n → K} {x : Fin n → K}
    (hx : x ∈ Submodule.span K (Set.range v)) :
    (fun i => j (x i)) ∈ Submodule.span K' (Set.range fun a i => j (v a i)) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
  refine (Submodule.mem_span_range_iff_exists_fun K').2 ⟨fun a => j (c a), ?_⟩
  ext i
  simp [Finset.sum_apply, map_sum]

open NumberField Module in
open scoped nonZeroDivisors in
open scoped ComplexOrder in
variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') {n : ℕ} in
private lemma isFrame_span_image_map (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (h' : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K' (Fin n → K'))
    (hf : ∀ s a b, h'.form s (Pi.single a 1) (Pi.single b 1) =
      h.form (s.comp j) (Pi.single a 1) (Pi.single b 1))
    {B : Submodule (𝓞 K) (Fin n → K)} {r : ℕ} {v : Fin r → Fin n → K} (hB : _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K B v) :
    _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K' (Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (B : Set (Fin n → K))))
      (fun a i => j (v a i)) := by
  unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame at hB ⊢
  obtain ⟨hmem, hli, hsub⟩ := hB
  refine ⟨fun a => Submodule.subset_span ⟨v a, hmem a, rfl⟩,
    linearIndependent_map_of_linearIndependent j h h' hf hli, ?_⟩
  have hle : Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (B : Set (Fin n → K))) ≤
      (Submodule.span K' (Set.range fun a i => j (v a i))).restrictScalars (𝓞 K') := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact map_mem_span_range_map_of_mem_span j (hsub hx)
  intro y hy
  exact hle hy

open NumberField Module in
open scoped nonZeroDivisors in
open scoped ComplexOrder in
variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') {n : ℕ} in
private lemma span_image_map_span_eq_span_image (S : Set (Fin n → K)) :
    Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (Submodule.span (𝓞 K) S : Set (Fin n → K))) =
      Submodule.span (𝓞 K') ((fun c i => j (c i)) '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe]
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      convert zero_mem (Submodule.span (𝓞 K') ((fun c i => j (c i)) '' S)) using 1
      ext i; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      ext i; simp
    | smul c x _ hx =>
      convert Submodule.smul_mem _ (RingOfIntegers.mapRingHom j c) hx using 1
      ext i; simp [Algebra.smul_def]
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

open NumberField Module in
open scoped nonZeroDivisors in
open scoped ComplexOrder in
variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') {n : ℕ} in
private lemma fg_span_image_map_of_fg {B : Submodule (𝓞 K) (Fin n → K)} (hB : B.FG) :
    (Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (B : Set (Fin n → K)))).FG := by
  obtain ⟨S, rfl⟩ := hB
  rw [span_image_map_span_eq_span_image]
  exact Submodule.fg_span (S.finite_toSet.image _)

open NumberField Module in
open scoped nonZeroDivisors in
variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] in
private lemma le_span_range_of_isFrame_fin_zero {B : Submodule (𝓞 L) V} {v : Fin 0 → V}
    (hB : _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame L B v) : B ≤ Submodule.span (𝓞 L) (Set.range v) := by
  unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame at hB
  intro x hx
  have hx' := hB.2.2 hx
  simp [Set.range_eq_empty] at hx'
  simp [hx']

open NumberField Module in
open scoped nonZeroDivisors in
variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] in
private lemma exists_linearForm_vanish_init_eq_one_last {r : ℕ} {v : Fin (r + 1) → V} (hv : LinearIndependent L v) :
    ∃ f : V →ₗ[L] L, (∀ i : Fin r, f (v i.castSucc) = 0) ∧ f (v (Fin.last r)) = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hv).coord (Fin.last r))
  have key : ∀ k, g (v k) = (Module.Basis.span hv).coord (Fin.last r) (Module.Basis.span hv k) := by
    intro k
    rw [← hg]
    simp [Module.Basis.span_apply]
  refine ⟨g, fun i => ?_, ?_⟩
  · rw [key]
    simp [Finsupp.single_apply, Fin.castSucc_ne_last]
  · rw [key]
    simp

open NumberField Module in
open scoped nonZeroDivisors in
variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] in
private lemma map_span_range_eq_one_of_form_last {r : ℕ} {v : Fin (r + 1) → V} {f : V →ₗ[L] L}
    (h0 : ∀ i : Fin r, f (v i.castSucc) = 0) (h1 : f (v (Fin.last r)) = 1) :
    (Submodule.span (𝓞 L) (Set.range v)).map (f.restrictScalars (𝓞 L)) = 1 := by
  rw [Submodule.map_span, Submodule.one_eq_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    induction i using Fin.lastCases with
    | last => simp [h1, Submodule.mem_span_singleton_self]
    | cast i => simp [h0 i]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨v (Fin.last r), Set.mem_range_self _, by simp [h1]⟩

open NumberField Module in
open scoped nonZeroDivisors in
variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] in
private lemma span_range_inf_ker_eq_span_range_castSucc {R : Type} [CommRing R] [Algebra R L] [Module R V]
    [IsScalarTower R L V] [FaithfulSMul R L] {r : ℕ} {v : Fin (r + 1) → V} {f : V →ₗ[L] L}
    (h0 : ∀ i : Fin r, f (v i.castSucc) = 0) (h1 : f (v (Fin.last r)) = 1) :
    Submodule.span R (Set.range v) ⊓ (LinearMap.ker f).restrictScalars R =
      Submodule.span R (Set.range fun i : Fin r => v i.castSucc) := by
  apply le_antisymm
  · rintro x ⟨hx, hk⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hx
    have hk' : f (∑ i, c i • v i) = 0 := hk
    rw [Fin.sum_univ_castSucc, map_add, map_sum] at hk'
    simp only [LinearMap.map_smul_of_tower, h0, h1, smul_zero, Finset.sum_const_zero,
      zero_add] at hk'
    have hc : c (Fin.last r) = 0 := by
      rw [Algebra.smul_def, mul_one] at hk'
      exact (FaithfulSMul.algebraMap_eq_zero_iff R L).1 hk'
    rw [Fin.sum_univ_castSucc, hc, zero_smul, add_zero]
    exact (Submodule.mem_span_range_iff_exists_fun R).2 ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Submodule.subset_span ⟨_, rfl⟩, by simp [h0 i]⟩

open NumberField Module in
open scoped nonZeroDivisors in
variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] in
private lemma relIndex_eq_relIndex_map_mul_relIndex_inf_ker {A B : Submodule (𝓞 L) V} (hAB : A ≤ B)
    (f : V →ₗ[L] L) :
    A.toAddSubgroup.relIndex B.toAddSubgroup =
      (A.map (f.restrictScalars (𝓞 L))).toAddSubgroup.relIndex
          (B.map (f.restrictScalars (𝓞 L))).toAddSubgroup *
        (A ⊓ (LinearMap.ker f).restrictScalars (𝓞 L)).toAddSubgroup.relIndex
          (B ⊓ (LinearMap.ker f).restrictScalars (𝓞 L)).toAddSubgroup := by
  have hk : ∀ C : Submodule (𝓞 L) V, (C ⊓ (LinearMap.ker f).restrictScalars (𝓞 L)).toAddSubgroup =
      C.toAddSubgroup ⊓ ((f.restrictScalars (𝓞 L) : V →ₗ[𝓞 L] L) : V →+ L).ker := by
    intro C; ext x; simp
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup, hk, hk]
  exact _root_.ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.relIndex_eq_map_mul_ker _ hAB

open NumberField Module in
open scoped nonZeroDivisors in
variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] in
private lemma log_relIndex_one_eq_neg_log_absNorm_of_one_le (𝔞 : FractionalIdeal (𝓞 L)⁰ L) (h1 : 1 ≤ (𝔞 : Submodule (𝓞 L) L)) :
    Real.log ((1 : Submodule (𝓞 L) L).toAddSubgroup.relIndex (𝔞 : Submodule (𝓞 L) L).toAddSubgroup) =
      -Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) := by
  have hq : FractionalIdeal.absNorm 𝔞 *
      ((1 : Submodule (𝓞 L) L).toAddSubgroup.relIndex (𝔞 : Submodule (𝓞 L) L).toAddSubgroup : ℚ) = 1 :=
    _root_.ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.absNorm_mul_relIndex_one (𝔞 : Submodule (𝓞 L) L) (FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔞) h1
  have hr : (FractionalIdeal.absNorm 𝔞 : ℝ) *
      ((1 : Submodule (𝓞 L) L).toAddSubgroup.relIndex (𝔞 : Submodule (𝓞 L) L).toAddSubgroup : ℝ) = 1 := by
    exact_mod_cast hq
  rw [eq_inv_of_mul_eq_one_right hr, Real.log_inv]

open NumberField Module in
open scoped nonZeroDivisors in
open scoped ComplexOrder in
variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') {n : ℕ} in
private lemma log_relIndex_map_lemma_4 (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (h' : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K' (Fin n → K'))
    (hf : ∀ s a b, h'.form s (Pi.single a 1) (Pi.single b 1) =
      h.form (s.comp j) (Pi.single a 1) (Pi.single b 1)) (r : ℕ) :
    ∀ {B : Submodule (𝓞 K) (Fin n → K)} {v : Fin r → Fin n → K}, B.FG → _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K B v →
      Real.log ((Submodule.span (𝓞 K') (Set.range fun a i => j (v a i))).toAddSubgroup.relIndex
          (Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (B : Set (Fin n → K)))).toAddSubgroup) /
          finrank ℚ K' =
        Real.log ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex B.toAddSubgroup) /
          finrank ℚ K := by
  induction r with
  | zero =>
    intro B v hB hv
    have hv' := isFrame_span_image_map j h h' hf hv
    rw [AddSubgroup.relIndex_eq_one.2 (le_span_range_of_isFrame_fin_zero hv'),
      AddSubgroup.relIndex_eq_one.2 (le_span_range_of_isFrame_fin_zero hv)]
    simp
  | succ r ih =>
    intro B v hB hv
    have hv' := isFrame_span_image_map j h h' hf hv
    have hB' := fg_span_image_map_of_fg j hB
    have hne := _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame.relIndex_ne_zero hB hv
    have hne' := _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame.relIndex_ne_zero hB' hv'
    have hv0 := hv
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame at hv0
    obtain ⟨hmem, hli, hsub⟩ := hv0
    obtain ⟨f, h0, h1⟩ := exists_linearForm_vanish_init_eq_one_last hli
    let f' : (Fin n → K') →ₗ[K'] K' := ∑ a, j (f (Pi.single a 1)) • LinearMap.proj a
    have hf' : ∀ x : Fin n → K, f' (fun i => j (x i)) = j (f x) := by
      intro x
      conv_rhs => rw [eq_sum_apply_smul_single x]
      simp [f', map_sum, mul_comm]
    have h0' : ∀ i : Fin r, f' (fun k => j (v i.castSucc k)) = 0 := fun i => by
      rw [hf', h0, map_zero]
    have h1' : f' (fun k => j (v (Fin.last r) k)) = 1 := by rw [hf', h1, map_one]
    have hA1 : (Submodule.span (𝓞 K) (Set.range v)).map (f.restrictScalars (𝓞 K)) = 1 :=
      map_span_range_eq_one_of_form_last h0 h1
    have hAB : Submodule.span (𝓞 K) (Set.range v) ≤ B :=
      Submodule.span_le.2 (Set.range_subset_iff.2 hmem)
    have hXfg : (B.map (f.restrictScalars (𝓞 K))).FG := hB.map _
    have hX1 : 1 ≤ B.map (f.restrictScalars (𝓞 K)) := hA1 ▸ Submodule.map_mono hAB
    obtain ⟨w, hw1, hw⟩ := _root_.ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.exists_section_of_image B f hXfg hX1
    have hC : ∀ x ∈ B, x - f x • w ∈ B ⊓ (LinearMap.ker f).restrictScalars (𝓞 K) := by
      intro x hx
      refine ⟨sub_mem hx (hw _ ⟨x, hx, rfl⟩), ?_⟩
      simp [hw1]
    have hCfg : (B ⊓ (LinearMap.ker f).restrictScalars (𝓞 K)).FG := Submodule.FG.of_le hB inf_le_left
    have hCfr : _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K (B ⊓ (LinearMap.ker f).restrictScalars (𝓞 K))
        (fun i : Fin r => v i.castSucc) := by
      unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame
      refine ⟨fun i => ⟨hmem _, by simp [h0 i]⟩, hli.comp _ (Fin.castSucc_injective r), ?_⟩
      intro x hx
      have hx1 : x ∈ Submodule.span K (Set.range v) ⊓ (LinearMap.ker f).restrictScalars K :=
        ⟨hsub hx.1, hx.2⟩
      rw [span_range_inf_ker_eq_span_range_castSucc h0 h1] at hx1
      exact hx1
    have hIH := ih hCfg hCfr
    have hsplit := relIndex_eq_relIndex_map_mul_relIndex_inf_ker hAB f
    rw [hA1, span_range_inf_ker_eq_span_range_castSucc h0 h1] at hsplit
    let 𝔞 : FractionalIdeal (𝓞 K)⁰ K :=
      ⟨B.map (f.restrictScalars (𝓞 K)), FractionalIdeal.isFractional_of_fg hXfg⟩
    have h𝔞 : 𝔞 ≠ 0 := by
      intro h𝔞0
      have h1mem : (1 : K) ∈ (𝔞 : Submodule (𝓞 K) K) := Submodule.one_le.1 hX1
      rw [h𝔞0] at h1mem
      simp at h1mem
    obtain ⟨𝔠, -, h𝔠, hN⟩ := _root_.GlobalTheory.exists_fractionalIdeal_eq_span_image j h𝔞
    have hc1 : 1 ≤ (𝔠 : Submodule (𝓞 K') K') := by
      rw [Submodule.one_le, h𝔠]
      exact Submodule.subset_span ⟨1, Submodule.one_le.1 hX1, map_one j⟩
    have hA'B' : Submodule.span (𝓞 K') (Set.range fun a i => j (v a i)) ≤
        Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (B : Set (Fin n → K))) :=
      Submodule.span_le.2 (Set.range_subset_iff.2 fun a =>
        Submodule.subset_span ⟨v a, hmem a, rfl⟩)
    have hsplit' := relIndex_eq_relIndex_map_mul_relIndex_inf_ker hA'B' f'
    rw [map_span_range_eq_one_of_form_last (v := fun a i => j (v a i)) h0' h1',
      span_range_inf_ker_eq_span_range_castSucc (v := fun a i => j (v a i)) h0' h1'] at hsplit'
    have hBX : (Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (B : Set (Fin n → K)))).map
        (f'.restrictScalars (𝓞 K')) = (𝔠 : Submodule (𝓞 K') K') := by
      rw [h𝔠, Submodule.map_span]
      congr 1
      ext t
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨f x, ⟨x, hx, rfl⟩, (hf' x).symm⟩
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 ha
        exact ⟨_, ⟨x, hx, rfl⟩, hf' x⟩
    have hBC : Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (B : Set (Fin n → K))) ⊓
        (LinearMap.ker f').restrictScalars (𝓞 K') = Submodule.span (𝓞 K')
          ((fun c i => j (c i)) '' ((B ⊓ (LinearMap.ker f).restrictScalars (𝓞 K) :
            Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
      apply le_antisymm
      · rintro y ⟨hy, hk⟩
        have key : ∀ y ∈ Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (B : Set (Fin n → K))),
            y - f' y • (fun i => j (w i)) ∈ Submodule.span (𝓞 K') ((fun c i => j (c i)) ''
              ((B ⊓ (LinearMap.ker f).restrictScalars (𝓞 K) :
                Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
          intro y hy
          induction hy using Submodule.span_induction with
          | mem z hz =>
            obtain ⟨x, hx, rfl⟩ := hz
            have hm : (fun i => j ((x - f x • w) i)) ∈ Submodule.span (𝓞 K')
                ((fun c i => j (c i)) '' ((B ⊓ (LinearMap.ker f).restrictScalars (𝓞 K) :
                  Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) :=
              Submodule.subset_span ⟨x - f x • w, hC x hx, rfl⟩
            convert hm using 1
            ext i
            simp [hf']
          | zero => simp
          | add a b _ _ ha hb =>
            convert add_mem ha hb using 1
            rw [map_add, add_smul]
            abel
          | smul c a _ ha =>
            convert Submodule.smul_mem _ c ha using 1
            rw [LinearMap.map_smul_of_tower, smul_sub, smul_assoc]
        have hk' : f' y = 0 := hk
        simpa [hk'] using key y hy
      · refine le_inf (Submodule.span_mono (Set.image_mono inf_le_left)) ?_
        rw [Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        have hfx : f x = 0 := hx.2
        show f' (fun i => j (x i)) = 0
        rw [hf', hfx, map_zero]
    rw [hBX, hBC] at hsplit'
    have e1 : Real.log ((1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex
        (B.map (f.restrictScalars (𝓞 K))).toAddSubgroup) =
        -Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) := log_relIndex_one_eq_neg_log_absNorm_of_one_le 𝔞 hX1
    have e2 := log_relIndex_one_eq_neg_log_absNorm_of_one_le 𝔠 hc1
    rw [hsplit] at hne ⊢
    rw [hsplit'] at hne' ⊢
    obtain ⟨ha, hb⟩ := mul_ne_zero_iff.1 hne
    obtain ⟨ha', hb'⟩ := mul_ne_zero_iff.1 hne'
    push_cast
    rw [Real.log_mul (Nat.cast_ne_zero.2 ha) (Nat.cast_ne_zero.2 hb),
      Real.log_mul (Nat.cast_ne_zero.2 ha') (Nat.cast_ne_zero.2 hb'), add_div, add_div, e1, e2,
      hIH, neg_div, neg_div, hN]

open NumberField Module in
open scoped nonZeroDivisors in

theorem _root_.GlobalTheory.deg_span_image_eq :
    ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
      (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (h' : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K' (Fin n → K')) (Λ : Submodule (𝓞 K) (Fin n → K)), Λ.FG →
      (∀ s a b, h'.form s (Pi.single a 1) (Pi.single b 1) = h.form (s.comp j) (Pi.single a 1) (Pi.single b 1)) →
      _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h' (Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (Λ : Set (Fin n → K)))) = _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ := by
  intro K K' _ _ _ _ j n h h' Λ hΛ hf
  obtain ⟨r, v, hv⟩ := _root_.ReciprocityTheory.GeometryOfNumbersTheory.exists_isFullRankFamily_of_fg Λ hΛ
  have hv' := isFrame_span_image_map j h h' hf hv
  rw [_root_.ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily h' (fg_span_image_map_of_fg j hΛ) hv', _root_.ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily h hΛ hv]
  unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily
  have hg : ∀ s : K' →+* ℂ, h'.gram s (fun a i => j (v a i)) = h.gram (s.comp j) v := by
    intro s
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram
    ext a b
    simp only [Matrix.of_apply]
    exact hermFam_form_map_eq_of_eq_on_basis j h h' hf s _ _
  simp only [hg]
  have hm := _root_.GlobalTheory.meanLog_comp j (fun σ => (h.gram σ v).det.re)
  unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog at hm
  rw [sub_div, sub_div, log_relIndex_map_lemma_4 j h h' hf r hΛ hv, mul_div_assoc, mul_div_assoc, hm]
