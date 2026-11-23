import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces

open NumberField IsDedekindDomain Set Filter Topology Matrix
open scoped NumberField.AdeleRing Classical

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem normAtPlace_ringEquiv_mixedSpace (z : InfiniteAdeleRing K) (w : InfinitePlace K) :
    mixedEmbedding.normAtPlace w (InfiniteAdeleRing.ringEquiv_mixedSpace K z) = ‖z w‖ := by
  by_cases hw : w.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) _
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hw
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) _

theorem norm_ringEquiv_mixedSpace_le {z : InfiniteAdeleRing K} {c : ℝ} (h : ∀ w, ‖z w‖ ≤ c) :
    ‖InfiniteAdeleRing.ringEquiv_mixedSpace K z‖ ≤ c := by
  classical
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [normAtPlace_ringEquiv_mixedSpace]
  exact h w

theorem norm_archMatrix_le {M : ArchMatrix K n} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, ‖(M : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) i j‖ ≤ c) :
    ‖M‖ ≤ n * c := by
  let M' : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) := M
  have hdef : ‖M‖ = ((Finset.univ.sup fun i => ∑ j, ‖M' i j‖₊ : NNReal) : ℝ) :=
    Matrix.linfty_opNorm_def M'
  rw [hdef]
  have hrow : ∀ i, ∑ j, ‖M' i j‖₊ ≤ (n : NNReal) * c.toNNReal := fun i => by
    calc ∑ j, ‖M' i j‖₊ ≤ ∑ _j : Fin n, c.toNNReal := Finset.sum_le_sum fun j _ => by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hc]
          exact h i j
      _ = (n : NNReal) * c.toNNReal := by simp
  have h2 := Finset.sup_le (s := Finset.univ) (f := fun i => ∑ j, ‖M' i j‖₊) fun i _ => hrow i
  calc ((Finset.univ.sup fun i => ∑ j, ‖M' i j‖₊ : NNReal) : ℝ)
      ≤ (((n : NNReal) * c.toNNReal : NNReal) : ℝ) := NNReal.coe_le_coe.2 h2
    _ = n * c := by rw [NNReal.coe_mul, Real.coe_toNNReal _ hc, NNReal.coe_natCast]

theorem norm_entry_le_norm_archMatrix (M : ArchMatrix K n) (i j : Fin n) :
    ‖(M : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) i j‖ ≤ ‖M‖ := by
  let M' : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) := M
  have hdef : ‖M‖ = ((Finset.univ.sup fun i => ∑ j, ‖M' i j‖₊ : NNReal) : ℝ) :=
    Matrix.linfty_opNorm_def M'
  rw [hdef]
  have h1 : ‖M' i j‖₊ ≤ ∑ j', ‖M' i j'‖₊ :=
    Finset.single_le_sum (f := fun j' => ‖M' i j'‖₊) (fun _ _ => zero_le) (Finset.mem_univ j)
  have h2 := Finset.le_sup (f := fun i => ∑ j', ‖M' i j'‖₊) (Finset.mem_univ i)
  exact NNReal.coe_le_coe.2 (h1.trans h2)

variable (K n) in

def archMat : Matrix (Fin n) (Fin n) 𝔸[K] →+* ArchMatrix K n :=
  (archMatrixEquiv K n).toRingHom.comp
    ((RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).mapMatrix)

theorem archMat_apply (M : Matrix (Fin n) (Fin n) 𝔸[K]) (i j : Fin n) :
    (archMat K n M : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) i j =
      InfiniteAdeleRing.ringEquiv_mixedSpace K ((M i j).1) := rfl

theorem continuous_archMat : Continuous (archMat K n) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) 𝔸[K] =>
    archMatrixEquiv K n (M.map fun a => a.1)
  exact (continuous_archMatrixEquiv K n).comp (continuous_id.matrix_map continuous_fst)

theorem archMat_diagonal (d : Fin n → 𝔸[K]) :
    (archMat K n (Matrix.diagonal d) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) =
      Matrix.diagonal fun i => InfiniteAdeleRing.ringEquiv_mixedSpace K (d i).1 := by
  refine Matrix.ext fun i j => ?_
  rw [archMat_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs with h
  · rfl
  · exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace K)

theorem conj_blockEntry_apply_eq_zero {r : ℕ} {b : AdelicGLn.AdelicGL K n} (hb : b ∈ adelicBorel)
    (P : UPos n r → 𝔸[K]) {i j : Fin n} (hij : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ))) :
    (((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry P *
      (b : Matrix (Fin n) (Fin n) 𝔸[K])) i j = 0 := by
  have hb' : ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]).IsUpperTriangular :=
    mem_adelicBorel.1 (inv_mem hb)
  have hb1 : (b : Matrix (Fin n) (Fin n) 𝔸[K]).IsUpperTriangular := mem_adelicBorel.1 hb
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hmj : j < m
  · rw [hb1 hmj, mul_zero]
  by_cases hli : l < i
  · rw [hb' hli, zero_mul, zero_mul]
  rw [blockEntry_apply, dif_neg, mul_zero, zero_mul]
  intro h
  apply hij
  have h1 : (i : ℕ) ≤ l := not_lt.1 hli
  have h2 : (m : ℕ) ≤ j := not_lt.1 hmj
  exact ⟨lt_of_le_of_lt h1 h.1, le_trans h.2 h2⟩

theorem norm_ringEquiv_posIdele_le {s : ℝ} (hs : 0 < s) :
    ‖InfiniteAdeleRing.ringEquiv_mixedSpace K ((posIdele (K := K) s hs : 𝔸[K]).1)‖ ≤ s := by
  refine norm_ringEquiv_mixedSpace_le fun w => ?_
  rw [← GroundTheory.Global.IdeleGroup.coe_infiniteProj, infiniteProj_posIdele, norm_posRealToUnits w hs]

theorem le_pow_mul_of_siegel {ρ : Fin n → ℝ} {t : ℝ} (ht : 0 < t) (hρ : ∀ i, 0 < ρ i)
    (hsieg : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) :
    ∀ (d : ℕ) (l m : Fin n), (m : ℕ) = l + d → ρ m ≤ (max 1 t⁻¹) ^ d * ρ l := by
  intro d
  induction d with
  | zero =>
    intro l m hlm
    rw [pow_zero, one_mul, Fin.ext (by omega : (m : ℕ) = l)]
  | succ d ih =>
    intro l m hlm
    have hm1 : (m : ℕ) - 1 < n := by omega
    set m' : Fin n := ⟨m - 1, hm1⟩
    have h1 := ih l m' (by simp [m']; omega)
    have h2 : t * ρ m ≤ ρ m' := hsieg m' m (by simp [m']; omega)
    have h3 : ρ m ≤ max 1 t⁻¹ * ρ m' := by
      calc ρ m = t⁻¹ * (t * ρ m) := by field_simp
        _ ≤ t⁻¹ * ρ m' := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 ht.le)
        _ ≤ max 1 t⁻¹ * ρ m' := mul_le_mul_of_nonneg_right (le_max_right _ _) (hρ m').le
    calc ρ m ≤ max 1 t⁻¹ * ρ m' := h3
      _ ≤ max 1 t⁻¹ * ((max 1 t⁻¹) ^ d * ρ l) :=
        mul_le_mul_of_nonneg_left h1 (le_trans zero_le_one (le_max_left _ _))
      _ = (max 1 t⁻¹) ^ (d + 1) * ρ l := by ring

theorem div_le_of_siegel {ρ : Fin n → ℝ} {t : ℝ} (ht : 0 < t) (hρ : ∀ i, 0 < ρ i)
    (hsieg : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) {r : ℕ} (hr : 0 < r) (hrn : r < n)
    {i j : Fin n} (hij : (i : ℕ) < r ∧ r ≤ (j : ℕ)) :
    ρ j / ρ i ≤ (max 1 t⁻¹) ^ (2 * n) * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) := by
  set T := max 1 t⁻¹
  have hT1 : 1 ≤ T := le_max_left _ _
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hj : ρ j ≤ T ^ n * ρ ⟨r, hrn⟩ := by
    have := le_pow_mul_of_siegel ht hρ hsieg ((j : ℕ) - r) ⟨r, hrn⟩ j (by simp; omega)
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (hρ _).le)
    exact pow_le_pow_right₀ hT1 (by omega)
  have hi : ρ ⟨r - 1, by omega⟩ ≤ T ^ n * ρ i := by
    have := le_pow_mul_of_siegel ht hρ hsieg (r - 1 - (i : ℕ)) i ⟨r - 1, by omega⟩ (by simp; omega)
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (hρ _).le)
    exact pow_le_pow_right₀ hT1 (by omega)
  have hpi := hρ i
  have hpr := hρ ⟨r - 1, by omega⟩
  have hTn : 0 < T ^ n := pow_pos hTpos n
  rw [div_le_iff₀ hpi]
  have e : T ^ (2 * n) * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) * ρ i =
      (T ^ n * ρ ⟨r, hrn⟩) * (T ^ n * ρ i) / ρ ⟨r - 1, by omega⟩ := by
    rw [pow_mul', sq]
    field_simp
  rw [e, le_div_iff₀ hpr]
  calc ρ j * ρ ⟨r - 1, by omega⟩ ≤ (T ^ n * ρ ⟨r, hrn⟩) * ρ ⟨r - 1, by omega⟩ :=
        mul_le_mul_of_nonneg_right hj hpr.le
    _ ≤ (T ^ n * ρ ⟨r, hrn⟩) * (T ^ n * ρ i) :=
        mul_le_mul_of_nonneg_left hi (mul_pos hTn (hρ _)).le

theorem diagonal_mul_mul_diagonal_apply {R : Type*} [CommRing R] (e d : Fin n → R)
    (Z : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Matrix.diagonal e * Z * Matrix.diagonal d) i j = e i * Z i j * d j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem continuous_blockEntry {r : ℕ} :
    Continuous (blockEntry : (UPos n r → 𝔸[K]) → Matrix (Fin n) (Fin n) 𝔸[K]) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blockEntry_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem ringEquiv_mul_ringEquiv_idele (u v : GroundTheory.Global.IdeleGroup K) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K ((u : 𝔸[K]).1) *
        InfiniteAdeleRing.ringEquiv_mixedSpace K ((v : 𝔸[K]).1) =
      InfiniteAdeleRing.ringEquiv_mixedSpace K (((u * v : GroundTheory.Global.IdeleGroup K) : 𝔸[K]).1) := by
  rw [← map_mul]
  rfl

theorem posIdele_inv_mul {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) :
    (posIdele (K := K) s hs)⁻¹ * posIdele ρ hρ = posIdele (s⁻¹ * ρ) (mul_pos (inv_pos.2 hs) hρ) := by
  have h1 : (posIdele (K := K) s hs)⁻¹ = posIdele s⁻¹ (inv_pos.2 hs) := by
    have := map_inv (posIdeleHom K) ⟨s, hs⟩
    rw [posIdeleHom_apply] at this
    exact this.symm
  rw [h1, posIdele_mul]

theorem exists_norm_archMat_conj_le {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (hωB : ω ⊆ ((adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))) {t : ℝ} (ht : 0 < t) {r : ℕ}
    (hr : 0 < r) (hrn : r < n) {𝒮 : Set (InfiniteAdeleRing K)} (h𝒮 : IsCompact 𝒮) :
    ∃ C : ℝ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)),
      ∀ P : UPos n r → 𝔸[K], (∀ p, (P p).2 = 0) → (∀ p, (P p).1 ∈ 𝒮) →
        ‖archMat K n
            ((((b * diagUnits n (fun i => posIdele (ρ i) (hρ i)) * k)⁻¹ : AdelicGLn.AdelicGL K n) :
              Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry P *
            ((b * diagUnits n (fun i => posIdele (ρ i) (hρ i)) * k : AdelicGLn.AdelicGL K n) :
              Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤
          C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) := by

  obtain ⟨cK1, homogComponent_comm_first_action⟩ := (isCompact_maxCompact (K := K) (n := n)).exists_bound_of_continuousOn
    (f := fun k : AdelicGLn.AdelicGL K n => archMat K n (k : Matrix (Fin n) (Fin n) 𝔸[K]))
    (continuous_archMat.comp Units.continuous_val).continuousOn
  obtain ⟨cK2, homogComponent_comm_second_action⟩ := (isCompact_maxCompact (K := K) (n := n)).exists_bound_of_continuousOn
    (f := fun k : AdelicGLn.AdelicGL K n =>
      archMat K n ((k⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))
    (continuous_archMat.comp Units.continuous_coe_inv).continuousOn
  set cK := max (max cK1 cK2) 0
  have hcK0 : 0 ≤ cK := le_max_right _ _

  set Pset : Set (UPos n r → 𝔸[K]) := Set.pi univ fun _ => {a : 𝔸[K] | a.2 = 0 ∧ a.1 ∈ 𝒮}
  have hPset : IsCompact Pset := by
    refine isCompact_univ_pi fun _ => ?_
    have he : {a : 𝔸[K] | a.2 = 0 ∧ a.1 ∈ 𝒮} =
        (fun x : InfiniteAdeleRing K => ((x, 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)) '' 𝒮 := by
      ext a
      constructor
      · rintro ⟨h2, h1⟩
        exact ⟨a.1, h1, Prod.ext rfl h2.symm⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨rfl, hx⟩
    rw [he]
    exact h𝒮.image (continuous_id.prodMk continuous_const)
  obtain ⟨cZ1, hcZ1⟩ := (hω.prod hPset).exists_bound_of_continuousOn
    (f := fun q : AdelicGLn.AdelicGL K n × (UPos n r → 𝔸[K]) =>
      archMat K n (((q.1⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        blockEntry q.2 * (q.1 : Matrix (Fin n) (Fin n) 𝔸[K])))
    (continuous_archMat.comp (((Units.continuous_coe_inv.comp continuous_fst).matrix_mul
      (continuous_blockEntry.comp continuous_snd)).matrix_mul
        (Units.continuous_val.comp continuous_fst))).continuousOn
  set cZ := max cZ1 0
  have hcZ0 : 0 ≤ cZ := le_max_right _ _
  set T := max 1 t⁻¹
  refine ⟨cK * (n * (T ^ (2 * n) * cZ)) * cK, ?_⟩
  intro b hb ρ hρ hsieg k hk P hP2 hP1
  set a := diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i))
  set q := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩
  have hq : 0 ≤ q := div_nonneg (hρ _).le (hρ _).le
  set Zb := archMat K n (((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
    blockEntry P * (b : Matrix (Fin n) (Fin n) 𝔸[K]))
  have hZb : ‖Zb‖ ≤ cZ := (hcZ1 (b, P) ⟨hb, fun p _ => ⟨hP2 p, hP1 p⟩⟩).trans (le_max_left _ _)

  have hmat : (((b * a * k)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
      blockEntry P * ((b * a * k : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ((k⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        (((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
          (((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry P *
            (b : Matrix (Fin n) (Fin n) 𝔸[K])) * (a : Matrix (Fin n) (Fin n) 𝔸[K])) *
        (k : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [hmat, map_mul, map_mul, map_mul, map_mul]
  set Mid := archMat K n ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * Zb *
    archMat K n (a : Matrix (Fin n) (Fin n) 𝔸[K])

  set E : Fin n → mixedEmbedding.mixedSpace K := fun i =>
    InfiniteAdeleRing.ringEquiv_mixedSpace K
      ((((posIdele (K := K) (ρ i) (hρ i))⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]).1)
  set D : Fin n → mixedEmbedding.mixedSpace K := fun i =>
    InfiniteAdeleRing.ringEquiv_mixedSpace K (((posIdele (K := K) (ρ i) (hρ i)) : 𝔸[K]).1)
  have hainv : ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      Matrix.diagonal fun i => (((posIdele (K := K) (ρ i) (hρ i))⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) := by
    rw [← map_inv, coe_diagUnits]
    rfl
  have hMid : ∀ i j, (Mid : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) i j =
      E i * (Zb : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) i j * D j := by
    intro i j
    change ((archMat K n ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) :
        Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) *
      (Zb : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) *
      (archMat K n (a : Matrix (Fin n) (Fin n) 𝔸[K]) :
        Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K))) i j = _
    rw [hainv, coe_diagUnits, archMat_diagonal, archMat_diagonal]
    exact diagonal_mul_mul_diagonal_apply _ _ _ i j
  have hEnt : ∀ i j, ‖(Mid : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) i j‖ ≤
      T ^ (2 * n) * cZ * q := by
    intro i j
    rw [hMid]
    by_cases hij : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · have hED : E i * D j = InfiniteAdeleRing.ringEquiv_mixedSpace K
          (((posIdele (K := K) ((ρ i)⁻¹ * ρ j) (mul_pos (inv_pos.2 (hρ i)) (hρ j)) :
            GroundTheory.Global.IdeleGroup K) : 𝔸[K]).1) := by
        simp only [E, D]
        rw [ringEquiv_mul_ringEquiv_idele, posIdele_inv_mul]
      have hnED : ‖E i * D j‖ ≤ ρ j / ρ i := by
        rw [hED, div_eq_inv_mul]
        exact norm_ringEquiv_posIdele_le _
      have hZij : ‖(Zb : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) i j‖ ≤ cZ :=
        (norm_entry_le_norm_archMatrix Zb i j).trans hZb
      have hratio := div_le_of_siegel ht hρ hsieg hr hrn hij
      calc ‖E i * (Zb : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) i j * D j‖
          = ‖(E i * D j) * (Zb : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) i j‖ := by
            rw [mul_right_comm]
        _ ≤ ‖E i * D j‖ * ‖(Zb : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) i j‖ :=
            norm_mul_le _ _
        _ ≤ (ρ j / ρ i) * cZ :=
            mul_le_mul hnED hZij (norm_nonneg _) (div_nonneg (hρ _).le (hρ _).le)
        _ ≤ (T ^ (2 * n) * q) * cZ := mul_le_mul_of_nonneg_right hratio hcZ0
        _ = T ^ (2 * n) * cZ * q := by ring
    · have h0 : (Zb : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) i j = 0 := by
        simp only [Zb]
        rw [archMat_apply, conj_blockEntry_apply_eq_zero (hωB hb) P hij]
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace K)
      rw [h0, mul_zero, zero_mul, norm_zero]
      positivity
  have hMidn : ‖Mid‖ ≤ n * (T ^ (2 * n) * cZ * q) :=
    norm_archMatrix_le (by positivity) hEnt
  have hk1 : ‖archMat K n (k : Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤ cK :=
    (homogComponent_comm_first_action k hk).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hk2 : ‖archMat K n ((k⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤ cK :=
    (homogComponent_comm_second_action k hk).trans ((le_max_right _ _).trans (le_max_left _ _))
  calc ‖archMat K n ((k⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * Mid *
        archMat K n (k : Matrix (Fin n) (Fin n) 𝔸[K])‖
      ≤ ‖archMat K n ((k⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖ * ‖Mid‖ *
          ‖archMat K n (k : Matrix (Fin n) (Fin n) 𝔸[K])‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ cK * (n * (T ^ (2 * n) * cZ * q)) * cK := by
        gcongr
    _ = cK * (n * (T ^ (2 * n) * cZ)) * cK * q := by ring

end CuspidalSpectrum

end

end GroundTheory.Automorphic
