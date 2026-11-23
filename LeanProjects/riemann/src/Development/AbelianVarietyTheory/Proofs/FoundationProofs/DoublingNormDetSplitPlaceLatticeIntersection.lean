import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GraphHeightLattice

noncomputable section

namespace GlobalTheory.SplitInterDet

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint bc)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

def diagGL {K : Type} [Field K] (d : Fin n → Kˣ) : GL (Fin n) K where
  val := Matrix.diagonal fun i => (d i : K)
  inv := Matrix.diagonal fun i => ((d i)⁻¹ : Kˣ)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

theorem mem_int_iff {a : Fv F v} : a ∈ v.adicCompletionIntegers F ↔ ‖a‖₊ ≤ 1 := nnnorm_le_one_iff_mem.symm

theorem nnnorm_det_le {M : Matrix (Fin n) (Fin n) (Fv F v)} (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers F) :
    ‖M.det‖₊ ≤ 1 := by
  rw [← mem_int_iff]
  let N : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F).toSubring := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have hN : M = N.map (v.adicCompletionIntegers F).toSubring.subtype := by ext i j; rfl
  rw [hN, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (N.det).2

theorem nnnorm_det_eq_one {k : GL (Fin n) (Fv F v)}
    (hk : k ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring) : ‖k.1.det‖₊ = 1 := by
  rw [mem_GLint_iff] at hk
  have h1 := nnnorm_det_le hk.1
  have h2 := nnnorm_det_le hk.2
  have h3 : ‖k.1.det‖₊ * ‖(k⁻¹).1.det‖₊ = 1 := by
    rw [← nnnorm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      nnnorm_one]
  refine le_antisymm h1 ?_
  calc (1 : ℝ≥0) = ‖k.1.det‖₊ * ‖(k⁻¹).1.det‖₊ := h3.symm
    _ ≤ ‖k.1.det‖₊ * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ‖k.1.det‖₊ := mul_one _

theorem dualConj_mem {k : GL (Fin n) (Fv F v)}
    (hk : k ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring) :
    dualConj 1 k ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring := by
  rw [mem_GLint_iff] at hk ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [dualConj_val]
    simpa using hk.2 j i
  · rw [← map_inv, dualConj_val]
    simpa using hk.1 j i

theorem isElemDiv_dual {x : GL (Fin n) (Fv F v)} {d : Fin n → (Fv F v)ˣ} (hd : IsElemDiv x d) :
    IsElemDiv (dualConj 1 x) fun i => (d i)⁻¹ := by
  unfold IsElemDiv at hd ⊢
  obtain ⟨k₁, hk₁, k₂, hk₂, hx⟩ := hd
  have hx' : x = k₁ * diagGL d * k₂ := Units.ext (by rw [hx]; rfl)
  refine ⟨dualConj 1 k₁, dualConj_mem hk₁, dualConj 1 k₂, dualConj_mem hk₂, ?_⟩
  have hD : (dualConj 1 (diagGL d)).1 = Matrix.diagonal fun i => (((d i)⁻¹ : (Fv F v)ˣ) : Fv F v) := by
    rw [dualConj_val]
    show (1 * Matrix.diagonal (fun i => (((d i)⁻¹ : (Fv F v)ˣ) : Fv F v)) * 1)ᵀ = _
    rw [Matrix.one_mul, Matrix.mul_one, Matrix.diagonal_transpose]
  rw [hx', map_mul, map_mul, Units.val_mul, Units.val_mul, hD]

private theorem unit_mul_mem_iff' (t : (Fv F v)ˣ) (z : Fv F v) :
    (z ∈ v.adicCompletionIntegers F ∧ ((t⁻¹ : (Fv F v)ˣ) : Fv F v) * z ∈ v.adicCompletionIntegers F) ↔
      (((if ‖(t : Fv F v)‖₊ ≤ 1 then t else 1 : (Fv F v)ˣ)⁻¹ : (Fv F v)ˣ) : Fv F v) * z ∈
        v.adicCompletionIntegers F := by
  have ht : 0 < ‖(t : Fv F v)‖₊ := nnnorm_pos.2 t.ne_zero
  split_ifs with h
  · simp only [mem_int_iff, nnnorm_mul, Units.val_inv_eq_inv_val, nnnorm_inv, inv_mul_le_iff₀ ht, mul_one]
    exact ⟨fun h' => h'.2, fun h' => ⟨h'.trans h, h'⟩⟩
  · simp only [mem_int_iff, nnnorm_mul, Units.val_inv_eq_inv_val, nnnorm_inv, inv_mul_le_iff₀ ht, mul_one,
      inv_one, Units.val_one, nnnorm_one, one_mul]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', h'.trans (not_le.1 h).le⟩⟩

theorem nnnorm_det_inter {a x : GL (Fin n) (Fv F v)} {d : Fin n → (Fv F v)ˣ} (hd : IsElemDiv x d)
    (H : ∀ u : Fin n → Fv F v, ((∀ i, u i ∈ v.adicCompletionIntegers F) ∧
      ∀ i, ((x⁻¹).1 *ᵥ u) i ∈ v.adicCompletionIntegers F) ↔ ∀ i, ((a⁻¹).1 *ᵥ u) i ∈ v.adicCompletionIntegers F) :
    ‖a.1.det‖₊ = ∏ i, min ‖(d i : Fv F v)‖₊ 1 := by
  unfold IsElemDiv at hd
  obtain ⟨k₁, hk₁, k₂, hk₂, hx⟩ := hd
  obtain ⟨m, hm⟩ : ∃ m : Fin n → (Fv F v)ˣ, m = fun i => if ‖(d i : Fv F v)‖₊ ≤ 1 then d i else 1 := ⟨_, rfl⟩
  have hx' : x = k₁ * diagGL d * k₂ := Units.ext (by rw [hx]; rfl)
  obtain ⟨c, hc⟩ : ∃ c : GL (Fin n) (Fv F v), c = k₁ * diagGL m := ⟨_, rfl⟩
  have hdinv : ∀ (e : Fin n → (Fv F v)ˣ) (w : Fin n → Fv F v) (i : Fin n),
      (((diagGL e)⁻¹).1 *ᵥ w) i = (((e i)⁻¹ : (Fv F v)ˣ) : Fv F v) * w i := by
    intro e w i
    show (Matrix.diagonal (fun j => (((e j)⁻¹ : (Fv F v)ˣ) : Fv F v)) *ᵥ w) i = _
    rw [Matrix.mulVec_diagonal]
  have hk₁' : k₁⁻¹ ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring := inv_mem hk₁
  have hk₂' : k₂⁻¹ ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring := inv_mem hk₂
  have key : ∀ u : Fin n → Fv F v, (∀ i, ((a⁻¹).1 *ᵥ u) i ∈ v.adicCompletionIntegers F) ↔
      ∀ i, ((c⁻¹).1 *ᵥ u) i ∈ v.adicCompletionIntegers F := by
    intro u
    rw [← H]
    have e1 : (x⁻¹).1 *ᵥ u = (k₂⁻¹).1 *ᵥ (((diagGL d)⁻¹).1 *ᵥ ((k₁⁻¹).1 *ᵥ u)) := by
      rw [hx', mul_inv_rev, mul_inv_rev, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
    have e2 : (c⁻¹).1 *ᵥ u = ((diagGL m)⁻¹).1 *ᵥ ((k₁⁻¹).1 *ᵥ u) := by
      rw [hc, mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [e1, e2, (mem_GLint_iff_mulVec.1 hk₁') u, ← (mem_GLint_iff_mulVec.1 hk₂') _]
    simp only [hdinv]
    rw [← forall_and]
    exact forall_congr' fun i => by rw [hm]; exact unit_mul_mem_iff' (d i) _
  have hg : a⁻¹ * c ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring := by
    rw [mem_GLint_iff_mulVec]
    intro u
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, key, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec]
  have hdet : ‖a.1.det‖₊ = ‖c.1.det‖₊ := by
    rw [← mul_inv_cancel_left a c, Units.val_mul, Matrix.det_mul, nnnorm_mul, nnnorm_det_eq_one hg, mul_one]
  rw [hdet, hc, Units.val_mul, Matrix.det_mul, nnnorm_mul, nnnorm_det_eq_one hk₁, one_mul]
  show ‖(Matrix.diagonal fun i => ((m i : (Fv F v)ˣ) : Fv F v)).det‖₊ = _
  rw [Matrix.det_diagonal, nnnorm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hm]
  show ‖((if ‖(d i : Fv F v)‖₊ ≤ 1 then d i else 1 : (Fv F v)ˣ) : Fv F v)‖₊ = _
  split_ifs with hi
  · exact (min_eq_left hi).symm
  · rw [Units.val_one, nnnorm_one]
    exact (min_eq_right (not_le.1 hi).le).symm

theorem mulVec_splitIncl (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (u : Fin n → Fv F v) : M *ᵥ splitIncl h τ u = splitIncl h τ (M.map (splitProj τ) *ᵥ u) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, splitIncl, Matrix.map_apply]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, mul_comm (M i j), splitIdem_mul, smul_smul, mul_comm (u j)]

theorem nnnorm_splitProj_det (h : IsCMExt F E σ) (hJ : IsHermND σ J) {L : Submodule (𝓞 E) (Fin n → E)}
    {τ : E →ₐ[F] Fv F v} {β : GL (Fin n) (Fv F v)} (hβ : IsSplitBasis τ L β) {g : GLoc σ J v}
    {α : GL (Fin n) (Fv F v ⊗[F] E)}
    (H : ∀ y : Fin n → Fv F v ⊗[F] E,
      (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x)
    {d : Fin n → (Fv F v)ˣ} (hd : IsElemDiv (splitEquivIn h hJ τ β g) d) :
    ‖splitProj τ α.1.det‖₊ = ∏ i, min ‖(d i : Fv F v)‖₊ 1 := by
  obtain ⟨αw, hαw⟩ : ∃ αw : GL (Fin n) (Fv F v), αw.1 = α.1.map (splitProj τ) :=
    ⟨Matrix.GeneralLinearGroup.map (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) α, rfl⟩
  have hdet : splitProj τ α.1.det = (β⁻¹ * αw * β).1.det := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul, hαw, AlgHom.map_det]
    rfl
  rw [hdet]
  refine nnnorm_det_inter hd fun u => ?_
  have hA : splitIncl h τ (β.1 *ᵥ u) ∈ latLoc F L v ↔ ∀ i, u i ∈ v.adicCompletionIntegers F :=
    (splitIncl_mem_latLoc_iff h).trans (hβ u).symm
  have hB : splitIncl h τ (β.1 *ᵥ u) ∈ latMoved σ J L v g ↔
      ∀ i, (((splitEquivIn h hJ τ β g)⁻¹).1 *ᵥ u) i ∈ v.adicCompletionIntegers F := by
    rw [mem_latMoved, matHom_mulVec_splitIncl, splitIncl_mem_latLoc_iff h, hβ.mem_iff, splitEquivIn_apply]
    simp only [mul_inv_rev, inv_inv, map_inv, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hC : (∃ z ∈ latLoc F L v, splitIncl h τ (β.1 *ᵥ u) = α.1 *ᵥ z) ↔
      (αw⁻¹).1 *ᵥ (β.1 *ᵥ u) ∈ splitLat τ L := by
    constructor
    · rintro ⟨z, hz, hyz⟩
      have e := congrArg (splitVec τ) hyz
      rw [splitVec_splitIncl, splitVec_mulVec, ← hαw] at e
      rw [e, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact mem_splitLat.2 ⟨z, hz, rfl⟩
    · intro hs
      refine ⟨splitIncl h τ ((αw⁻¹).1 *ᵥ (β.1 *ᵥ u)), (splitIncl_mem_latLoc_iff h).2 hs, ?_⟩
      rw [mulVec_splitIncl, ← hαw, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
  rw [← hA, ← hB, H, hC, hβ.mem_iff]
  simp only [mul_inv_rev, inv_inv, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]

private theorem algebra_norm_prod_pair_eq_mul {K : Type} [Field K] (a b : K) : Algebra.norm K ((a, b) : K × K) = a * b := by
  rw [Algebra.norm_apply]
  have e : Algebra.lmul K (K × K) (a, b) = LinearMap.prodMap (LinearMap.mulLeft K a) (LinearMap.mulLeft K b) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp
  rw [e, LinearMap.det_prodMap, LinearMap.det_mulLeft, LinearMap.det_mulLeft]

theorem norm_eq_split (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (x : Fv F v ⊗[F] E) :
    Algebra.norm (Fv F v) x = splitProj τ x * splitProj (τ.comp σ) x := by
  rw [← Algebra.norm_eq_of_algEquiv (splitAlgEquiv h τ) x, splitAlgEquiv_apply]
  exact algebra_norm_prod_pair_eq_mul _ _

private theorem dualConj_eq_dualConj_one_conj {K : Type} [Field K] (A x : GL (Fin n) K) :
    dualConj A x = dualConj 1 (A * x * A⁻¹) := by
  apply Units.ext
  rw [dualConj_val, dualConj_val]
  simp only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc]

private theorem forall_mem_integers_iff_dotProduct_mem (u : Fin n → Fv F v) : (∀ i, u i ∈ v.adicCompletionIntegers F) ↔
    ∀ s : Fin n → Fv F v, (∀ i, s i ∈ v.adicCompletionIntegers F) → u ⬝ᵥ s ∈ v.adicCompletionIntegers F := by
  classical
  constructor
  · intro hu s hs
    exact sum_mem fun i _ => mul_mem (hu i) (hs i)
  · intro H i
    have := H (Pi.single i 1) fun j => by
      rcases eq_or_ne j i with rfl | hji
      · rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hji]; exact zero_mem _
    rwa [dotProduct_single, mul_one] at this

theorem absEv_det_split (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F))
    (hL : IsSelfDualAt σ J L v) (τ : E →ₐ[F] Fv F v) (β : GL (Fin n) (Fv F v)) (hβ : IsSplitBasis τ L β)
    (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E))
    (H : ∀ y : Fin n → Fv F v ⊗[F] E,
      (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x)
    (d : Fin n → (Fv F v)ˣ) (hd : IsElemDiv (splitEquivIn h hJ τ β g) d) :
    absEv F E v (Matrix.GeneralLinearGroup.det α) = ∏ i, min ‖(d i : Fv F v)‖₊ ‖(d i : Fv F v)‖₊⁻¹ := by
  obtain ⟨β', hβ'eq⟩ : ∃ β' : GL (Fin n) (Fv F v), β' = dualConj 1 (splitGram hJ τ * β) := ⟨_, rfl⟩
  have hXJ : ((splitGram hJ τ * β)⁻¹).1 * J.map τ = (β⁻¹).1 := by
    rw [mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← splitGram_val hJ τ, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one]
  have key : ∀ u t : Fin n → Fv F v, (β'.1 *ᵥ u) ⬝ᵥ (J.map τ *ᵥ t) = u ⬝ᵥ ((β⁻¹).1 *ᵥ t) := by
    intro u t
    rw [hβ'eq, dualConj_val]
    simp only [Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hXJ]
  have hβ' : IsSplitBasis (τ.comp σ) L β' := by
    unfold IsSplitBasis
    intro u
    rw [mem_splitLat_comp_iff h hJ hL, forall_mem_integers_iff_dotProduct_mem]
    constructor
    · intro H' t ht
      rw [key]
      exact H' _ (hβ.mem_iff.1 ht)
    · intro H' s hs
      have hts : β.1 *ᵥ s ∈ splitLat τ L := by
        rw [hβ.mem_iff, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
        exact hs
      have := H' _ hts
      rwa [key, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  have hd' : IsElemDiv (splitEquivIn h hJ (τ.comp σ) β' g) fun i => (d i)⁻¹ := by
    have e : splitEquivIn h hJ (τ.comp σ) β' g = dualConj 1 (splitEquivIn h hJ τ β g) := by
      rw [splitEquivIn_apply, splitEquivIn_apply, splitHom_comp hJ τ g, dualConj_eq_dualConj_one_conj (splitGram hJ τ), hβ'eq,
        ← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    rw [e]
    exact isElemDiv_dual hd
  rw [absEv_apply, Matrix.GeneralLinearGroup.val_det_apply, norm_eq_split h τ, nnnorm_mul,
    nnnorm_splitProj_det h hJ hβ H hd, nnnorm_splitProj_det h hJ hβ' H hd', ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hpos : 0 < ‖(d i : Fv F v)‖₊ := nnnorm_pos.2 (d i).ne_zero
  rw [Units.val_inv_eq_inv_val, nnnorm_inv]
  rcases le_total ‖(d i : Fv F v)‖₊ 1 with hle | hle
  · rw [min_eq_left hle, min_eq_right ((one_le_inv₀ hpos).2 hle), mul_one,
      min_eq_left (hle.trans ((one_le_inv₀ hpos).2 hle))]
  · rw [min_eq_right hle, min_eq_left ((inv_le_one₀ hpos).2 hle), one_mul,
      min_eq_right (((inv_le_one₀ hpos).2 hle).trans hle)]

end GlobalTheory.SplitInterDet

end
