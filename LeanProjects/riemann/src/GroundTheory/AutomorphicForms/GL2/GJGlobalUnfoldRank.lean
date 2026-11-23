import Mathlib
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.SingleMemInitialCoordSubspace

open Function Module

namespace GroundTheory.Automorphic.GJGlobal

namespace RankDecomp

variable {K : Type*} [Field K] {n : ℕ} (k : ℕ)

def U0 : Submodule K (Fin n → K) := by
  first
  | exact @GroundTheory.Variant₂.N1.initialCoordSubspace _ _ _ k
  | exact GroundTheory.Variant₂.N1.initialCoordSubspace ..
  | (intros; apply GroundTheory.Variant₂.N1.initialCoordSubspace <;> assumption)

variable {k}

theorem mem_U0 {v : Fin n → K} : v ∈ U0 k ↔ ∀ i : Fin n, k ≤ (i : ℕ) → v i = 0 := Iff.rfl

theorem single_mem_U0 {j : Fin n} (hj : (j : ℕ) < k) (c : K) : (Pi.single j c : Fin n → K) ∈ U0 k := by
  intro i hi
  rw [Pi.single_apply, if_neg (by rintro rfl; omega)]

theorem finrank_U0 (hk : k ≤ n) : finrank K (U0 (K := K) (n := n) k) = k := by
  classical
  let f : (Fin k → K) →ₗ[K] (Fin n → K) :=
    { toFun := fun w i => if h : (i : ℕ) < k then w ⟨i, h⟩ else 0
      map_add' := fun a b => by funext i; by_cases h : (i : ℕ) < k <;> simp [h]
      map_smul' := fun c a => by funext i; by_cases h : (i : ℕ) < k <;> simp [h] }
  have hinj : Injective f := by
    intro a b hab
    funext j
    have := congrFun hab ⟨j, lt_of_lt_of_le j.2 hk⟩
    simpa [f, j.2] using this
  have hrange : LinearMap.range f = U0 k := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩ i hi
      simp [f, not_lt.2 hi]
    · intro hv
      refine ⟨fun j => v ⟨j, lt_of_lt_of_le j.2 hk⟩, funext fun i => ?_⟩
      by_cases h : (i : ℕ) < k
      · simp [f, h]
      · simp [f, h, hv i (not_lt.1 h)]
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, finrank_fin_fun]

def IsBlockUpper (k : ℕ) (M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j : Fin n, k ≤ (i : ℕ) → (j : ℕ) < k → M i j = 0

theorem isBlockUpper_iff {M : Matrix (Fin n) (Fin n) K} :
    IsBlockUpper k M ↔ ∀ v ∈ U0 k, M.mulVec v ∈ U0 k := by
  classical
  constructor
  · intro hM v hv i hi
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) < k
    · rw [hM i j hi hj, zero_mul]
    · rw [hv j (not_lt.1 hj), mul_zero]
  · intro h i j hi hj
    have := h _ (single_mem_U0 hj 1) i hi
    simpa [Matrix.mulVec_single_one] using this

variable (k) in

def parabolic : Subgroup (GL (Fin n) K) where
  carrier := {γ | IsBlockUpper k (γ : Matrix (Fin n) (Fin n) K) ∧
    IsBlockUpper k ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    rw [isBlockUpper_iff] at ha1 ha2 hb1 hb2
    refine ⟨isBlockUpper_iff.2 fun v hv => ?_, isBlockUpper_iff.2 fun v hv => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact ha1 _ (hb1 v hv)
    · rw [mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hb2 _ (ha2 v hv)
  one_mem' := by
    refine ⟨fun i j hi hj => ?_, fun i j hi hj => ?_⟩ <;>
    · simp only [inv_one, Units.val_one]
      rw [Matrix.one_apply, if_neg (by intro h; subst h; omega)]
  inv_mem' := by
    rintro a ⟨h1, h2⟩
    exact ⟨h2, by simpa using h1⟩

theorem mulVec_mem_U0_iff {p : GL (Fin n) K} (hp : p ∈ parabolic k) (v : Fin n → K) :
    (p : Matrix (Fin n) (Fin n) K).mulVec v ∈ U0 k ↔ v ∈ U0 k := by
  constructor
  · intro h
    have := (isBlockUpper_iff.1 hp.2) _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at this
  · exact fun h => isBlockUpper_iff.1 hp.1 v h

def kerM (Z : Matrix (Fin n) (Fin n) K) : Submodule K (Fin n → K) :=
  LinearMap.ker Z.mulVecLin

theorem mem_kerM {Z : Matrix (Fin n) (Fin n) K} {v : Fin n → K} : v ∈ kerM Z ↔ Z.mulVec v = 0 :=
  Iff.rfl

theorem kerM_mul (Z : Matrix (Fin n) (Fin n) K) (γ : GL (Fin n) K) (v : Fin n → K) :
    v ∈ kerM (Z * (γ : Matrix (Fin n) (Fin n) K)) ↔ (γ : Matrix (Fin n) (Fin n) K).mulVec v ∈ kerM Z := by
  rw [mem_kerM, mem_kerM, ← Matrix.mulVec_mulVec]

theorem rank_add_finrank_kerM (Z : Matrix (Fin n) (Fin n) K) : Z.rank + finrank K (kerM Z) = n := by
  rw [Matrix.rank, kerM, LinearMap.finrank_range_add_finrank_ker, finrank_fin_fun]

theorem U0_le_kerM_iff {Z : Matrix (Fin n) (Fin n) K} :
    U0 k ≤ kerM Z ↔ ∀ i j : Fin n, (j : ℕ) < k → Z i j = 0 := by
  classical
  constructor
  · intro h i j hj
    have := h (single_mem_U0 hj 1)
    rw [mem_kerM, Matrix.mulVec_single_one] at this
    exact congrFun this i
  · intro h v hv
    rw [mem_kerM]
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) < k
    · rw [h i j hj, zero_mul]
    · rw [hv j (not_lt.1 hj), mul_zero]

variable (k) in

def R : Set (Matrix (Fin n) (Fin n) K) :=
  {Z | (∀ i j : Fin n, (j : ℕ) < k → Z i j = 0) ∧ Z.rank = n - k}

theorem mem_R_iff (hk : k ≤ n) {Z : Matrix (Fin n) (Fin n) K} : Z ∈ R k ↔ kerM Z = U0 k := by
  have hsum := rank_add_finrank_kerM Z
  constructor
  · rintro ⟨h1, h2⟩
    refine (Submodule.eq_of_le_of_finrank_eq (U0_le_kerM_iff.2 h1) ?_).symm
    rw [finrank_U0 hk]
    omega
  · intro h
    refine ⟨U0_le_kerM_iff.1 h.ge, ?_⟩
    rw [h, finrank_U0 hk] at hsum
    omega

theorem exists_GL_map_eq (hk : k ≤ n) {W : Submodule K (Fin n → K)} (hW : finrank K W = k) :
    ∃ δ : GL (Fin n) K, ∀ v, v ∈ W ↔ (δ : Matrix (Fin n) (Fin n) K).mulVec v ∈ U0 k := by
  obtain ⟨C, hC⟩ := W.exists_isCompl
  obtain ⟨C', hC'⟩ := (U0 (K := K) (n := n) k).exists_isCompl
  have h1 : finrank K W = finrank K (U0 (K := K) (n := n) k) := by rw [hW, finrank_U0 hk]
  have h2 : finrank K C = finrank K C' := by
    have a := Submodule.finrank_add_eq_of_isCompl hC
    have b := Submodule.finrank_add_eq_of_isCompl hC'
    omega
  let e : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (Submodule.prodEquivOfIsCompl W C hC).symm ≪≫ₗ
      ((LinearEquiv.ofFinrankEq W (U0 k) h1).prodCongr (LinearEquiv.ofFinrankEq C C' h2)) ≪≫ₗ
      Submodule.prodEquivOfIsCompl (U0 k) C' hC'
  have he : ∀ v, v ∈ W ↔ e v ∈ U0 k := by
    intro v
    obtain ⟨⟨w, c⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl W C hC).surjective v
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.prodCongr_apply]
    simp only [Submodule.coe_prodEquivOfIsCompl']
    constructor
    · intro hv
      have hc : (c : Fin n → K) = 0 := by
        have hcW : (c : Fin n → K) ∈ W := by
          have := W.sub_mem hv w.2
          simpa using this
        have := Submodule.disjoint_def.1 hC.disjoint _ hcW c.2
        exact this
      have hc0 : c = 0 := Subtype.ext hc
      subst hc0
      simp
    · intro hv
      have hc : ((LinearEquiv.ofFinrankEq C C' h2 c : C') : Fin n → K) = 0 := by
        have hcU : ((LinearEquiv.ofFinrankEq C C' h2 c : C') : Fin n → K) ∈ U0 k := by
          have hw := (LinearEquiv.ofFinrankEq W (U0 (K := K) (n := n) k) h1 w).2
          have := Submodule.sub_mem (U0 (K := K) (n := n) k) hv hw
          rwa [add_sub_cancel_left] at this
        exact Submodule.disjoint_def.1 hC'.disjoint _ hcU (LinearEquiv.ofFinrankEq C C' h2 c).2
      have hc0 : c = 0 := by
        have : (LinearEquiv.ofFinrankEq C C' h2 c) = 0 := Subtype.ext hc
        exact (LinearEquiv.ofFinrankEq C C' h2).map_eq_zero_iff.1 this
      subst hc0
      simp
  let A := LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K))
  let B := LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K))
  have hAB : A * B = 1 := by
    simp only [A, B, ← LinearMap.toMatrix'_comp]
    rw [show ((e : (Fin n → K) →ₗ[K] (Fin n → K)).comp (e.symm : (Fin n → K) →ₗ[K] (Fin n → K))) =
      LinearMap.id from by ext; simp]
    exact LinearMap.toMatrix'_id
  have hBA : B * A = 1 := by
    simp only [A, B, ← LinearMap.toMatrix'_comp]
    rw [show ((e.symm : (Fin n → K) →ₗ[K] (Fin n → K)).comp (e : (Fin n → K) →ₗ[K] (Fin n → K))) =
      LinearMap.id from by ext; simp]
    exact LinearMap.toMatrix'_id
  refine ⟨⟨A, B, hAB, hBA⟩, fun v => ?_⟩
  show v ∈ W ↔ A.mulVec v ∈ U0 k
  rw [LinearMap.toMatrix'_mulVec]
  exact he v

theorem rank_mul_GL (Z : Matrix (Fin n) (Fin n) K) (γ : GL (Fin n) K) :
    (Z * (γ : Matrix (Fin n) (Fin n) K)).rank = Z.rank :=
  Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units γ)

variable (k) in

def mulMap (S : Set (GL (Fin n) K)) (x : S × R (K := K) (n := n) k) :
    {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k} :=
  ⟨x.2.1 * ((x.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), by rw [rank_mul_GL]; exact x.2.2.2⟩

theorem bijective_mulMap (hk : k ≤ n) {S : Set (GL (Fin n) K)}
    (hS : ∀ γ₀ : GL (Fin n) K, ∃! p : parabolic (K := K) (n := n) k, (p : GL (Fin n) K) * γ₀ ∈ S) :
    Bijective (mulMap k S) := by
  constructor
  · rintro ⟨⟨γ, hγ⟩, ⟨Z, hZ⟩⟩ ⟨⟨γ', hγ'⟩, ⟨Z', hZ'⟩⟩ h
    have hξ : Z * (γ : Matrix (Fin n) (Fin n) K) = Z' * (γ' : Matrix (Fin n) (Fin n) K) :=
      congrArg Subtype.val h
    have hZk := (mem_R_iff hk).1 hZ
    have hZk' := (mem_R_iff hk).1 hZ'
    have hker : ∀ v, (γ : Matrix (Fin n) (Fin n) K).mulVec v ∈ U0 k ↔
        (γ' : Matrix (Fin n) (Fin n) K).mulVec v ∈ U0 k := by
      intro v
      have e1 : (γ : Matrix (Fin n) (Fin n) K).mulVec v ∈ U0 k ↔
          v ∈ kerM (Z * (γ : Matrix (Fin n) (Fin n) K)) := by rw [kerM_mul, hZk]
      have e2 : (γ' : Matrix (Fin n) (Fin n) K).mulVec v ∈ U0 k ↔
          v ∈ kerM (Z' * (γ' : Matrix (Fin n) (Fin n) K)) := by rw [kerM_mul, hZk']
      rw [e1, e2, hξ]
    have hp : γ' * γ⁻¹ ∈ parabolic k := by
      refine ⟨isBlockUpper_iff.2 fun v hv => ?_, isBlockUpper_iff.2 fun v hv => ?_⟩
      · have := (hker (((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v)).1
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec,
          Matrix.mulVec_mulVec, ← Units.val_mul] at this
        exact this hv
      · have := (hker (((γ'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v)).2
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec,
          Matrix.mulVec_mulVec, ← Units.val_mul] at this
        rw [mul_inv_rev, inv_inv]
        exact this hv
    obtain ⟨p₀, -, hp₀⟩ := hS γ
    have e1 : (1 : parabolic k) = p₀ := hp₀ 1 (by simpa using hγ)
    have e2 : (⟨γ' * γ⁻¹, hp⟩ : parabolic k) = p₀ := hp₀ _ (by simpa using hγ')
    have h1 : (1 : GL (Fin n) K) = γ' * γ⁻¹ := congrArg Subtype.val (e1.trans e2.symm)
    have hγγ : γ' = γ := mul_inv_eq_one.1 h1.symm
    subst hγγ
    have hZZ : Z = Z' := by
      have := congrArg (· * ((γ'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hξ
      simpa [Matrix.mul_assoc, ← Units.val_mul] using this
    subst hZZ
    rfl
  · rintro ⟨ξ, hξ⟩
    have hW : finrank K (kerM ξ) = k := by
      have := rank_add_finrank_kerM ξ
      omega
    obtain ⟨δ, hδ⟩ := exists_GL_map_eq hk hW
    obtain ⟨p, hp, -⟩ := hS δ
    refine ⟨(⟨(p : GL (Fin n) K) * δ, hp⟩,
      ⟨ξ * ((((p : GL (Fin n) K) * δ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        (mem_R_iff hk).2 ?_⟩), ?_⟩
    · ext v
      rw [kerM_mul, hδ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_rev, ← mul_assoc,
        mul_inv_cancel, one_mul, mulVec_mem_U0_iff (inv_mem p.2)]
    · apply Subtype.ext
      show ξ * ((((p : GL (Fin n) K) * δ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((p : GL (Fin n) K) * δ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ξ
      rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end RankDecomp

end GroundTheory.Automorphic.GJGlobal
