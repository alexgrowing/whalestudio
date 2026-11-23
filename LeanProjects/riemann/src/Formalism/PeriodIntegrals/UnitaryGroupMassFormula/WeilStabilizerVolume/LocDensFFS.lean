import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFF

noncomputable section

namespace PI.VolStabW

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k]

def cols {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) : Fin a → Fin M → k := fun j i ↦ P i j

theorem linInd_cols_iff {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) :
    LinearIndependent k (cols P) ↔ ∀ v : Fin a → k, P *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  have h : ∀ v : Fin a → k, ∑ j, v j • cols P j = P *ᵥ v := by
    intro v
    ext i
    simp [cols, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  simp_rw [h]
  constructor
  · intro H v hv
    funext j
    exact H v hv j
  · intro H v hv j
    rw [H v hv]
    rfl

theorem exists_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) : ∃ L : Matrix (Fin a) (Fin M) k, L * P = 1 := by
  have hker : LinearMap.ker (Matrix.mulVecLin P) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact (linInd_cols_iff P).mp hP v (by simpa using hv)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin P) = LinearMap.toMatrix' g * P := by
    rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rw [← this, hg, LinearMap.toMatrix'_id]

theorem linInd_of_left_inv {M a : ℕ} (W : Matrix (Fin a) (Fin M) k) (P : Matrix (Fin M) (Fin a) k)
    (h : W * P = 1) : LinearIndependent k (cols P) := by
  refine (linInd_cols_iff P).mpr fun v hv ↦ ?_
  have : W *ᵥ (P *ᵥ v) = (W * P) *ᵥ v := Matrix.mulVec_mulVec _ _ _
  rw [h, Matrix.one_mulVec, hv, Matrix.mulVec_zero] at this
  exact this.symm

theorem card_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) :
    Nat.card {W : Matrix (Fin a) (Fin M) k // W * P = 1} = Nat.card k ^ (a * (M - a)) := by
  classical
  obtain ⟨L, hL⟩ := exists_left_inv P hP
  let f : Matrix (Fin a) (Fin M) k →ₗ[k] Matrix (Fin a) (Fin a) k :=
    { toFun := fun W ↦ W * P
      map_add' := fun x y ↦ Matrix.add_mul x y P
      map_smul' := fun c x ↦ Matrix.smul_mul c x P }
  have hf : ∀ W, f W = W * P := fun _ ↦ rfl
  have hsurj : Function.Surjective f := fun Z ↦ ⟨Z * L, by rw [hf, Matrix.mul_assoc, hL, Matrix.mul_one]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_matrix,
    Module.finrank_matrix] at hrk
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hrk
  have hker : Module.finrank k (LinearMap.ker f) = a * (M - a) := by
    rw [Nat.mul_sub]
    omega
  let e : {W : Matrix (Fin a) (Fin M) k // W * P = 1} ≃ LinearMap.ker f :=
    { toFun := fun W ↦ ⟨W.1 - L, by
        rw [LinearMap.mem_ker, hf, Matrix.sub_mul, W.2, hL, sub_self]⟩
      invFun := fun Z ↦ ⟨Z.1 + L, by
        have h0 := Z.2
        rw [LinearMap.mem_ker, hf] at h0
        rw [Matrix.add_mul, h0, hL, zero_add]⟩
      left_inv := fun W ↦ by
        apply Subtype.ext
        simp
      right_inv := fun Z ↦ by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := k), hker]

theorem card_pairs {M a : ℕ} (ha : a ≤ M) :
    Nat.card {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  let e : {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} ≃
      Σ P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)},
        {W : Matrix (Fin a) (Fin M) k // W * P.1 = 1} :=
    { toFun := fun x ↦ ⟨⟨x.1.2, linInd_of_left_inv x.1.1 x.1.2 x.2⟩, ⟨x.1.1, x.2⟩⟩
      invFun := fun y ↦ ⟨(y.2.1, y.1.1), y.2.2⟩
      left_inv := fun x ↦ rfl
      right_inv := fun y ↦ rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [fun P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ↦
    card_left_inv P.1 P.2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  let e2 : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ≃
      {s : Fin a → Fin M → k // LinearIndependent k s} :=
    { toFun := fun P ↦ ⟨cols P.1, P.2⟩
      invFun := fun s ↦ ⟨fun i j ↦ s.1 j i, s.2⟩
      left_inv := fun P ↦ rfl
      right_inv := fun s ↦ rfl }
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e2, card_linearIndependent
    (by rw [Module.finrank_fin_fun]; exact ha), Module.finrank_fin_fun, Nat.card_eq_fintype_card]

end FiniteFieldSplitting

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k] {M a : ℕ}

abbrev swapR (k : Type) [Field k] : k × k →+* k × k := (RingEquiv.prodComm (R := k) (S := k)).toRingHom

def U1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).1

def V1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).2

theorem ffH_fst (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).1 = ∑ i, ∑ j, (x i).2 * (J i j).1 * (y j).1 := by
  simp [ffH, Prod.fst_sum]

theorem ffH_snd (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).2 = ∑ i, ∑ j, (x i).1 * (J i j).2 * (y j).2 := by
  simp [ffH, Prod.snd_sum]

theorem gram_iff (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j)
    (X : Fin a → Fin M → k × k) :
    ffGram (swapR k) J X = T ↔
      V1 X * J.map Prod.fst * (U1 X)ᵀ = T.map Prod.fst := by
  have key : ∀ r s, (ffGram (swapR k) J X r s).1 = (V1 X * J.map Prod.fst * (U1 X)ᵀ) r s := by
    intro r s
    simp only [ffGram, ffH_fst, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, U1,
      V1, Finset.sum_mul]
    exact Finset.sum_comm
  have key2 : ∀ r s, (ffGram (swapR k) J X r s).2 = (ffGram (swapR k) J X s r).1 := by
    intro r s
    simp only [ffGram, ffH_fst, ffH_snd]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have h1 : (J j i).2 = (J i j).1 := by
      have := congrArg Prod.fst (hJ i j)
      simpa using this
    rw [h1]
    ring
  constructor
  · intro h
    ext r s
    rw [← key, h]
    rfl
  · intro h
    funext r s
    refine Prod.ext ?_ ?_
    · rw [key, h]
      rfl
    · rw [key2, key, h, Matrix.map_apply]
      have := congrArg Prod.fst (hT s r)
      simpa using this.symm

theorem fFSplit_nat (M a : ℕ) (ha : a ≤ M)
    (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j) (hJd : IsUnit J.det)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j) (hTd : IsUnit T.det) :
    Nat.card {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  set A := J.map Prod.fst with hA
  set T1 := T.map Prod.fst with hT1
  have hAd : IsUnit A.det := by
    have := hJd.map (RingHom.fst k k)
    rwa [RingHom.map_det] at this
  have hT1d : IsUnit T1.det := by
    have := hTd.map (RingHom.fst k k)
    rwa [RingHom.map_det] at this
  let e : (Fin a → Fin M → k × k) ≃ Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k :=
    { toFun := fun X ↦ (T1⁻¹ * V1 X, A * (U1 X)ᵀ)
      invFun := fun WP r i ↦ ((A⁻¹ * WP.2)ᵀ r i, (T1 * WP.1) r i)
      left_inv := fun X ↦ by
        funext r i
        simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hAd,
          Matrix.mul_nonsing_inv_cancel_left _ _ hT1d, Matrix.transpose_transpose]
        rfl
      right_inv := fun WP ↦ by
        have h1 : V1 (fun r i ↦ ((A⁻¹ * WP.2)ᵀ r i, (T1 * WP.1) r i)) = T1 * WP.1 := rfl
        have h2 : U1 (fun r i ↦ ((A⁻¹ * WP.2)ᵀ r i, (T1 * WP.1) r i)) = (A⁻¹ * WP.2)ᵀ := rfl
        simp only [h1, h2, Matrix.transpose_transpose, Matrix.nonsing_inv_mul_cancel_left _ _ hT1d,
          Matrix.mul_nonsing_inv_cancel_left _ _ hAd] }
  have hcond : ∀ X, ffGram (swapR k) J X = T ↔ (e X).1 * (e X).2 = 1 := by
    intro X
    rw [gram_iff J hJ T hT X, ← hT1, ← hA]
    change V1 X * A * (U1 X)ᵀ = T1 ↔ T1⁻¹ * V1 X * (A * (U1 X)ᵀ) = 1
    have hre : T1⁻¹ * V1 X * (A * (U1 X)ᵀ) = T1⁻¹ * (V1 X * A * (U1 X)ᵀ) := by
      simp only [Matrix.mul_assoc]
    rw [hre]
    constructor
    · intro h
      rw [h, Matrix.nonsing_inv_mul _ hT1d]
    · intro h
      calc V1 X * A * (U1 X)ᵀ = T1 * (T1⁻¹ * (V1 X * A * (U1 X)ᵀ)) :=
            (Matrix.mul_nonsing_inv_cancel_left _ _ hT1d).symm
        _ = T1 := by rw [h, Matrix.mul_one]
  rw [Nat.card_congr (Equiv.subtypeEquiv (p := fun X ↦ ffGram (swapR k) J X = T)
    (q := fun WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k ↦ WP.1 * WP.2 = 1) e hcond),
    card_pairs ha]

end FiniteFieldSplitting

theorem fFSplit_holds : FFSplit := by
  intro k _ _ M a ha J hJ hJd T hT hTd
  rw [FiniteFieldSplitting.fFSplit_nat M a ha J hJ hJd T hT hTd]
  have hq : 0 < Nat.card k := Nat.card_pos
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
  push_cast
  rfl

end PI.VolStabW
