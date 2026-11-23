import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem w_rev (n : ℕ) (i : Fin n) : w n i.rev = - w n i := by
  have := i.isLt
  simp only [w, Fin.val_rev]
  split_ifs <;> omega

private theorem J_apply {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat K n * Xᵀ * Jmat K n) i j = X j.rev i.rev := by
  simp only [Matrix.mul_apply, Jmat, Matrix.transpose_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have key : ∀ k : Fin n, (j = k.rev) ↔ (k = j.rev) := by
    intro k
    constructor
    · rintro rfl
      simp
    · rintro rfl
      simp
  simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private def tw {K : Type} [CommRing K] (n : ℕ) (u : Kˣ) :
    Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) K where
  toFun X := Matrix.of fun i j => ((u ^ (w n i - w n j) : Kˣ) : K) * X i j
  map_one' := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  map_mul' X Y := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : w n i - w n j = (w n i - w n a) + (w n a - w n j) := by ring
    rw [this, _root_.zpow_add, Units.val_mul]
    ring
  map_zero' := by ext i j; simp
  map_add' X Y := by ext i j; simp [mul_add]
  commutes' c := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply]

private theorem tw_apply {K : Type} [CommRing K] (n : ℕ) (u : Kˣ) (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    tw n u X i j = ((u ^ (w n i - w n j) : Kˣ) : K) * X i j := rfl

private theorem ordProd_tw {H K : Type} [CommRing K] {n : ℕ} (u : Kˣ)
    (r : H → Matrix (Fin n) (Fin n) K) (ψ : Fin n → H → K) (g : Fin n → H) :
    ordProd (fun s => tw n u (r s)) ψ g = tw n u (ordProd r ψ g) := by
  unfold ordProd
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply, map_sub, map_smul, map_one]

theorem UpperTheory.V.Fr.alg_twist :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {K : Type} [CommRing K] (u : Kˣ) (ρ : NRep F n K), ∃ ρ' : NRep F n K, (∀ g i j, ρ'.r g i j = ((u ^ (w n i - w n j) : Kˣ) : K) * ρ.r g i j) ∧ ρ'.ψ = ρ.ψ := by
  intro l _ k _ F n K _ u ρ
  refine ⟨⟨(tw n u).toRingHom.toMonoidHom.comp ρ.r, ρ.ψ, ?_, ?_, ?_⟩, fun g i j => rfl, rfl⟩
  · intro g
    ext i j
    rw [J_apply]
    show tw n u (ρ.r (F.star g)) i j = tw n u (ρ.r g) j.rev i.rev
    rw [tw_apply, tw_apply, ρ.pol, J_apply, w_rev, w_rev]
    congr 3
    ring
  · intro i j h
    have := ρ.diag i j h
    rw [Matrix.sub_apply] at this ⊢
    show tw n u (ρ.r F.g0) i j - tw n u (ρ.r (F.star F.g0)) i j = 0
    rw [tw_apply, tw_apply, ← mul_sub, this, mul_zero]
  · intro v g
    have := ordProd_tw u (fun s => ρ.r (F.loc0 v s)) (fun i s => ((ρ.ψ v i s : Kˣ) : K)) g
    exact this.trans (by rw [ρ.ord, map_zero])
