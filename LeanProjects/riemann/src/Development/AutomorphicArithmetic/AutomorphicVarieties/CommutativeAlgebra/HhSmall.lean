import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Matrix in
private theorem expand_small {O : Type} [CommRing O] [IsLocalRing O] {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R']
    (p : R →ₐ[O] R') (hs : maximalIdeal R * RingHom.ker p = ⊥) (J h Z : Matrix ι ι R)
    (hh : h.map (res O R) = 1) (hZ : Z.map p = 0) :
    (h + Z)ᵀ * J * (h + Z) = hᵀ * J * h + (Zᵀ * J + J * Z) ∧ (h + Z).map (res O R) = 1 := by
  have k : ∀ x y : R, res O R x = 0 → p y = 0 → x * y = 0 := fun x y hx hy => by
    have : x * y ∈ maximalIdeal R * RingHom.ker p :=
      Ideal.mul_mem_mul ((res_eq_zero_iff O R x).1 hx) hy
    rwa [hs, Ideal.mem_bot] at this
  have z1 : ∀ a b, p (Z a b) = 0 := fun a b => congrFun (congrFun hZ a) b
  have z2 : ∀ a b, res O R (Z a b) = 0 := fun a b => by rw [← res_map p, z1, map_zero]
  have h1 : ∀ a b, res O R ((h - 1) a b) = 0 := fun a b => by
    have := congrFun (congrFun hh a) b
    simp only [map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    by_cases e : a = b
    · subst e; simp
    · simp [one_apply_ne e]
  have K : ∀ A B : Matrix ι ι R, (∀ a b, res O R (A a b) = 0) → (∀ a b, p (B a b) = 0) →
      Aᵀ * J * B = 0 ∧ Bᵀ * J * A = 0 := fun A B hA hB => by
    constructor
    · ext a b
      simp only [mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rw [mul_right_comm, k _ _ (hA _ _) (hB _ _), zero_mul]
    · ext a b
      simp only [mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rw [mul_right_comm, mul_comm (B _ _), k _ _ (hA _ _) (hB _ _), zero_mul]
  constructor
  · obtain ⟨e1, e2⟩ := K (h - 1) Z h1 z1
    obtain ⟨e3, -⟩ := K Z Z z2 z1
    rw [transpose_sub, transpose_one, sub_mul, sub_mul, one_mul, sub_eq_zero] at e1
    rw [mul_sub, mul_one, sub_eq_zero] at e2
    rw [transpose_add, add_mul, add_mul, mul_add, mul_add, e1, e2, e3]
    abel
  · ext a b
    have := congrFun (congrFun hh a) b
    simp only [map_apply] at this
    rw [map_apply, Matrix.add_apply, map_add, z2, add_zero, this]

open Matrix in
theorem UpperTheory.V.Alg.hh_small :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ →
      (∀ h' : Matrix ι ι R', Φ.HH h' → ∃ h : Matrix ι ι R, Φ.HH h ∧ h.map p = h') ∧
      (∀ h₁ h₂ : Matrix ι ι R, Φ.HH h₁ → Φ.HH h₂ → h₁.map p = h₂.map p → h₂ - h₁ ∈ Φ.g R) ∧
      ∀ h Y : Matrix ι ι R, Φ.HH h → Y ∈ Φ.g R → Y.map p = 0 → Φ.HH (h + Y) := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 R _ _ _ R' _ _ _ p hp hs
  refine ⟨?_, ?_, ?_⟩
  · classical
    rintro h' ⟨a1, a2, a3⟩
    choose s hs' using hp
    obtain ⟨h0, b1, b2⟩ : ∃ h0 : Matrix ι ι R, h0.map p = h' ∧ ∀ a b, Φ.blk a ≠ Φ.blk b → h0 a b = 0 := by
      refine ⟨Matrix.of fun a b => if Φ.blk a = Φ.blk b then s (h' a b) else 0, ?_, fun a b e => by simp [e]⟩
      ext a b
      by_cases e : Φ.blk a = Φ.blk b
      · simp [e, hs']
      · simp [e, a2 a b e]
    have b3 : h0.map (res O R) = 1 := by
      rw [← a3, ← b1]
      ext a b
      simp [res_map]
    have jp : (Φ.JR R).map p = Φ.JR R' := by
      ext a b
      simp [FormData.JR]
    have jb : ∀ a b, Φ.JR R a b ≠ 0 → Φ.blk b = Φ.σ (Φ.blk a) := fun a b e =>
      Φ.hblk a b fun n => e (by simp [FormData.JR, n])
    obtain ⟨K, hK⟩ : ∃ K : Matrix ι ι R, Φ.JR R * K = 1 :=
      (Φ.unit.map (algebraMap O R).mapMatrix).exists_right_inv
    obtain ⟨u, hu⟩ : ∃ u : R, 2 * u = 1 := by
      have := (h2.map (algebraMap O R)).exists_right_inv
      rwa [map_ofNat] at this
    obtain ⟨ε, hε, hε2⟩ : ∃ ε : R, (Φ.JR R)ᵀ = ε • Φ.JR R ∧ ε * ε = 1 := by
      rcases Φ.sym with e | e
      · refine ⟨1, ?_, by simp⟩
        ext a b
        have := congrFun (congrFun e a) b
        simp only [transpose_apply] at this
        simp [FormData.JR, this]
      · refine ⟨-1, ?_, by simp⟩
        ext a b
        have := congrFun (congrFun e a) b
        simp only [transpose_apply] at this
        simp [FormData.JR, this]
    set E := h0ᵀ * Φ.JR R * h0 - Φ.JR R with hE
    have E1 : E.map p = 0 := by
      rw [hE, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, transpose_map, b1, jp, a1, sub_self]
    have E2 : Eᵀ = ε • E := by
      rw [hE, transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hε, smul_sub]
      simp [mul_assoc]
    have E3 : ∀ a b, Φ.blk b ≠ Φ.σ (Φ.blk a) → E a b = 0 := fun a b e => by
      have : Φ.JR R a b = 0 := by_contra fun n => e (jb a b n)
      rw [hE, Matrix.sub_apply, this, sub_zero]
      simp only [mul_apply, transpose_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      by_cases e1 : Φ.blk d = Φ.blk a
      · by_cases e2 : Φ.blk c = Φ.blk b
        · have : Φ.JR R d c = 0 := by_contra fun n => e (by rw [← e2, ← e1]; exact jb d c n)
          simp [this]
        · simp [b2 _ _ e2]
      · simp [b2 _ _ e1]
    set Z0 : Matrix ι ι R := K * ((-u) • E) with hZ0
    have Z1 : Φ.JR R * Z0 = (-u) • E := by rw [hZ0, ← mul_assoc, hK, one_mul]
    have Z2 : ∀ a b, p (Z0 a b) = 0 := fun a b => by
      rw [hZ0, mul_apply, map_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      have : p (E c b) = 0 := congrFun (congrFun E1 c) b
      simp [this]
    let Z : Matrix ι ι R := Matrix.of fun a b => if Φ.blk a = Φ.blk b then Z0 a b else 0
    have Z3 : Z.map p = 0 := by
      ext a b
      by_cases e : Φ.blk a = Φ.blk b <;> simp [Z, e, Z2]
    have Z4 : Φ.JR R * Z = (-u) • E := by
      ext a b
      by_cases e : Φ.blk b = Φ.σ (Φ.blk a)
      · rw [← Z1, mul_apply, mul_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases n : Φ.JR R a c = 0
        · simp [n]
        · have : Φ.blk c = Φ.blk b := by rw [e]; exact jb a c n
          simp [Z, this]
      · rw [Matrix.smul_apply, E3 a b e, smul_zero, mul_apply]
        refine Finset.sum_eq_zero fun c _ => ?_
        by_cases n : Φ.JR R a c = 0
        · simp [n]
        · have : ¬ Φ.blk c = Φ.blk b := fun m => e (by rw [← m]; exact jb a c n)
          simp [Z, this]
    have Z5 : Zᵀ * Φ.JR R = (-u) • E := by
      have := congrArg (fun M => ε • Mᵀ) Z4
      simp only [transpose_mul, transpose_smul, hε, E2, Matrix.mul_smul, smul_smul] at this
      rw [hε2, one_smul, mul_left_comm, hε2, mul_one] at this
      exact this
    obtain ⟨c1, c2⟩ := expand_small p hs (Φ.JR R) h0 Z b3 Z3
    refine ⟨h0 + Z, ⟨?_, fun a b e => by simp [Z, e, b2 a b e], c2⟩, ?_⟩
    · rw [c1, Z4, Z5, ← add_smul, show -u + -u = -1 by rw [← hu]; ring, neg_one_smul, hE]
      abel
    · rw [Matrix.map_add _ (map_add p), b1, Z3, add_zero]
  · rintro h₁ h₂ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ e
    have hZ : (h₂ - h₁).map p = 0 := by rw [Matrix.map_sub _ (map_sub p), e, sub_self]
    obtain ⟨c1, -⟩ := expand_small p hs (Φ.JR R) h₁ (h₂ - h₁) a3 hZ
    rw [add_sub_cancel, a1, b1, left_eq_add] at c1
    exact ⟨c1, fun a b n => by simp [a2 a b n, b2 a b n]⟩
  · rintro h Y ⟨a1, a2, a3⟩ ⟨b1, b2⟩ e
    obtain ⟨c1, c2⟩ := expand_small p hs (Φ.JR R) h Y a3 e
    exact ⟨by rw [c1, a1, b1, add_zero], fun a b n => by simp [a2 a b n, b2 a b n], c2⟩
