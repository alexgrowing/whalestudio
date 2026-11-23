import Mathlib

noncomputable section

open scoped Matrix

namespace GlobalTheory.HermEichler

variable {R : Type} [CommRing R] (c : R →+* R) {n m : ℕ} (J : Matrix (Fin n) (Fin n) R)

def hf (v w : Fin n → R) : R := v ⬝ᵥ (J *ᵥ fun i => c (w i))

def eich (x : Fin n → R) (ι : Matrix (Fin n) (Fin m) R) (a : R) (v : Fin m → R) : Matrix (Fin n) (Fin n) R :=
  1 + Matrix.vecMulVec ((a + c a) • x + ι *ᵥ v) (J *ᵥ fun i => c (x i)) -
    Matrix.vecMulVec x (J *ᵥ fun i => c ((a • x + ι *ᵥ v) i))

theorem eich_mulVec (x : Fin n → R) (ι : Matrix (Fin n) (Fin m) R) (a : R) (v : Fin m → R) (t : Fin n → R) :
    eich c J x ι a v *ᵥ t = t + hf c J t x • ((a + c a) • x + ι *ᵥ v) - hf c J t (a • x + ι *ᵥ v) • x := by
  ext i
  simp only [eich, hf, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.add_apply,
    Matrix.vecMulVec_mulVec, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
  rw [dotProduct_comm t, dotProduct_comm t]
  ring

theorem hf_add_left (v v' w : Fin n → R) : hf c J (v + v') w = hf c J v w + hf c J v' w := by
  simp [hf, add_dotProduct]

theorem hf_smul_left (a : R) (v w : Fin n → R) : hf c J (a • v) w = a * hf c J v w := by
  simp [hf, smul_dotProduct]

theorem hf_sub_left (v v' w : Fin n → R) : hf c J (v - v') w = hf c J v w - hf c J v' w := by
  simp [hf, sub_dotProduct]

theorem hf_neg_left (v w : Fin n → R) : hf c J (-v) w = -hf c J v w := by
  simp [hf]

theorem hf_add_right (v w w' : Fin n → R) : hf c J v (w + w') = hf c J v w + hf c J v w' := by
  have : (fun i => c ((w + w') i)) = (fun i => c (w i)) + (fun i => c (w' i)) := by
    funext i; simp
  rw [hf, this, Matrix.mulVec_add, dotProduct_add]; rfl

theorem hf_smul_right (a : R) (v w : Fin n → R) : hf c J v (a • w) = c a * hf c J v w := by
  have : (fun i => c ((a • w) i)) = c a • (fun i => c (w i)) := by
    funext i; simp
  rw [hf, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]; rfl

theorem hf_sub_right (v w w' : Fin n → R) : hf c J v (w - w') = hf c J v w - hf c J v w' := by
  have : (fun i => c ((w - w') i)) = (fun i => c (w i)) - (fun i => c (w' i)) := by
    funext i; simp
  rw [hf, this, Matrix.mulVec_sub, dotProduct_sub]; rfl

theorem hf_neg_right (v w : Fin n → R) : hf c J v (-w) = -hf c J v w := by
  have : (fun i => c ((-w) i)) = -(fun i => c (w i)) := by
    funext i; simp
  rw [hf, this, Matrix.mulVec_neg, dotProduct_neg]; rfl

theorem hf_herm (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j) (v w : Fin n → R) :
    hf c J w v = c (hf c J v w) := by
  simp only [hf, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

end GlobalTheory.HermEichler

namespace GlobalTheory.HermEichler

variable {R : Type} [CommRing R] (c : R →+* R) {n m : ℕ} (J : Matrix (Fin n) (Fin n) R)

theorem hf_single (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    hf c M (Pi.single i 1) (Pi.single j 1) = M i j := by
  have : (fun k => c ((Pi.single j (1 : R) : Fin n → R) k)) = Pi.single j 1 := by
    funext k; by_cases h : k = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [hf, this, Matrix.mulVec_single_one, single_dotProduct, one_mul]; rfl

theorem hf_mulVec_mulVec (A : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) :
    hf c J (A *ᵥ u) (A *ᵥ v) = hf c (Aᵀ * J * A.map c) u v := by
  have h : (fun i => c ((A *ᵥ v) i)) = A.map c *ᵥ fun i => c (v i) := funext fun i => RingHom.map_mulVec _ _ _ _
  simp only [hf, h, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

variable {c J}

theorem eich_mul (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j) {x : Fin n → R} {ι : Matrix (Fin n) (Fin m) R}
    (hxx : hf c J x x = 0) (hιx : ∀ z, hf c J (ι *ᵥ z) x = 0) (a₁ a₂ : R) (v₁ v₂ : Fin m → R) :
    eich c J x ι a₁ v₁ * eich c J x ι a₂ v₂ = eich c J x ι (a₁ + a₂ - hf c J (ι *ᵥ v₂) (ι *ᵥ v₁)) (v₁ + v₂) := by
  have hxι : ∀ z, hf c J x (ι *ᵥ z) = 0 := fun z => by rw [hf_herm c J hc hJ, hιx, map_zero]
  refine Matrix.ext_of_mulVec_single fun k => ?_
  rw [← Matrix.mulVec_mulVec]
  generalize (Pi.single k (1 : R) : Fin n → R) = t
  simp only [eich_mulVec, hf_add_left, hf_sub_left, hf_smul_left, hf_add_right, hf_sub_right, hf_smul_right, hxx, hιx, hxι,
    Matrix.mulVec_add, map_add, map_sub, hc]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem eich_zero (x : Fin n → R) (ι : Matrix (Fin n) (Fin m) R) : eich c J x ι 0 0 = 1 := by
  have h0 : (fun _ : Fin n => (0 : R)) = 0 := rfl
  simp [eich, h0]

theorem eich_unitary (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j) {x : Fin n → R} {ι : Matrix (Fin n) (Fin m) R}
    (hxx : hf c J x x = 0) (hιx : ∀ z, hf c J (ι *ᵥ z) x = 0) {a : R} {v : Fin m → R}
    (ha : a + c a + hf c J (ι *ᵥ v) (ι *ᵥ v) = 0) :
    (eich c J x ι a v)ᵀ * J * (eich c J x ι a v).map c = J := by
  have hxι : ∀ z, hf c J x (ι *ᵥ z) = 0 := fun z => by rw [hf_herm c J hc hJ, hιx, map_zero]
  refine Matrix.ext fun i j => ?_
  rw [← hf_single c ((eich c J x ι a v)ᵀ * J * (eich c J x ι a v).map c) i j, ← hf_mulVec_mulVec, ← hf_single c J i j]
  generalize (Pi.single i (1 : R) : Fin n → R) = s
  generalize (Pi.single j (1 : R) : Fin n → R) = t
  have h1 : hf c J x t = c (hf c J t x) := hf_herm c J hc hJ t x
  have h2 : hf c J (ι *ᵥ v) t = c (hf c J t (ι *ᵥ v)) := hf_herm c J hc hJ t _
  simp only [eich_mulVec, hf_add_left, hf_sub_left, hf_smul_left, hf_add_right, hf_sub_right, hf_smul_right, hxx, hιx, hxι,
    h1, h2, map_add, map_sub, map_mul, hc]
  linear_combination (hf c J s x * c (hf c J t x)) * ha

end GlobalTheory.HermEichler

namespace GlobalTheory.HermEichler

variable {R : Type} [CommRing R] {c : R →+* R} {n m : ℕ} {J : Matrix (Fin n) (Fin n) R}

theorem hf_zero_left (w : Fin n → R) : hf c J 0 w = 0 := by simp [hf]

theorem eich_mulVec_x_eq_x (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j) {x : Fin n → R}
    {ι : Matrix (Fin n) (Fin m) R} (hxx : hf c J x x = 0) (hιx : ∀ z, hf c J (ι *ᵥ z) x = 0) (a : R) (v : Fin m → R) :
    eich c J x ι a v *ᵥ x = x := by
  have hxι : ∀ z, hf c J x (ι *ᵥ z) = 0 := fun z => by rw [hf_herm c J hc hJ, hιx, map_zero]
  rw [eich_mulVec, hf_add_right, hf_smul_right, hxx, hxι]; simp

theorem eich_mulVec_ι {x : Fin n → R} {ι : Matrix (Fin n) (Fin m) R} (hιx : ∀ z, hf c J (ι *ᵥ z) x = 0) (a : R)
    (v z : Fin m → R) : eich c J x ι a v *ᵥ (ι *ᵥ z) = ι *ᵥ z + (-hf c J (ι *ᵥ z) (ι *ᵥ v)) • x := by
  rw [eich_mulVec, hf_add_right, hf_smul_right, hιx]; simp [sub_eq_add_neg]

theorem eich_mulVec_y {x y : Fin n → R} {ι : Matrix (Fin n) (Fin m) R} (hyx : hf c J y x = 1)
    (hyι : ∀ z, hf c J y (ι *ᵥ z) = 0) (a : R) (v : Fin m → R) :
    eich c J x ι a v *ᵥ y = a • x + y + ι *ᵥ v := by
  rw [eich_mulVec, hf_add_right, hf_smul_right, hyx, hyι]
  ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem eich_mul_inv (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j) {x : Fin n → R}
    {ι : Matrix (Fin n) (Fin m) R} (hxx : hf c J x x = 0) (hιx : ∀ z, hf c J (ι *ᵥ z) x = 0) (a : R) (v : Fin m → R) :
    eich c J x ι a v * eich c J x ι (-a - hf c J (ι *ᵥ v) (ι *ᵥ v)) (-v) = 1 ∧
      eich c J x ι (-a - hf c J (ι *ᵥ v) (ι *ᵥ v)) (-v) * eich c J x ι a v = 1 := by
  rw [eich_mul hc hJ hxx hιx, eich_mul hc hJ hxx hιx]
  constructor
  · convert eich_zero (c := c) (J := J) x ι using 2
    · simp [Matrix.mulVec_neg, hf_neg_left] <;> ring
    · simp
  · convert eich_zero (c := c) (J := J) x ι using 2
    · simp [Matrix.mulVec_neg, hf_neg_right] <;> ring
    · simp

theorem con_mul (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j) {ι : Matrix (Fin n) (Fin m) R} {a₁ a₂ : R}
    {v₁ v₂ : Fin m → R} (h₁ : a₁ + c a₁ + hf c J (ι *ᵥ v₁) (ι *ᵥ v₁) = 0)
    (h₂ : a₂ + c a₂ + hf c J (ι *ᵥ v₂) (ι *ᵥ v₂) = 0) :
    (a₁ + a₂ - hf c J (ι *ᵥ v₂) (ι *ᵥ v₁)) + c (a₁ + a₂ - hf c J (ι *ᵥ v₂) (ι *ᵥ v₁)) +
      hf c J (ι *ᵥ (v₁ + v₂)) (ι *ᵥ (v₁ + v₂)) = 0 := by
  have h := hf_herm c J hc hJ (ι *ᵥ v₂) (ι *ᵥ v₁)
  simp only [Matrix.mulVec_add, hf_add_left, hf_add_right, map_add, map_sub]
  rw [← h]
  linear_combination h₁ + h₂

theorem eich_map {S : Type} [CommRing S] (f : R →+* S) (c' : S →+* S) (hf' : ∀ r, f (c r) = c' (f r))
    (x : Fin n → R) (ι : Matrix (Fin n) (Fin m) R) (a : R) (v : Fin m → R) :
    (eich c J x ι a v).map f = eich c' (J.map f) (fun i => f (x i)) (ι.map f) (f a) (fun i => f (v i)) := by
  ext i j
  simp only [eich, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    Matrix.mulVec, dotProduct, map_add, map_sub, map_mul, map_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf']
  split_ifs <;> simp

end GlobalTheory.HermEichler

namespace GlobalTheory.HermEichler

theorem decomp {K : Type} [Field K] {c : K →+* K} {n m : ℕ} {J : Matrix (Fin n) (Fin n) K} {x y : Fin n → K}
    {ι : Matrix (Fin n) (Fin m) K} (hn : m + 2 = n) (hxy : hf c J x y = 1) (hyx : hf c J y x = 1) (hxx : hf c J x x = 0)
    (hyy : hf c J y y = 0) (hιx : ∀ z, hf c J (ι *ᵥ z) x = 0) (hιy : ∀ z, hf c J (ι *ᵥ z) y = 0)
    (hinj : Function.Injective ι.mulVec) (t : Fin n → K) : ∃ (s r : K) (z : Fin m → K), t = s • x + ι *ᵥ z + r • y := by
  let L : (Fin m → K) × (K × K) →ₗ[K] (Fin n → K) :=
    LinearMap.coprod (Matrix.mulVecLin ι) (LinearMap.coprod ((LinearMap.id : K →ₗ[K] K).smulRight x)
      ((LinearMap.id : K →ₗ[K] K).smulRight y))
  have hL : ∀ p : (Fin m → K) × (K × K), L p = ι *ᵥ p.1 + (p.2.1 • x + p.2.2 • y) := fun p => by
    simp [L]
  have hinjL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨z, s, r⟩ h
    rw [hL] at h
    have h1 := congrArg (fun w => hf c J w y) h
    have h2 := congrArg (fun w => hf c J w x) h
    simp only [hf_add_left, hf_smul_left, hιx, hιy, hxy, hyx, hxx, hyy, hf_zero_left] at h1 h2
    have hs : s = 0 := by linear_combination h1
    have hr : r = 0 := by linear_combination h2
    subst hs hr
    have hz : ι *ᵥ z = ι *ᵥ 0 := by simpa using h
    rw [hinj hz]; rfl
  have hfr : Module.finrank K ((Fin m → K) × (K × K)) = Module.finrank K (Fin n → K) := by
    simp [Module.finrank_prod, ← hn]
  obtain ⟨⟨z, s, r⟩, h⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinjL t
  refine ⟨s, r, z, ?_⟩
  rw [← h, hL]; abel

end GlobalTheory.HermEichler
