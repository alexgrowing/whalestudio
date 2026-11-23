import Mathlib

namespace GlobalTheory.GramCount

variable {A : Type} [CommRing A]

def ip (c : A →+* A) {n : ℕ} (x y : Fin n → A) : A := ∑ i, x i * c (y i)

def Prim (c : A →+* A) {m n : ℕ} (x : Fin m → Fin n → A) : Prop :=
  ∃ y : Fin m → Fin n → A, ∀ a b, ip c (x a) (y b) = if a = b then 1 else 0

def sols (c : A →+* A) {m : ℕ} (n : ℕ) (G : Matrix (Fin m) (Fin m) A) :
    Set (Fin m → Fin n → A) :=
  {x | Prim c x ∧ ∀ a b, ip c (x b) (x a) = G a b}

variable (c : A →+* A) {n : ℕ}

theorem ip_add_left (x x' y : Fin n → A) : ip c (x + x') y = ip c x y + ip c x' y := by
  simp only [ip, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem ip_add_right (x y y' : Fin n → A) : ip c x (y + y') = ip c x y + ip c x y' := by
  simp only [ip, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem ip_sub_left (x x' y : Fin n → A) : ip c (x - x') y = ip c x y - ip c x' y := by
  simp only [ip, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem ip_zero_left (y : Fin n → A) : ip c 0 y = 0 := by
  simp [ip]

theorem ip_zero_right (x : Fin n → A) : ip c x 0 = 0 := by
  simp [ip]

theorem ip_smul_left (a : A) (x y : Fin n → A) : ip c (a • x) y = a * ip c x y := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem ip_smul_right (a : A) (x y : Fin n → A) : ip c x (a • y) = c a * ip c x y := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem ip_sum_left {ι : Type} (s : Finset ι) (x : ι → Fin n → A) (y : Fin n → A) :
    ip c (∑ a ∈ s, x a) y = ∑ a ∈ s, ip c (x a) y := by
  unfold ip
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem ip_sum_right {ι : Type} (s : Finset ι) (x : Fin n → A) (y : ι → Fin n → A) :
    ip c x (∑ a ∈ s, y a) = ∑ a ∈ s, ip c x (y a) := by
  unfold ip
  simp only [Finset.sum_apply, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem cj_ip (hc : ∀ u, c (c u) = u) (x y : Fin n → A) : c (ip c x y) = ip c y x := by
  unfold ip
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hc, mul_comm]

theorem map_ip {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) (x y : Fin n → A) :
    φ (ip c x y) = ip c' (fun i => φ (x i)) (fun i => φ (y i)) := by
  unfold ip
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hφ]

theorem prim_of_isUnit_det (hc : ∀ u, c (c u) = u) {m : ℕ} (x y : Fin m → Fin n → A)
    (h : IsUnit (Matrix.of fun a b => ip c (x a) (y b)).det) : Prim c x := by

  unfold Prim
  refine ⟨fun b => ∑ k, c ((Matrix.of fun a b => ip c (x a) (y b))⁻¹ k b) • y k,
    fun a b => ?_⟩
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv _ h) a) b
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  simp only [Matrix.of_apply] at h1
  rw [ip_sum_right]
  simp only [ip_smul_right, hc]
  rw [← h1]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem prim_of_sub_mem (hc : ∀ u, c (c u) = u) (I : Ideal A) (hI : ∀ u ∈ I, IsUnit (1 + u))
    {m : ℕ} (x y : Fin m → Fin n → A)
    (h : ∀ a b, ip c (x a) (y b) - (if a = b then 1 else 0) ∈ I) : Prim c x := by

  apply prim_of_isUnit_det c hc x y
  have hone : (Ideal.Quotient.mk I).mapMatrix (Matrix.of fun a b => ip c (x a) (y b)) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
    have hab := h a b
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at hab
    rw [hab]
    split_ifs <;> simp
  have key : (Matrix.of fun a b => ip c (x a) (y b)).det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, hone,
      Matrix.det_one, sub_self]
  simpa using hI _ key

theorem Prim.map {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) {m : ℕ} {x : Fin m → Fin n → A} (h : Prim c x) :
    Prim c' (fun a i => φ (x a i)) := by
  unfold Prim at h ⊢
  obtain ⟨y, hy⟩ := h
  refine ⟨fun b i => φ (y b i), fun a b => ?_⟩
  show ip c' (fun i => φ (x a i)) (fun i => φ (y b i)) = _
  rw [← map_ip c c' φ hφ (x a) (y b), hy a b]
  split_ifs <;> simp

theorem prim_of_map (hc : ∀ u, c (c u) = u) {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) (hs : Function.Surjective φ)
    (hk : ∀ u, φ u = 0 → IsUnit (1 + u)) {m : ℕ} {x : Fin m → Fin n → A}
    (h : Prim c' (fun a i => φ (x a i))) : Prim c x := by

  unfold Prim at h
  obtain ⟨y', hy'⟩ := h
  choose y hy using fun b i => hs (y' b i)
  apply prim_of_sub_mem c hc (RingHom.ker φ) (fun u hu => hk u (RingHom.mem_ker.mp hu)) x y
  intro a b
  have h2 : ip c' (fun i => φ (x a i)) (y' b) = if a = b then 1 else 0 := hy' a b
  have e : (fun i => φ (y b i)) = y' b := funext (hy b)
  rw [RingHom.mem_ker, map_sub, map_ip c c' φ hφ, e, h2]
  split_ifs <;> simp

theorem Prim.eq_zero {m : ℕ} {x : Fin m → Fin n → A} (h : Prim c x) (s : Fin m → A)
    (hs : ∑ a, s a • x a = 0) : s = 0 := by

  unfold Prim at h
  obtain ⟨y, hy⟩ := h
  funext b
  have hb := congrArg (fun z => ip c z (y b)) hs
  simp only [ip_sum_left, ip_smul_left, hy, ip_zero_left] at hb
  simpa using hb

theorem exists_trace_one (hc : ∀ u, c (c u) = u) {ω : A} (hω : IsUnit (ω - c ω)) :
    ∃ θ e : A, θ + c θ = 1 ∧ IsUnit e ∧ c e = -e := by
  obtain ⟨U, hU⟩ := hω
  have h1 : (ω - c ω) * ↑U⁻¹ = 1 := by rw [← hU]; exact U.mul_inv
  have h2 : (c ω - ω) * c ↑U⁻¹ = 1 := by
    have h3 := congrArg c h1
    rwa [map_mul, map_sub, hc, map_one] at h3
  have hv : c ↑U⁻¹ = -(↑U⁻¹ : A) := by
    linear_combination (-(c ↑U⁻¹)) * h1 + (-(↑U⁻¹ : A)) * h2
  refine ⟨ω * ↑U⁻¹, ω - c ω, ?_, ⟨U, hU⟩, ?_⟩
  · rw [map_mul, hv]
    linear_combination h1
  · rw [map_sub, hc]
    ring

theorem card_fixed_sq (hc : ∀ u, c (c u) = u) {ω : A} (hω : IsUnit (ω - c ω))
    {M : Type} [AddCommGroup M] [Module A M] (σ : M →+ M) (hσ : ∀ x, σ (σ x) = x)
    (hs : ∀ (a : A) x, σ (a • x) = c a • σ x) :
    Nat.card {x : M // σ x = x} ^ 2 = Nat.card M ∧
      Nat.card {x : M // σ x = -x} ^ 2 = Nat.card M := by

  obtain ⟨U, hU⟩ := hω
  have h1 : (ω - c ω) * ↑U⁻¹ = 1 := by rw [← hU]; exact U.mul_inv
  have h2 : (c ω - ω) * c ↑U⁻¹ = 1 := by
    have h3 := congrArg c h1
    rwa [map_mul, map_sub, hc, map_one] at h3
  have hvn : c ↑U⁻¹ = -(↑U⁻¹ : A) := by
    linear_combination (-(c ↑U⁻¹)) * h1 + (-(↑U⁻¹ : A)) * h2
  obtain ⟨v, hv1, hv2⟩ : ∃ v : A, (ω - c ω) * v = 1 ∧ c v = -v := ⟨_, h1, hvn⟩
  have hu : c (ω - c ω) = -(ω - c ω) := by
    rw [map_sub, hc]
    ring
  have hg : ∀ x, σ (v • (x - σ x)) = v • (x - σ x) := by
    intro x
    rw [hs, map_sub, hσ, hv2, neg_smul, ← smul_neg, neg_sub]
  have hab : ω * v = c ω * v + 1 := by linear_combination hv1
  have hf : ∀ x, σ (x - ω • v • (x - σ x)) = x - ω • v • (x - σ x) := by
    intro x
    rw [map_sub, hs, hg, smul_smul, smul_smul, hab, add_smul, one_smul]
    abel
  have e : M ≃ {x : M // σ x = x} × {x : M // σ x = x} :=
    { toFun := fun x => (⟨x - ω • v • (x - σ x), hf x⟩, ⟨v • (x - σ x), hg x⟩)
      invFun := fun p => p.1.1 + ω • p.2.1
      left_inv := fun x => sub_add_cancel _ _
      right_inv := fun p => by
        obtain ⟨⟨f, hf0⟩, ⟨g, hg0⟩⟩ := p
        have key : v • (f + ω • g - σ (f + ω • g)) = g := by
          rw [map_add, hs, hf0, hg0, add_sub_add_left_eq_sub, ← sub_smul, smul_smul, mul_comm,
            hv1, one_smul]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show f + ω • g - ω • v • (f + ω • g - σ (f + ω • g)) = f
          rw [key, add_sub_cancel_right]
        · exact key }
  have e2 : {x : M // σ x = -x} ≃ {x : M // σ x = x} :=
    { toFun := fun x => ⟨v • x.1, by rw [hs, x.2, hv2, smul_neg, neg_smul, neg_neg]⟩
      invFun := fun y => ⟨(ω - c ω) • y.1, by rw [hs, y.2, hu, neg_smul]⟩
      left_inv := fun x => Subtype.ext (by
        show (ω - c ω) • v • x.1 = x.1
        rw [smul_smul, hv1, one_smul])
      right_inv := fun y => Subtype.ext (by
        show v • (ω - c ω) • y.1 = y.1
        rw [smul_smul, mul_comm, hv1, one_smul]) }
  have hM : Nat.card M = Nat.card {x : M // σ x = x} ^ 2 := by
    rw [Nat.card_congr e, Nat.card_prod, sq]
  exact ⟨hM.symm, by rw [Nat.card_congr e2, hM]⟩

end GlobalTheory.GramCount
