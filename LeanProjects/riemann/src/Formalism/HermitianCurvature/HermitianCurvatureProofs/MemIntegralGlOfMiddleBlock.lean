import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x3

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)

section Blocks

variable {A : Type} {r k : ℕ}

@[simp] theorem block11_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b11 (x.map f) = (b11 x).map f := rfl

@[simp] theorem block12_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b12 (x.map f) = (b12 x).map f := rfl

@[simp] theorem block13_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b13 (x.map f) = (b13 x).map f := rfl

@[simp] theorem block21_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b21 (x.map f) = (b21 x).map f := rfl

@[simp] theorem block22_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b22 (x.map f) = (b22 x).map f := rfl

@[simp] theorem block23_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b23 (x.map f) = (b23 x).map f := rfl

@[simp] theorem block31_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b31 (x.map f) = (b31 x).map f := rfl

@[simp] theorem block32_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b32 (x.map f) = (b32 x).map f := rfl

@[simp] theorem block33_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b33 (x.map f) = (b33 x).map f := rfl

variable [CommRing A]

theorem block11_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b11 (x * y) = b11 x * b11 y + b12 x * b21 y + b13 x * b31 y := by
  ext i j
  simp [b11, b11, b12, b13, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block12_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b12 (x * y) = b11 x * b12 y + b12 x * b22 y + b13 x * b32 y := by
  ext i j
  simp [b12, b11, b12, b13, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block13_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b13 (x * y) = b11 x * b13 y + b12 x * b23 y + b13 x * b33 y := by
  ext i j
  simp [b13, b11, b12, b13, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block21_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b21 (x * y) = b21 x * b11 y + b22 x * b21 y + b23 x * b31 y := by
  ext i j
  simp [b21, b21, b22, b23, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block22_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b22 (x * y) = b21 x * b12 y + b22 x * b22 y + b23 x * b32 y := by
  ext i j
  simp [b22, b21, b22, b23, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block23_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b23 (x * y) = b21 x * b13 y + b22 x * b23 y + b23 x * b33 y := by
  ext i j
  simp [b23, b21, b22, b23, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block31_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x * y) = b31 x * b11 y + b32 x * b21 y + b33 x * b31 y := by
  ext i j
  simp [b31, b31, b32, b33, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block32_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b32 (x * y) = b31 x * b12 y + b32 x * b22 y + b33 x * b32 y := by
  ext i j
  simp [b32, b31, b32, b33, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block33_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b33 (x * y) = b31 x * b13 y + b32 x * b23 y + b33 x * b33 y := by
  ext i j
  simp [b33, b31, b32, b33, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

@[simp] theorem block11_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b11 (hEmb r h) = 1 := by
  ext i j
  simp [b11, hEmb, Matrix.one_apply]

@[simp] theorem block12_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b12 (hEmb r h) = 0 := by
  ext i j
  simp [b12, hEmb]

@[simp] theorem block13_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b13 (hEmb r h) = 0 := by
  ext i j
  simp [b13, hEmb]

@[simp] theorem block21_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b21 (hEmb r h) = 0 := by
  ext i j
  simp [b21, hEmb]

@[simp] theorem block22_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b22 (hEmb r h) = midEmb h := by
  ext i j
  simp [b22, hEmb]

@[simp] theorem block23_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b23 (hEmb r h) = 0 := by
  ext i j
  simp [b23, hEmb]

@[simp] theorem block31_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b31 (hEmb r h) = 0 := by
  ext i j
  simp [b31, hEmb]

@[simp] theorem block32_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b32 (hEmb r h) = 0 := by
  ext i j
  simp [b32, hEmb]

@[simp] theorem block33_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b33 (hEmb r h) = 1 := by
  ext i j
  simp [b33, hEmb, Matrix.one_apply]

@[simp] theorem block11_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b11 (x * hEmb r h) = b11 x := by
  simp [block11_mul]

@[simp] theorem block12_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b12 (x * hEmb r h) = b12 x * midEmb h := by
  simp [block12_mul]

@[simp] theorem block13_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b13 (x * hEmb r h) = b13 x := by
  simp [block13_mul]

@[simp] theorem block21_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b21 (x * hEmb r h) = b21 x := by
  simp [block21_mul]

@[simp] theorem block22_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b22 (x * hEmb r h) = b22 x * midEmb h := by
  simp [block22_mul]

@[simp] theorem block23_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b23 (x * hEmb r h) = b23 x := by
  simp [block23_mul]

@[simp] theorem block31_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b31 (x * hEmb r h) = b31 x := by
  simp [block31_mul]

@[simp] theorem block32_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b32 (x * hEmb r h) = b32 x * midEmb h := by
  simp [block32_mul]

@[simp] theorem block33_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b33 (x * hEmb r h) = b33 x := by
  simp [block33_mul]

@[simp] theorem block11_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b11 (hEmb r h * x) = b11 x := by
  simp [block11_mul]

@[simp] theorem block12_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b12 (hEmb r h * x) = b12 x := by
  simp [block12_mul]

@[simp] theorem block13_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b13 (hEmb r h * x) = b13 x := by
  simp [block13_mul]

@[simp] theorem block21_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b21 (hEmb r h * x) = midEmb h * b21 x := by
  simp [block21_mul]

@[simp] theorem block22_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b22 (hEmb r h * x) = midEmb h * b22 x := by
  simp [block22_mul]

@[simp] theorem block23_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b23 (hEmb r h * x) = midEmb h * b23 x := by
  simp [block23_mul]

@[simp] theorem block31_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b31 (hEmb r h * x) = b31 x := by
  simp [block31_mul]

@[simp] theorem block32_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b32 (hEmb r h * x) = b32 x := by
  simp [block32_mul]

@[simp] theorem block33_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b33 (hEmb r h * x) = b33 x := by
  simp [block33_mul]

end Blocks

section Alg

variable {A : Type} [CommRing A] {r k : ℕ}

theorem midEmb_mul (a b : Matrix (Fin k) (Fin k) A) : midEmb (a * b) = midEmb a * midEmb b := by
  simp [midEmb, Matrix.fromBlocks_multiply]

theorem midEmb_one : midEmb (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [midEmb]

theorem midEmb_inj {a b : Matrix (Fin k) (Fin k) A} (h : midEmb a = midEmb b) : a = b :=
  (Matrix.fromBlocks_inj.1 h).1

theorem hEmb_mul (a b : Matrix (Fin k) (Fin k) A) : hEmb r (a * b) = hEmb r a * hEmb r b := by
  simp [hEmb, Matrix.fromBlocks_multiply, midEmb_mul]

theorem hEmb_one : hEmb r (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [hEmb, midEmb_one]

theorem det_hEmb (h : Matrix (Fin k) (Fin k) A) : (hEmb r h).det = h.det := by
  simp [hEmb, midEmb, Matrix.det_fromBlocks_zero₂₁]

theorem hEmb_map {B : Type} [CommRing B] (f : A →+* B) (h : Matrix (Fin k) (Fin k) A) :
    (hEmb r h).map f = hEmb r (h.map f) := by
  simp [hEmb, midEmb, Matrix.fromBlocks_map]

theorem det_of_isN {n : Matrix (Idx r k) (Idx r k) A} (hn : IsN n) : n.det = 1 := by
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  have e : n = Matrix.fromBlocks (b11 n) (n.toBlocks₁₂) 0 (Matrix.fromBlocks 1 (b23 n) 0 (b33 n)) := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j
    · rfl
    · rfl
    · rfl
    · exact congrFun (congrFun h21 i) j
    · exact congrFun (congrFun h22 i) j
    · rfl
    · exact congrFun (congrFun h31 i) j
    · exact congrFun (congrFun h32 i) j
    · rfl
  rw [e, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    Formalism.DoubleCosetMeasures.isUpUni_det A h11, Formalism.DoubleCosetMeasures.isUpUni_det A h33]
  simp

theorem isUpUni_map {B : Type} [CommRing B] (f : A →+* B) {n : ℕ} {x : Matrix (Fin n) (Fin n) A}
    (hx : IsUpUni x) : IsUpUni (x.map f) :=
  ⟨fun i j hij => by simp [hx.1 hij], fun a => by simp [hx.2 a]⟩

theorem isUpUni_of_map {B : Type} [CommRing B] (f : A →+* B) (hf : Function.Injective f) {n : ℕ}
    {x : Matrix (Fin n) (Fin n) A} (hx : IsUpUni (x.map f)) : IsUpUni x :=
  ⟨fun i j hij => hf (by simpa using hx.1 hij), fun a => hf (by simpa using hx.2 a)⟩

theorem isN_map {B : Type} [CommRing B] (f : A →+* B) {n : Matrix (Idx r k) (Idx r k) A}
    (hn : IsN n) : IsN (n.map f) := by
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  refine ⟨isUpUni_map f h11, isUpUni_map f h33, ?_, ?_, ?_, ?_⟩
  · rw [block22_map, h22]; simp
  · rw [block21_map, h21]; simp
  · rw [block31_map, h31]; simp
  · rw [block32_map, h32]; simp

theorem isN_of_map {B : Type} [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    {n : Matrix (Idx r k) (Idx r k) A} (hn : IsN (n.map f)) : IsN n := by
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  refine ⟨isUpUni_of_map f hf h11, isUpUni_of_map f hf h33, ?_, ?_, ?_, ?_⟩
  · apply Matrix.map_injective hf; show (b22 n).map f = _; rw [← block22_map, h22]; simp
  · apply Matrix.map_injective hf; show (b21 n).map f = _; rw [← block21_map, h21]; simp
  · apply Matrix.map_injective hf; show (b31 n).map f = _; rw [← block31_map, h31]; simp
  · apply Matrix.map_injective hf; show (b32 n).map f = _; rw [← block32_map, h32]; simp

theorem isN_conj {a b : Matrix (Fin k) (Fin k) A} (hab : a * b = 1)
    {n : Matrix (Idx r k) (Idx r k) A} (hn : IsN n) : IsN (hEmb r a * n * hEmb r b) := by
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  refine ⟨by simpa using h11, by simpa using h33, ?_, ?_, ?_, ?_⟩
  · simp [h22, ← midEmb_mul, hab, midEmb_one]
  · simp [h21]
  · simp [h31]
  · simp [h32]

theorem isNU_hEmb_mul {u : Matrix (Fin k) (Fin k) A} (hu : IsUpUni u)
    {n : Matrix (Idx r k) (Idx r k) A} (hn : IsN n) : IsNU (hEmb r u * n) := by
  have hdet : IsUnit u.det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det A hu]; exact isUnit_one
  refine ⟨hEmb r u * n * hEmb r u⁻¹, hEmb r u, isN_conj (Matrix.mul_nonsing_inv u hdet) hn,
    ⟨u, hu, rfl⟩, ?_⟩
  rw [mul_assoc, ← hEmb_mul, Matrix.nonsing_inv_mul u hdet, hEmb_one, mul_one]

end Alg

section Integral

variable (o : Type) [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]

theorem inGLo_mul {ι : Type} [Fintype ι] [DecidableEq ι] {x y : Matrix ι ι k0} (hx : InGLo o x)
    (hy : InGLo o y) : InGLo o (x * y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a * b, by rw [Matrix.det_mul]; exact ha.mul hb, by rw [Matrix.map_mul]⟩

theorem inGLo_inv {ι : Type} [Fintype ι] [DecidableEq ι] {x : Matrix ι ι k0} (hx : InGLo o x) :
    InGLo o x⁻¹ := by
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a⁻¹, Matrix.isUnit_nonsing_inv_det a ha, ?_⟩
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv a ha]
  simp

theorem inGLo_hEmb {r k : ℕ} {h : Matrix (Fin k) (Fin k) k0} (hh : InGLo o h) :
    InGLo o (hEmb r h) := by
  obtain ⟨a, ha, rfl⟩ := hh
  exact ⟨hEmb r a, by rw [det_hEmb]; exact ha, hEmb_map _ _⟩

variable [IsFractionRing o k0]

theorem mem_integral_gl_of_middle_block {r k : ℕ} {x : Matrix (Idx r k) (Idx r k) k0} {h : Matrix (Fin k) (Fin k) k0}
    (hx : InGLo o x) (h22 : b22 x = midEmb h) (hdet : x.det = h.det) : InGLo o h := by
  obtain ⟨y, hy, rfl⟩ := hx
  have e : ((b22 y).toBlocks₁₁).map (algebraMap o k0) = h := by
    ext i j
    have := congrFun (congrFun h22 (Sum.inl i)) (Sum.inl j)
    simpa [midEmb, Matrix.toBlocks₁₁] using this
  refine ⟨(b22 y).toBlocks₁₁, ?_, e⟩
  have h2 : algebraMap o k0 ((b22 y).toBlocks₁₁).det = algebraMap o k0 y.det := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, e, hdet]
  rw [IsFractionRing.injective o k0 h2]
  exact hy

theorem inGLo_nh {r k : ℕ} {n : Matrix (Idx r k) (Idx r k) k0} {h : Matrix (Fin k) (Fin k) k0}
    (hn : IsN n) (hh : IsUnit h.det) : InGLo o (n * hEmb r h) ↔ InGLo o n ∧ InGLo o h := by
  constructor
  · intro hx
    have h1 : InGLo o h := mem_integral_gl_of_middle_block o hx (by simp [hn.2.2.1])
      (by rw [Matrix.det_mul, det_of_isN hn, det_hEmb, one_mul])
    refine ⟨?_, h1⟩
    have h2 := inGLo_mul o hx (inGLo_inv o (inGLo_hEmb o (r := r) h1))
    rwa [Matrix.mul_nonsing_inv_cancel_right _ _ (by rw [det_hEmb]; exact hh)] at h2
  · rintro ⟨h1, h2⟩
    exact inGLo_mul o h1 (inGLo_hEmb o h2)

theorem inGLo_hn {r k : ℕ} {n : Matrix (Idx r k) (Idx r k) k0} {h : Matrix (Fin k) (Fin k) k0}
    (hn : IsN n) (hh : IsUnit h.det) : InGLo o (hEmb r h * n) ↔ InGLo o n ∧ InGLo o h := by
  constructor
  · intro hx
    have h1 : InGLo o h := mem_integral_gl_of_middle_block o hx (by simp [hn.2.2.1])
      (by rw [Matrix.det_mul, det_of_isN hn, det_hEmb, mul_one])
    refine ⟨?_, h1⟩
    have h2 := inGLo_mul o (inGLo_inv o (inGLo_hEmb o (r := r) h1)) hx
    rwa [Matrix.nonsing_inv_mul_cancel_left _ _ (by rw [det_hEmb]; exact hh)] at h2
  · rintro ⟨h1, h2⟩
    exact inGLo_mul o (inGLo_hEmb o h2) h1

variable [IsLocalRing o]

theorem kpp_nh {r k : ℕ} {n : Matrix (Idx r k) (Idx r k) k0} {h : Matrix (Fin k) (Fin k) k0}
    (hn : IsN n) (hh : IsUnit h.det) :
    (∃ y : Matrix (Idx r k) (Idx r k) o, KppO y ∧ y.map (algebraMap o k0) = n * hEmb r h) ↔
      InGLo o n ∧ ∃ y : Matrix (Fin k) (Fin k) o, IsUnit y.det ∧
        IsUpUni (y.map (IsLocalRing.residue o)) ∧ y.map (algebraMap o k0) = h := by
  have hinj := IsFractionRing.injective o k0
  constructor
  · rintro ⟨y, ⟨hdet, hNU⟩, hy⟩
    obtain ⟨hn', yh, hyh, rfl⟩ := (inGLo_nh o hn hh).1 ⟨y, hdet, hy⟩
    refine ⟨hn', yh, hyh, ?_, rfl⟩
    obtain ⟨yn, hyn, rfl⟩ := hn'
    have e : y = yn * hEmb r yh := by
      apply Matrix.map_injective hinj
      show y.map (algebraMap o k0) = (yn * hEmb r yh).map (algebraMap o k0)
      rw [hy, Matrix.map_mul, hEmb_map]
    subst e
    obtain ⟨n', u', hn', ⟨u, hu, rfl⟩, e⟩ := hNU
    have hN := isN_map (IsLocalRing.residue o) (isN_of_map _ hinj hn)
    have e2 := congrArg b22 e
    rw [Matrix.map_mul, hEmb_map, block22_mul_levi_embedding, block22_mul_levi_embedding, hN.2.2.1, hn'.2.2.1, one_mul,
      one_mul] at e2
    rw [midEmb_inj e2]
    exact hu
  · rintro ⟨⟨yn, hyn, rfl⟩, yh, hyh, hu, rfl⟩
    refine ⟨yn * hEmb r yh, ⟨?_, ?_⟩, ?_⟩
    · rw [Matrix.det_mul, det_hEmb]; exact hyn.mul hyh
    · rw [Matrix.map_mul, hEmb_map]
      exact ⟨_, _, isN_map (IsLocalRing.residue o) (isN_of_map _ hinj hn), ⟨_, hu, rfl⟩, rfl⟩
    · rw [Matrix.map_mul, hEmb_map]

theorem kpp_hn {r k : ℕ} {n : Matrix (Idx r k) (Idx r k) k0} {h : Matrix (Fin k) (Fin k) k0}
    (hn : IsN n) (hh : IsUnit h.det) :
    (∃ y : Matrix (Idx r k) (Idx r k) o, KppO y ∧ y.map (algebraMap o k0) = hEmb r h * n) ↔
      InGLo o n ∧ ∃ y : Matrix (Fin k) (Fin k) o, IsUnit y.det ∧
        IsUpUni (y.map (IsLocalRing.residue o)) ∧ y.map (algebraMap o k0) = h := by
  have hinj := IsFractionRing.injective o k0
  constructor
  · rintro ⟨y, ⟨hdet, hNU⟩, hy⟩
    obtain ⟨hn', yh, hyh, rfl⟩ := (inGLo_hn o hn hh).1 ⟨y, hdet, hy⟩
    refine ⟨hn', yh, hyh, ?_, rfl⟩
    obtain ⟨yn, hyn, rfl⟩ := hn'
    have e : y = hEmb r yh * yn := by
      apply Matrix.map_injective hinj
      show y.map (algebraMap o k0) = (hEmb r yh * yn).map (algebraMap o k0)
      rw [hy, Matrix.map_mul, hEmb_map]
    subst e
    obtain ⟨n', u', hn', ⟨u, hu, rfl⟩, e⟩ := hNU
    have hN := isN_map (IsLocalRing.residue o) (isN_of_map _ hinj hn)
    have e2 := congrArg b22 e
    rw [Matrix.map_mul, hEmb_map, block22_levi_embedding_mul, block22_mul_levi_embedding, hN.2.2.1, hn'.2.2.1, one_mul,
      mul_one] at e2
    rw [midEmb_inj e2]
    exact hu
  · rintro ⟨⟨yn, hyn, rfl⟩, yh, hyh, hu, rfl⟩
    refine ⟨hEmb r yh * yn, ⟨?_, ?_⟩, ?_⟩
    · rw [Matrix.det_mul, det_hEmb]; exact hyh.mul hyn
    · rw [Matrix.map_mul, hEmb_map]
      exact isNU_hEmb_mul hu (isN_map (IsLocalRing.residue o) (isN_of_map _ hinj hn))
    · rw [Matrix.map_mul, hEmb_map]

end Integral

section Counting

theorem red_surjective (o : Type) [CommRing o] [IsLocalRing o] (ι : Type) [Fintype ι]
    [DecidableEq ι] : Function.Surjective (red o ι) := by
  intro g
  choose y hy using fun i j => IsLocalRing.residue_surjective ((g : Matrix ι ι (IsLocalRing.ResidueField o)) i j)
  have hmap : (Matrix.of y).map (IsLocalRing.residue o) = g := by
    ext i j; simp [hy]
  have hdet : IsUnit (Matrix.of y).det := by
    have h1 : IsUnit (IsLocalRing.residue o (Matrix.of y).det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
      exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact isUnit_of_map_unit _ _ h1
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, ?_⟩
  apply Units.ext
  exact hmap

theorem index_mul_card {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (K : Subgroup G) (P : H → Prop) (hK : ∀ x, x ∈ K ↔ P (f x)) :
    K.index * Nat.card {h : H // P h} = Nat.card H := by
  have e : K = (K.map f).comap f := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, e⟩; rw [hK, ← e, ← hK]; exact hy
  have hmem : ∀ h, h ∈ K.map f ↔ P h := by
    intro h
    obtain ⟨x, rfl⟩ := hf h
    constructor
    · rintro ⟨y, hy, e⟩; rw [← e, ← hK]; exact hy
    · intro hp; exact ⟨x, (hK x).2 hp, rfl⟩
  have h1 : K.index = (K.map f).index :=
    (congrArg Subgroup.index e).trans (Subgroup.index_comap_of_surjective _ hf)
  rw [h1, ← Subgroup.index_mul_card (K.map f)]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun h => (hmem h).symm))

theorem card_GL_subtype {ι K : Type} [Fintype ι] [DecidableEq ι] [CommRing K]
    (P : Matrix ι ι K → Prop) (hP : ∀ x, P x → IsUnit x.det) :
    Nat.card {g : GL ι K // P g} = Nat.card {x : Matrix ι ι K // P x} := by
  refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨g.1, g.2⟩) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (Units.ext (congrArg Subtype.val h))
  · rintro ⟨x, hx⟩
    exact ⟨⟨((Matrix.isUnit_iff_isUnit_det x).2 (hP x hx)).unit, hx⟩, rfl⟩

variable {A : Type} [CommRing A] {r k : ℕ}

theorem card_prod_set (Q : Matrix (Fin k) (Fin k) A → Prop) (hQ : ∀ h, Q h → IsUnit h.det) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) A //
        ∃ n h', IsN n ∧ (∃ h, Q h ∧ h' = hEmb r h) ∧ x = n * h'} =
      Nat.card {g : GL (Fin k) A // Q g} * Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} := by
  rw [card_GL_subtype Q hQ, ← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ⟨p.2.1 * hEmb r p.1.1, p.2.1, hEmb r p.1.1, p.2.2, ⟨p.1.1, p.1.2, rfl⟩, rfl⟩) ⟨?_, ?_⟩)
  · rintro ⟨⟨g, hg⟩, ⟨n, hn⟩⟩ ⟨⟨g', hg'⟩, ⟨n', hn'⟩⟩ e
    have e1 : n * hEmb r g = n' * hEmb r g' := congrArg Subtype.val e
    have e2 := congrArg b22 e1
    rw [block22_mul_levi_embedding, block22_mul_levi_embedding, hn.2.2.1, hn'.2.2.1, one_mul, one_mul] at e2
    have e3 : g = g' := midEmb_inj e2
    subst e3
    have hu : IsUnit (hEmb r g) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_hEmb]; exact hQ g hg)
    have e4 : n = n' := hu.mul_left_injective e1
    subst e4
    rfl
  · rintro ⟨x, n, h', hn, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨⟨⟨h, hh⟩, ⟨n, hn⟩⟩, rfl⟩

theorem isUnit_det_of_isS {x : Matrix (Idx r k) (Idx r k) A} (hx : IsS x) : IsUnit x.det := by
  obtain ⟨n, h', hn, ⟨h, hh, rfl⟩, rfl⟩ := hx
  rw [Matrix.det_mul, det_of_isN hn, det_hEmb, one_mul]
  exact hh

theorem isUnit_det_of_isUpUni {u : Matrix (Fin k) (Fin k) A} (hu : IsUpUni u) : IsUnit u.det := by
  rw [Formalism.DoubleCosetMeasures.isUpUni_det A hu]; exact isUnit_one

theorem isUnit_det_of_isNU {x : Matrix (Idx r k) (Idx r k) A} (hx : IsNU x) : IsUnit x.det := by
  obtain ⟨n, h', hn, ⟨h, hh, rfl⟩, rfl⟩ := hx
  rw [Matrix.det_mul, det_of_isN hn, det_hEmb, one_mul]
  exact isUnit_det_of_isUpUni hh

theorem card_S : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsS x} =
    Nat.card (GL (Fin k) A) * Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} := by
  have h := card_prod_set (r := r) (fun h : Matrix (Fin k) (Fin k) A => IsUnit h.det) (fun _ h => h)
  have h2 : Nat.card {g : GL (Fin k) A // IsUnit (g : Matrix (Fin k) (Fin k) A).det} =
      Nat.card (GL (Fin k) A) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun g => (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  rw [h2] at h
  exact h

theorem card_NU : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsNU x} =
    Nat.card (upUniG A k) * Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} :=
  card_prod_set (r := r) (fun h : Matrix (Fin k) (Fin k) A => IsUpUni h)
    (fun _ h => isUnit_det_of_isUpUni h)

end Counting

section Levels

variable (o : Type) [CommRing o] [IsLocalRing o] {r k : ℕ} (L : Levels o r k)

theorem index_Kpp : L.Kpp.index *
    (Nat.card (upUniG (IsLocalRing.ResidueField o) k) *
      Nat.card {x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o) // IsN x}) =
    Nat.card (GL (Idx r k) (IsLocalRing.ResidueField o)) := by
  rw [← card_NU, ← card_GL_subtype _ (fun _ h => isUnit_det_of_isNU h)]
  exact index_mul_card (red o (Idx r k)) (red_surjective o _) L.Kpp _ L.mem_Kpp

theorem index_Knat : L.Knat.index *
    (Nat.card (GL (Fin k) (IsLocalRing.ResidueField o)) *
      Nat.card {x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o) // IsN x}) =
    Nat.card (GL (Idx r k) (IsLocalRing.ResidueField o)) := by
  rw [← card_S, ← card_GL_subtype _ (fun _ h => isUnit_det_of_isS h)]
  exact index_mul_card (red o (Idx r k)) (red_surjective o _) L.Knat _ L.mem_Knat

theorem index_JH : L.JH.index * Nat.card (upUniG (IsLocalRing.ResidueField o) k) =
    Nat.card (GL (Fin k) (IsLocalRing.ResidueField o)) :=
  index_mul_card (red o (Fin k)) (red_surjective o _) L.JH _ L.mem_JH

end Levels

theorem ratios (I1 I2 I3 cN volK volKpp volKnat volKH volJH volNo cG cS cGLk cUk γ : ℝ)
    (hG : 0 < cG) (h1 : I1 * (cUk * cN) = cG) (h2 : I2 * (cGLk * cN) = cG) (h3 : I3 * cUk = cGLk)
    (hS : cS = cGLk * cN) (p1 : 0 < volKpp) (p2 : 0 < volKnat) (p3 : 0 < volJH) (p4 : 0 < volNo)
    (v1 : volK = I1 * volKpp) (v2 : volK = I2 * volKnat) (v3 : volKH = I3 * volJH)
    (hγ : γ = cGLk / cUk) :
    γ * cS / cG = γ ^ 2 / I1 ∧
      volKnat / volK = cS / cG ∧
      (volKnat / (volNo * volKH) ^ 2) / (volK / (volNo * volKH) ^ 2) = cS / cG ∧
      (volKpp / volJH ^ 2) / (volK / volKH ^ 2) = γ ^ 2 / I1 ∧
      γ * (volKnat / (volNo * volKH) ^ 2) = (volKpp / volJH ^ 2) / volNo ^ 2 := by
  have hI1 : I1 ≠ 0 := by rintro rfl; simp at h1; exact hG.ne h1
  have hUk : cUk ≠ 0 := by rintro rfl; simp at h1; exact hG.ne h1
  have hN : cN ≠ 0 := by rintro rfl; simp at h1; exact hG.ne h1
  have hI2 : I2 ≠ 0 := by rintro rfl; simp at h2; exact hG.ne h2
  have hGLk : cGLk ≠ 0 := by rintro rfl; simp at h2; exact hG.ne h2
  have hI3 : I3 ≠ 0 := by rintro rfl; simp at h3; exact hGLk h3.symm
  have hγ' : γ = I3 := by rw [hγ, ← h3]; field_simp
  have h12 : I1 = I2 * I3 := by
    have : I1 * (cUk * cN) = (I2 * I3) * (cUk * cN) := by rw [h1, ← h2, ← h3]; ring
    exact mul_right_cancel₀ (mul_ne_zero hUk hN) this
  have hv : volKnat = I3 * volKpp := by
    have : I2 * volKnat = I2 * (I3 * volKpp) := by rw [← v2, v1, h12]; ring
    exact mul_left_cancel₀ hI2 this
  subst hγ' hS
  subst v3 v1 hv h12
  rw [← h2, ← h3]
  have q1 := p1.ne'
  have q3 := p3.ne'
  have q4 := p4.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp

end Formalism.FourierDecayAlt.P.S3x3

namespace Formalism.FourierDecayAlt.P

theorem typedArithmetic_statement : Formalism.FourierDecayAlt.S3.TypedArithmetic := by
  intro o _ _ _ r k L volK volKpp volKnat volKH volJH volNo p1 p2 p3 p4 v1 v2 v3 cG cS cGLk cUk γ
    hG hS hGLk hUk hγ
  refine S3x3.ratios L.Kpp.index L.Knat.index L.JH.index
    (Nat.card {x : Matrix (S3.Idx r k) (S3.Idx r k) (IsLocalRing.ResidueField o) // S3.IsN x})
    volK volKpp volKnat volKH volJH volNo cG cS cGLk cUk γ ?_ ?_ ?_ ?_ ?_ p1 p2 p3 p4 v1 v2 v3 hγ
  · rw [hG]; exact_mod_cast Nat.card_pos
  · rw [hG, hUk]; exact_mod_cast S3x3.index_Kpp o L
  · rw [hG, hGLk]; exact_mod_cast S3x3.index_Knat o L
  · rw [hGLk, hUk]; exact_mod_cast S3x3.index_JH o L
  · rw [hS, hGLk]; exact_mod_cast S3x3.card_S

theorem integralProduct_statement : Formalism.FourierDecayAlt.S3.IntegralProduct := by
  intro o _ _ _ k0 _ _ _ r k n h hn hh
  exact ⟨S3x3.inGLo_nh o hn hh, S3x3.inGLo_hn o hn hh, S3x3.kpp_nh o hn hh, S3x3.kpp_hn o hn hh⟩

end Formalism.FourierDecayAlt.P
