import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob.Inhab

variable {E : Type} [Field E] [NumberField E]

abbrev Int' (E : Type) [Field E] : Subring E := (algebraMap (𝓞 E) E).range

omit [NumberField E] in
theorem mem_int_iff (x : E) : x ∈ Int' E ↔ IsIntegral ℤ x :=
  ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

omit [NumberField E] in
theorem map_mem_int (σ : E →+* E) {x : E} (h : x ∈ Int' E) : σ x ∈ Int' E := by
  rw [mem_int_iff] at h ⊢
  exact h.map σ.toIntAlgHom

omit [NumberField E] in
theorem smul_eq (c : 𝓞 E) (x : E) : c • x = algebraMap (𝓞 E) E c * x := Algebra.smul_def c x

theorem mem_dInv_zero (x : E) : x ∈ dInv E 0 ↔ x ∈ Int' E := by
  simp only [dInv, pow_zero, FractionalIdeal.mem_one_iff]
  rfl

def std (E : Type) [Field E] : Submodule (𝓞 E) (Fin 2 → E) :=
  Submodule.span (𝓞 E) {![0, 1], ![1, 1]}

omit [NumberField E] in
theorem mem_std (v : Fin 2 → E) : v ∈ std E ↔ v 0 ∈ Int' E ∧ v 1 ∈ Int' E := by
  rw [std, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    constructor
    · exact ⟨b, by simp [smul_eq]⟩
    · exact ⟨a + b, by simp [smul_eq]⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨b - a, a, ?_⟩
    ext i
    fin_cases i <;> simp [smul_eq, ← ha, ← hb]

omit [NumberField E] in
theorem form_two (σ : E →+* E) (v w : Fin 2 → E) :
    form σ !![1, 0; 0, -1] v w = σ (w 0) * v 0 - σ (w 1) * v 1 := by
  simp [form, dotProduct, Matrix.mulVec, Fin.sum_univ_two, sub_eq_add_neg]

theorem selfDual_std (σ : E →+* E) : SelfDual σ !![1, 0; 0, -1] (std E) := by
  refine ⟨Submodule.fg_span (Set.toFinite _), fun v => ⟨fun hv w hw => ?_, fun h => ?_⟩⟩
  · rw [mem_std] at hv hw
    rw [form_two]
    exact sub_mem (mul_mem (map_mem_int σ hw.1) hv.1) (mul_mem (map_mem_int σ hw.2) hv.2)
  · have h0 := h ![1, 0] ((mem_std _).2 ⟨one_mem _, zero_mem _⟩)
    have h1 := h ![0, -1] ((mem_std _).2 ⟨zero_mem _, neg_mem (one_mem _)⟩)
    rw [form_two] at h0 h1
    exact (mem_std v).2 ⟨by simpa using h0, by simpa using h1⟩

theorem frameLat_zero {n : ℕ} (P : Matrix (Fin n) (Fin (0 + 1)) E) :
    frameLat P = Submodule.span (𝓞 E) {fun i => P i 0} := by
  apply le_antisymm
  · rw [frameLat, Submodule.span_le]
    rintro v ⟨b, a, ha, rfl⟩
    obtain rfl : b = 0 := Subsingleton.elim (α := Fin 1) _ _
    obtain ⟨c, rfl⟩ := (mem_dInv_zero a).1 ha
    exact Submodule.mem_span_singleton.2 ⟨c, by ext i; simp [smul_eq]⟩
  · rw [Submodule.span_le]
    rintro v rfl
    exact Submodule.subset_span ⟨0, 1, (mem_dInv_zero 1).2 (one_mem _), by simp⟩

theorem pairLat_std {g : ℕ} (hg : g ≠ 0) :
    pairLat (r := 0) g (!![0; 1] : Matrix (Fin 2) (Fin (0 + 1)) E) !![(g : E); 1 + g] = std E := by
  have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  rw [pairLat, frameLat_zero, frameLat_zero, std, Submodule.span_insert]
  congr 3
  · ext i; fin_cases i <;> simp
  · ext i; fin_cases i <;> simp [hg']

theorem mem_genConf_zero (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    ((std E, !![0; 1], !![(g : E); 1 + g]) : Tri E 2 0) ∈
      GenConf σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] := by
  refine ⟨selfDual_std σ, ⟨⟨⟨!![0, 1], ?_⟩, ?_⟩, ⟨⟨!![-1, 1], ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [pairM, cT, TF, Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [pairM, cT, TF, Matrix.mul_apply]; ring
  · ext i j; fin_cases i; fin_cases j; simp [pairM, cT, Matrix.mul_apply]; ring
  · dsimp only
    rw [pairLat_std hg]
    exact ⟨le_rfl, fun v hv _ => hv⟩

omit [NumberField E] in
theorem gq_zero (σ : E →+* E) (g : ℕ) :
    Gq (r := 0) σ 1 (1 + 2 * g) !![-1 - (g : E)] = (g : E) ^ 2 := by
  simp [Gq, lead]
  ring

theorem mem_lzSet (σ : E →+* E) : (std E, ![0, 1]) ∈ LzSet σ !![1, 0; 0, -1] 1 := by
  refine ⟨selfDual_std σ, by simp [form_two], ?_, ?_⟩
  · dsimp only
    rw [Submodule.span_le]
    rintro v rfl
    exact (mem_std _).2 ⟨zero_mem _, one_mem _⟩
  · intro v hv hs
    dsimp only at hv hs ⊢
    rw [Submodule.span_span_of_tower, Submodule.mem_span_singleton] at hs
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨c, hc⟩ := ((mem_std _).1 hv).2
    refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
    ext i
    fin_cases i <;> simp [smul_eq]
    simpa using hc

theorem aut_eq_one (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) {x : Tri E 2 0}
    (hx : x ∈ GenConf σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)])
    {γ : Matrix (Fin 2) (Fin 2) E} (hγ : IsoTri σ !![1, 0; 0, -1] γ x x) : γ = 1 := by
  obtain ⟨Λ, P, Q⟩ := x
  obtain ⟨-, ⟨⟨-, h1⟩, ⟨-, h2⟩, h3⟩, -⟩ := hx
  obtain ⟨-, -, hP, hQ⟩ := hγ
  dsimp only at h1 h2 h3 hP hQ
  have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have e1 := congrFun (congrFun h1 0) 0
  have e2 := congrFun (congrFun h2 0) 0
  have e3 := congrFun (congrFun h3 0) 0
  simp [pairM, cT, TF, Matrix.mul_apply] at e1 e2 e3
  have hd : P 0 0 * Q 1 0 - P 1 0 * Q 0 0 ≠ 0 := by
    intro hd
    have q0 : Q 0 0 = (1 + g) * P 0 0 := by
      linear_combination Q 0 0 * e1 - P 0 0 * e3 - σ (P 1 0) * hd
    have q1 : Q 1 0 = (1 + g) * P 1 0 := by
      linear_combination Q 1 0 * e1 - P 1 0 * e3 - σ (P 0 0) * hd
    rw [q0, q1] at e2
    simp only [map_mul, map_add, map_one, map_natCast] at e2
    apply pow_ne_zero 2 hg'
    linear_combination (1 + g : E) ^ 2 * e1 - e2
  have p (i) := congrFun (congrFun hP i) 0
  have q (i) := congrFun (congrFun hQ i) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at p q
  ext i j
  apply mul_left_cancel₀ hd
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination Q 1 0 * p 0 - P 1 0 * q 0
  · right
    apply mul_left_cancel₀ hd
    linear_combination P 0 0 * q 0 - Q 0 0 * p 0
  · right
    apply mul_left_cancel₀ hd
    linear_combination Q 1 0 * p 1 - P 1 0 * q 1
  · linear_combination P 0 0 * q 1 - Q 0 0 * p 1

theorem massOf_ne_zero {G X : Type} {C : Set X} {iso : G → X → X → Prop} (hC : C.Nonempty)
    (hf : ∀ x ∈ C, Finite {γ : G // iso γ x x}) : massOf C iso ≠ 0 := by
  obtain ⟨x, hx⟩ := hC
  rw [massOf, Ne, ENNReal.tsum_eq_zero]
  intro h
  have h1 := h (Quot.mk _ ⟨x, hx⟩)
  rw [ENNReal.inv_eq_zero, ENat.toENNReal_eq_top, ENat.card_eq_top] at h1
  exact h1.not_finite (hf _ (Quot.out (Quot.mk (fun x y : C => ∃ γ, iso γ x.1 y.1) ⟨x, hx⟩)).2)

theorem mass_ne_zero (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    Mass (r := 0) σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] ≠ 0 := by
  refine massOf_ne_zero ⟨_, mem_genConf_zero σ hg⟩ fun x hx => ?_
  have : Subsingleton {γ // IsoTri σ !![1, 0; 0, -1] γ x x} :=
    ⟨fun a b => Subtype.ext ((aut_eq_one σ hg hx a.2).trans (aut_eq_one σ hg hx b.2).symm)⟩
  infer_instance

abbrev dOne (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)

theorem dOne_ne_zero : dOne E ≠ 0 := by
  rw [dOne, coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)]
  exact inv_ne_zero (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)

omit [NumberField E] in
theorem mem_one_iff' (x : E) : x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ x ∈ Int' E := by
  simp only [FractionalIdeal.mem_one_iff]
  rfl

theorem mem_dInv_one (x : E) : x ∈ dInv E 1 ↔ ∀ t ∈ dOne E, x * t ∈ Int' E := by
  rw [dInv, pow_one, FractionalIdeal.mem_inv_iff dOne_ne_zero]
  simp only [mem_one_iff']

theorem mem_dOne (t : E) : t ∈ dOne E ↔ ∀ x ∈ dInv E 1, t * x ∈ Int' E := by
  have h : dOne E = (dInv E 1)⁻¹ := by rw [dInv, pow_one, inv_inv]
  have h0 : dInv E 1 ≠ 0 := by rw [dInv, pow_one]; exact inv_ne_zero dOne_ne_zero
  rw [h, FractionalIdeal.mem_inv_iff h0]
  simp only [mem_one_iff']

theorem map_mem_dInv (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {x : E} (hx : x ∈ dInv E 1) :
    σ x ∈ dInv E 1 := by
  rw [dInv, pow_one, coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv,
    FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))] at hx ⊢
  intro a ha
  have h := hx (σ a) ((mem_one_iff' _).2 (map_mem_int σ ((mem_one_iff' _).1 ha)))
  let e : E ≃ₐ[ℚ] E := AlgEquiv.ofBijective σ.toRatAlgHom (Function.Involutive.bijective hσ)
  have he : e (x * σ a) = σ x * a := by
    change σ (x * σ a) = _
    rw [map_mul, hσ]
  rw [Algebra.traceForm_apply] at h ⊢
  rwa [← he, Algebra.trace_eq_of_algEquiv]

theorem map_mem_dOne (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {t : E} (ht : t ∈ dOne E) :
    σ t ∈ dOne E := by
  rw [mem_dOne] at ht ⊢
  intro x hx
  have := map_mem_int σ (ht _ (map_mem_dInv σ hσ hx))
  rwa [map_mul, hσ] at this

omit [NumberField E] in
theorem int_mul_mem {I : FractionalIdeal (𝓞 E)⁰ E} {c x : E} (hc : c ∈ Int' E) (hx : x ∈ I) :
    c * x ∈ I := by
  obtain ⟨c, rfl⟩ := hc
  rw [← smul_eq]
  exact Submodule.smul_mem (I : Submodule (𝓞 E) E) c hx

def splitJ (E : Type) [Field E] : Matrix (Fin 8) (Fin 8) E :=
  !![0, 1, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, -1]

omit [NumberField E] in
theorem isHermU_splitJ (σ : E →+* E) : IsHermU σ (splitJ E) := by
  refine ⟨?_, Matrix.isUnit_det_of_left_inverse (B := splitJ E) ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [cT, splitJ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [splitJ, Matrix.mul_apply, Fin.sum_univ_eight]

omit [NumberField E] in
theorem form_split (σ : E →+* E) (v w : Fin 8 → E) :
    form σ (splitJ E) v w = σ (w 0) * v 1 + σ (w 1) * v 0 + σ (w 2) * v 2 + σ (w 3) * v 3 +
      σ (w 4) * v 4 + σ (w 5) * v 5 + σ (w 6) * v 6 - σ (w 7) * v 7 := by
  simp [form, splitJ, dotProduct, Matrix.mulVec, Fin.sum_univ_eight, sub_eq_add_neg]

def splitLat (E : Type) [Field E] [NumberField E] : Submodule (𝓞 E) (Fin 8 → E) :=
  Submodule.pi Set.univ fun i =>
    ((![dInv E 1, dOne E, 1, 1, 1, 1, 1, 1] : Fin 8 → FractionalIdeal (𝓞 E)⁰ E) i : Submodule (𝓞 E) E)

theorem mem_splitLat (v : Fin 8 → E) : v ∈ splitLat E ↔ v 0 ∈ dInv E 1 ∧ v 1 ∈ dOne E ∧
    v 2 ∈ Int' E ∧ v 3 ∈ Int' E ∧ v 4 ∈ Int' E ∧ v 5 ∈ Int' E ∧ v 6 ∈ Int' E ∧ v 7 ∈ Int' E := by
  simp only [← mem_one_iff', splitLat, Submodule.mem_pi, Set.mem_univ, forall_true_left,
    FractionalIdeal.mem_coe, Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
  rfl

theorem selfDual_splitLat (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) :
    SelfDual σ (splitJ E) (splitLat E) := by
  refine ⟨Submodule.fg_pi fun i => FractionalIdeal.fg_of_isNoetherianRing le_rfl _,
    fun v => ⟨fun hv w hw => ?_, fun h => ?_⟩⟩
  · rw [mem_splitLat] at hv hw
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ := hw
    rw [form_split]
    have m {x y : E} (hx : x ∈ Int' E) (hy : y ∈ Int' E) := mul_mem (map_mem_int σ hx) hy
    exact sub_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem
      ((mem_dInv_one _).1 (map_mem_dInv σ hσ w0) _ v1) ((mem_dOne _).1 (map_mem_dOne σ hσ w1) _ v0))
      (m w2 v2)) (m w3 v3)) (m w4 v4)) (m w5 v5)) (m w6 v6)) (m w7 v7)
  · have z (I : FractionalIdeal (𝓞 E)⁰ E) : (0 : E) ∈ I := FractionalIdeal.zero_mem I
    have o : (0 : E) ∈ Int' E := zero_mem _
    have u : (1 : E) ∈ Int' E := one_mem _
    refine (mem_splitLat v).2 ⟨(mem_dInv_one _).2 fun t ht => ?_, (mem_dOne _).2 fun t ht => ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [form_split, hσ, mul_comm] using h ![0, σ t, 0, 0, 0, 0, 0, 0]
        ((mem_splitLat _).2 ⟨z _, map_mem_dOne σ hσ ht, o, o, o, o, o, o⟩)
    · simpa [form_split, hσ, mul_comm] using h ![σ t, 0, 0, 0, 0, 0, 0, 0]
        ((mem_splitLat _).2 ⟨map_mem_dInv σ hσ ht, z _, o, o, o, o, o, o⟩)
    · simpa [form_split] using h ![0, 0, 1, 0, 0, 0, 0, 0]
        ((mem_splitLat _).2 ⟨z _, z _, u, o, o, o, o, o⟩)
    · simpa [form_split] using h ![0, 0, 0, 1, 0, 0, 0, 0]
        ((mem_splitLat _).2 ⟨z _, z _, o, u, o, o, o, o⟩)
    · simpa [form_split] using h ![0, 0, 0, 0, 1, 0, 0, 0]
        ((mem_splitLat _).2 ⟨z _, z _, o, o, u, o, o, o⟩)
    · simpa [form_split] using h ![0, 0, 0, 0, 0, 1, 0, 0]
        ((mem_splitLat _).2 ⟨z _, z _, o, o, o, u, o, o⟩)
    · simpa [form_split] using h ![0, 0, 0, 0, 0, 0, 1, 0]
        ((mem_splitLat _).2 ⟨z _, z _, o, o, o, o, u, o⟩)
    · simpa [form_split] using h ![0, 0, 0, 0, 0, 0, 0, -1]
        ((mem_splitLat _).2 ⟨z _, z _, o, o, o, o, o, neg_mem u⟩)

theorem mem_frameLat_one {n : ℕ} (P : Matrix (Fin n) (Fin (1 + 1)) E) (v : Fin n → E) :
    v ∈ frameLat P ↔ ∃ α ∈ dInv E 1, ∃ β ∈ Int' E, v = fun i => α * P i 0 + β * P i 1 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨b, a, ha, rfl⟩ := hv
      fin_cases b
      · exact ⟨a, ha, 0, zero_mem _, by ext i; simp⟩
      · exact ⟨0, FractionalIdeal.zero_mem _, a, (mem_dInv_zero a).1 ha, by ext i; simp⟩
    | zero => exact ⟨0, FractionalIdeal.zero_mem _, 0, zero_mem _, by ext i; simp⟩
    | add v w _ _ hv hw =>
      obtain ⟨α, hα, β, hβ, rfl⟩ := hv
      obtain ⟨α', hα', β', hβ', rfl⟩ := hw
      exact ⟨α + α', Submodule.add_mem (dInv E 1 : Submodule (𝓞 E) E) hα hα', β + β',
        add_mem hβ hβ', by ext i; simp; ring⟩
    | smul c v _ hv =>
      obtain ⟨α, hα, β, hβ, rfl⟩ := hv
      exact ⟨algebraMap _ E c * α, int_mul_mem ⟨c, rfl⟩ hα, algebraMap _ E c * β,
        mul_mem ⟨c, rfl⟩ hβ, by ext i; simp [smul_eq]; ring⟩
  · rintro ⟨α, hα, β, hβ, rfl⟩
    have h0 : (α • fun i => P i 0) ∈ frameLat P := Submodule.subset_span ⟨0, α, hα, rfl⟩
    have h1 : (β • fun i => P i 1) ∈ frameLat P :=
      Submodule.subset_span ⟨1, β, (mem_dInv_zero β).2 hβ, rfl⟩
    exact add_mem h0 h1

def splitP (E : Type) [Field E] : Matrix (Fin 8) (Fin (1 + 1)) E :=
  !![1, 0; 0, 0; 0, 0; 0, 0; 0, 0; 0, 0; 0, 0; 0, 1]

def splitC (σ : E →+* E) (g : ℕ) (a b : E) : E := -(g * (a * σ a + b * σ b))

def splitQ (σ : E →+* E) (g : ℕ) (a b : E) : Matrix (Fin 8) (Fin (1 + 1)) E :=
  !![1, 0; g * splitC σ g a b, 0; g * a, 0; g * a, 0; g * b, 0; g * b, 0; 0, g; 0, 1 + g]

theorem mem_pairLat_split (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) (a b : E) (v : Fin 8 → E) :
    v ∈ pairLat g (splitP E) (splitQ σ g a b) ↔
      ∃ α ∈ dInv E 1, ∃ β ∈ Int' E, ∃ γ ∈ dInv E 1, ∃ δ ∈ Int' E,
        v = ![α, γ * splitC σ g a b, γ * a, γ * a, γ * b, γ * b, δ, β + δ] := by
  have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have key (α β γ δ : E) : ((fun i => α * splitP E i 0 + β * splitP E i 1) +
      fun i => γ * ((g : E)⁻¹ • (splitQ σ g a b - splitP E)) i 0 +
        δ * ((g : E)⁻¹ • (splitQ σ g a b - splitP E)) i 1) =
      ![α, γ * splitC σ g a b, γ * a, γ * a, γ * b, γ * b, δ, β + δ] := by
    ext i
    fin_cases i <;> simp [splitP, splitQ, hg']
  simp only [pairLat, Submodule.mem_sup, mem_frameLat_one]
  constructor
  · rintro ⟨_, ⟨α, hα, β, hβ, rfl⟩, _, ⟨γ, hγ, δ, hδ, rfl⟩, rfl⟩
    exact ⟨α, hα, β, hβ, γ, hγ, δ, hδ, key α β γ δ⟩
  · rintro ⟨α, hα, β, hβ, γ, hγ, δ, hδ, rfl⟩
    exact ⟨_, ⟨α, hα, β, hβ, rfl⟩, _, ⟨γ, hγ, δ, hδ, rfl⟩, key α β γ δ⟩

theorem primIn_split (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {g : ℕ} (hg : g ≠ 0) {a b : 𝓞 E}
    (hab : differentIdeal ℤ (𝓞 E) = Ideal.span {a, b}) :
    PrimIn (pairLat g (splitP E) (splitQ σ g (a : E) (b : E))) (splitLat E) := by
  have ha : (a : E) ∈ dOne E := FractionalIdeal.mem_coeIdeal_of_mem _
    (hab ▸ Ideal.subset_span (by simp))
  have hb : (b : E) ∈ dOne E := FractionalIdeal.mem_coeIdeal_of_mem _
    (hab ▸ Ideal.subset_span (by simp))
  constructor
  · intro v hv
    obtain ⟨α, hα, β, hβ, γ, hγ, δ, hδ, rfl⟩ := (mem_pairLat_split σ hg _ _ v).1 hv
    have h1 := (mem_dInv_one γ).1 hγ _ ha
    have h2 := (mem_dInv_one γ).1 hγ _ hb
    refine (mem_splitLat _).2 ⟨hα, ?_, h1, h1, h2, h2, hδ, add_mem hβ hδ⟩
    have h3 := Submodule.add_mem (dOne E : Submodule (𝓞 E) E)
      (int_mul_mem h1 (map_mem_dOne σ hσ ha)) (int_mul_mem h2 (map_mem_dOne σ hσ hb))
    have h4 := int_mul_mem (I := dOne E) (neg_mem (natCast_mem (Int' E) g)) h3
    convert h4 using 1
    simp [splitC]
    ring
  · intro v hv hs
    have hv' : ∃ α β γ δ : E,
        v = ![α, γ * splitC σ g (a : E) (b : E), γ * a, γ * a, γ * b, γ * b, δ, β + δ] := by
      clear hv
      induction hs using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨α, -, β, -, γ, -, δ, -, rfl⟩ := (mem_pairLat_split σ hg _ _ v).1 hv
        exact ⟨α, β, γ, δ, rfl⟩
      | zero => exact ⟨0, 0, 0, 0, by ext i; fin_cases i <;> simp⟩
      | add v w _ _ hv hw =>
        obtain ⟨α, β, γ, δ, rfl⟩ := hv
        obtain ⟨α', β', γ', δ', rfl⟩ := hw
        exact ⟨α + α', β + β', γ + γ', δ + δ', by ext i; fin_cases i <;> simp <;> ring⟩
      | smul c v _ hv =>
        obtain ⟨α, β, γ, δ, rfl⟩ := hv
        exact ⟨c * α, c * β, c * γ, c * δ, by ext i; fin_cases i <;> simp <;> ring⟩
    obtain ⟨α, β, γ, δ, rfl⟩ := hv'
    obtain ⟨h0, -, h2, -, h4, -, h6, h7⟩ := (mem_splitLat _).1 hv
    refine (mem_pairLat_split σ hg _ _ _).2
      ⟨α, h0, β, by simpa using sub_mem h7 h6, γ, (mem_dInv_one γ).2 fun t ht => ?_, δ, h6, rfl⟩
    obtain ⟨s, hs, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ht
    rw [hab, Ideal.mem_span_pair] at hs
    obtain ⟨p, q, rfl⟩ := hs
    convert add_mem (mul_mem (⟨p, rfl⟩ : _ ∈ Int' E) h2) (mul_mem (⟨q, rfl⟩ : _ ∈ Int' E) h4) using 1
    simp
    ring

theorem mem_genConf_one (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {g : ℕ} (hg : g ≠ 0) {a b : 𝓞 E}
    (hab : differentIdeal ℤ (𝓞 E) = Ideal.span {a, b}) :
    ((splitLat E, splitP E, splitQ σ g (a : E) (b : E)) : Tri E 8 1) ∈
      GenConf σ (splitJ E) 1 (1 + 2 * g) g
        !![(g : E) * splitC σ g (a : E) (b : E), 0; 0, -1 - (g : E)] := by
  refine ⟨selfDual_splitLat σ hσ,
    ⟨⟨⟨!![1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1], ?_⟩, ?_⟩,
      ⟨⟨!![1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, -1, 1], ?_⟩, ?_⟩, ?_⟩, primIn_split σ hσ hg hab⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [splitP, Matrix.mul_apply, Fin.sum_univ_eight]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairM, cT, TF, splitP, splitJ, Matrix.mul_apply, Fin.sum_univ_eight]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [splitQ, Matrix.mul_apply, Fin.sum_univ_eight]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairM, cT, TF, splitQ, splitC, splitJ, hσ, Matrix.mul_apply, Fin.sum_univ_eight] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairM, cT, splitP, splitQ, splitJ, Matrix.mul_apply, Fin.sum_univ_eight] <;> ring

omit [NumberField E] in
theorem gq_one (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (g : ℕ) (a b : E) :
    Gq (r := 1) σ 1 (1 + 2 * g) !![(g : E) * splitC σ g a b, 0; 0, -1 - (g : E)] =
      ((g : E) ^ 3 * (a * σ a + b * σ b)) ^ 2 := by
  simp [Gq, lead, splitC, hσ, Matrix.det_fin_two]
  ring

theorem exists_different_pair (E : Type) [Field E] [NumberField E] :
    ∃ a b : 𝓞 E, a ≠ 0 ∧ differentIdeal ℤ (𝓞 E) = Ideal.span {a, b} := by
  have h : differentIdeal ℤ (𝓞 E) ≠ ⊥ := fun h => dOne_ne_zero (E := E) (by simp [dOne, h])
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_eq_span_pair ha ha0
  exact ⟨a, b, ha0, hb⟩

omit [NumberField E] in
theorem norm_add_norm_ne_zero (σ : E →+* E) (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x))
    {a : E} (ha : a ≠ 0) (b : E) : a * σ a + b * σ b ≠ 0 := by
  intro h
  have h1 := congrArg τ h
  rw [map_add, map_mul, map_mul, hτ, hτ, Complex.mul_conj, Complex.mul_conj, map_zero,
    ← Complex.ofReal_add, Complex.ofReal_eq_zero] at h1
  have h2 := Complex.normSq_pos.2 ((map_ne_zero τ).2 ha)
  have h3 := Complex.normSq_nonneg (τ b)
  linarith

theorem inhabitants (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    (IsHermU σ (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) E) ∧
      ((Submodule.span (𝓞 E) {![0, 1], ![1, 1]}, !![0; 1], !![(g : E); 1 + g]) : Tri E 2 0) ∈
        GenConf σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] ∧
      Gq (r := 0) σ 1 (1 + 2 * g) !![-1 - (g : E)] = (g : E) ^ 2) ∧
    ((Submodule.span (𝓞 E) {![0, 1], ![1, 1]}, ![0, 1]) ∈ LzSet σ !![1, 0; 0, -1] (1 : E)) ∧
    ((∀ x, σ (σ x) = x) → IsHermU σ (splitJ E) ∧
      ∃ (Q : Matrix (Fin 8) (Fin (1 + 1)) E) (Z : Matrix (Fin (1 + 1)) (Fin (1 + 1)) E),
        ((splitLat E, splitP E, Q) : Tri E 8 1) ∈ GenConf σ (splitJ E) 1 (1 + 2 * g) g Z ∧
        ((∃ τ : E →+* ℂ, ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) → Gq σ 1 (1 + 2 * g) Z ≠ 0)) ∧
    Mass (r := 0) σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] ≠ 0 := by
  refine ⟨⟨⟨?_, by simp [Matrix.det_fin_two]⟩, mem_genConf_zero σ hg, gq_zero σ g⟩, mem_lzSet σ,
    fun hσ => ⟨isHermU_splitJ σ, ?_⟩, mass_ne_zero σ hg⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [cT]
  · obtain ⟨a, b, ha, hab⟩ := exists_different_pair E
    refine ⟨_, _, mem_genConf_one σ hσ hg hab, fun ⟨τ, hτ⟩ => ?_⟩
    rw [gq_one σ hσ]
    exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hg))
      (norm_add_norm_ne_zero σ τ hτ (RingOfIntegers.coe_ne_zero_iff.2 ha) _))

end GlobalTheory.SgGlob.Inhab
