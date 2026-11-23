import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf

noncomputable section

namespace GlobalTheory.Eis.Conv

open Matrix Formalism.UG GlobalTheory.Doubling
open scoped NNReal

section Alg

variable {A : Type} [CommRing A] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
  (e : n ⊕ n ≃ ι)

def uni (S : Matrix n n A) : GL ι A :=
  ⟨(fromBlocks 1 S 0 1).submatrix e.symm e.symm, (fromBlocks 1 (-S) 0 1).submatrix e.symm e.symm,
    by simp [submatrix_mul_equiv, fromBlocks_multiply], by simp [submatrix_mul_equiv, fromBlocks_multiply]⟩

theorem val_uni (S : Matrix n n A) : (uni e S).1 = (fromBlocks 1 S 0 1).submatrix e.symm e.symm := rfl

theorem uni_add (S T : Matrix n n A) : uni e (S + T) = uni e S * uni e T :=
  Units.ext (by simp [val_uni, submatrix_mul_equiv, fromBlocks_multiply, add_comm])

theorem blk_mul_uni (a d : GL n A) (S : Matrix n n A) :
    blkGL e (a, d) * uni e S = uni e (a.1 * S * d⁻¹.1) * blkGL e (a, d) :=
  Units.ext (by simp [val_uni, blkMat, submatrix_mul_equiv, fromBlocks_multiply, Matrix.mul_assoc])

def cti (σ : A →+* A) : GL n A →* GL n A where
  toFun g := ⟨cT σ g⁻¹.1, cT σ g.1, by rw [← cT_mul, Units.mul_inv, cT_one], by rw [← cT_mul, Units.inv_mul, cT_one]⟩
  map_one' := Units.ext (by simp [cT_one])
  map_mul' g h := Units.ext (by simp [cT_mul])

theorem val_cti (σ : A →+* A) (g : GL n A) : (cti σ g).1 = cT σ g⁻¹.1 := rfl

variable [Invertible (2 : A)]

theorem conj_mem (x : GL ι A) (h : (x.1.submatrix e e).toBlocks₂₁ = 0) :
    (cayley e)⁻¹ * x * cayley e ∈ stabGL (diagSub A e) := by
  refine mem_stabGL_diagSub.2 (keepsDiag_of_mulVec fun w hw => ?_)
  obtain ⟨y, rfl⟩ := (mem_diagSub e).1 hw
  refine (mem_diagSub e).2 ⟨⅟(2 : A) • ((x.1.submatrix e e).toBlocks₁₁ *ᵥ (y + y)), ?_⟩
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, cayley_mulVec, mulVec_pairVec e x.1, h]
  refine (congrArg (fun z => (cayley e)⁻¹.1 *ᵥ z) ?_).trans
    (by rw [mulVec_mulVec, Units.inv_mul, one_mulVec] : (cayley e)⁻¹.1 *ᵥ ((cayley e).1 *ᵥ _) = _)
  rw [cayley_mulVec, ← add_smul, invOf_two_add_invOf_two]
  simp

def upper : Subgroup (GL ι A) := (stabGL (diagSub A e)).comap (MulAut.conj (cayley (A := A) e)⁻¹).toMonoidHom

theorem mem_upper {x : GL ι A} : x ∈ upper e ↔ (cayley e)⁻¹ * x * cayley e ∈ stabGL (diagSub A e) := by
  simp [upper]

theorem uni_mem (S : Matrix n n A) : uni e S ∈ upper e := (mem_upper e).2 (conj_mem e _ (by simp [val_uni]))

theorem blk_mem (a d : GL n A) : blkGL e (a, d) ∈ upper e := (mem_upper e).2 (conj_mem e _ (by simp [blkMat]))

theorem exists_decomp {σ : A →+* A} (hσ : ∀ x, σ (σ x) = x) {U : GL n A} (hU : cT σ U.1 = U.1) {p : GL ι A}
    (hp : p ∈ UJ σ (dblGram e U.1)) (hk : KeepsDiag e p.1) : ∃ (β : GL n A) (S : Matrix n n A), cT σ S = -S ∧
      leviMat e p.1 = (cti σ β * U).1 ∧
      blkGL e (1, U) * cayley e * p = uni e S * blkGL e (cti σ β * U, β) * cayley e := by
  have hc : ∀ X : Matrix n n A, cT σ (cT σ X) = X := fun X => by ext i j; exact hσ _
  have hu : IsUnit (quotMat e p.1) := by
    have := (isUnit_iff_isUnit_det _).1 p.isUnit
    rw [hk.det_eq] at this
    exact (isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right this)
  obtain ⟨b₀, hb₀⟩ := hu
  have h0 := quot_levi e hp hk
  have hl : leviMat e p.1 = (cti σ (U * b₀) * U).1 := by
    have h0' : cT σ (U * b₀).1 * leviMat e p.1 = U.1 := by rw [Units.val_mul, cT_mul, hU, hb₀]; exact h0
    refine Eq.trans ?_ (congrArg (cT σ (U * b₀)⁻¹.1 * ·) h0')
    rw [← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul]
  have h1 : cT σ (p.1.submatrix e e) * fromBlocks U.1 0 0 (-U.1) * p.1.submatrix e e = fromBlocks U.1 0 0 (-U.1) := by
    rw [← submatrix_blkMat e, show cT σ (p.1.submatrix e e) = (cT σ p.1).submatrix e e from rfl, submatrix_mul_equiv,
      submatrix_mul_equiv]
    exact congrArg (fun X => X.submatrix e e) hp
  have hp' : p.1 = (fromBlocks (p.1.submatrix e e).toBlocks₁₁ (p.1.submatrix e e).toBlocks₁₂
      (p.1.submatrix e e).toBlocks₂₁ (p.1.submatrix e e).toBlocks₂₂).submatrix e.symm e.symm := by
    simp [fromBlocks_toBlocks]
  rw [← fromBlocks_toBlocks (p.1.submatrix e e)] at h1
  unfold KeepsDiag at hk
  unfold leviMat at hk hl ⊢
  unfold quotMat at hb₀
  generalize (p.1.submatrix e e).toBlocks₁₁ = a at *
  generalize (p.1.submatrix e e).toBlocks₁₂ = b at *
  generalize (p.1.submatrix e e).toBlocks₂₁ = c at *
  generalize (p.1.submatrix e e).toBlocks₂₂ = d at *
  obtain rfl : d = a + b - c := by rw [← hk]; abel
  have hs : ∀ X Y : Matrix n n A, cT σ (X - Y) = cT σ X - cT σ Y := fun X Y => by ext; simp [cT]
  have ha : ∀ X Y : Matrix n n A, cT σ (X + Y) = cT σ X + cT σ Y := fun X Y => by ext; simp [cT]
  have hf : cT σ (fromBlocks a b c (a + b - c)) = fromBlocks (cT σ a) (cT σ c) (cT σ b) (cT σ a + cT σ b - cT σ c) := by
    rw [← ha, ← hs]; simp [cT, fromBlocks_map, fromBlocks_transpose]
  simp only [hf, fromBlocks_multiply, Matrix.mul_zero, add_zero, zero_add, fromBlocks_inj] at h1
  have h2 : cT σ (c - b) * (U * b₀).1 + cT σ (U * b₀).1 * (c - b) = 0 := by
    have h3 : (2 : A) • (cT σ (c - b) * (U * b₀).1 + cT σ (U * b₀).1 * (c - b)) = 0 := by
      rw [Units.val_mul, cT_mul, hU, hb₀, hs, hs, two_smul]
      refine Eq.trans ?_ ((congrArg₂ (· + ·) (congrArg₂ (· - ·) h1.1 h1.2.1)
        (congrArg₂ (· - ·) h1.2.2.2 h1.2.2.1)).trans (by simp))
      noncomm_ring
    simpa [smul_smul] using congrArg (⅟(2 : A) • ·) h3
  refine ⟨U * b₀, (c - b) * (U * b₀)⁻¹.1, ?_, hl, Units.ext ?_⟩
  · have := congrArg (fun X => cT σ (U * b₀)⁻¹.1 * X * (U * b₀)⁻¹.1) h2
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul] at this
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, ← cT_mul, ← cT_mul,
      Units.mul_inv, cT_one, Matrix.one_mul] at this
    exact eq_neg_of_add_eq_zero_left this
  · have h4 : (c - b) * (U * b₀)⁻¹.1 * (U * b₀).1 = c - b := by rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    simp only [Units.val_mul (uni e _ * _), Units.val_mul (uni e _), Units.val_mul (blkGL e _ * _),
      Units.val_mul (blkGL e _), val_blkGL, val_uni, blkMat, ← hl]
    rw [hp']
    simp only [cayley, submatrix_mul_equiv, fromBlocks_multiply, h4, Matrix.mul_zero, add_zero, zero_add,
      Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, Units.val_one, Matrix.mul_neg]
    congr 1
    rw [Units.val_mul, hb₀, fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

end Alg

section Bounded

variable {Q X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def Bdd (f : Q → X) : Prop := ∃ K, IsCompact K ∧ ∀ q, f q ∈ K

theorem Bdd.map {f : Q → X} (h : Bdd f) {g : X → Y} (hg : Continuous g) : Bdd fun q => g (f q) :=
  let ⟨K, hK, h⟩ := h; ⟨g '' K, hK.image hg, fun q => ⟨_, h q, rfl⟩⟩

theorem Bdd.prod {f : Q → X} {g : Q → Y} (h : Bdd f) (h' : Bdd g) : Bdd fun q => (f q, g q) :=
  let ⟨K, hK, h⟩ := h; let ⟨L, hL, h'⟩ := h'; ⟨K ×ˢ L, hK.prod hL, fun q => ⟨h q, h' q⟩⟩

theorem Bdd.comp {f : Q → X} (h : Bdd f) {Q' : Type} (r : Q' → Q) : Bdd fun q => f (r q) :=
  let ⟨K, hK, h⟩ := h; ⟨K, hK, fun _ => h _⟩

theorem Bdd.mul [Mul X] [ContinuousMul X] {f g : Q → X} (h : Bdd f) (h' : Bdd g) : Bdd fun q => f q * g q :=
  (h.prod h').map (g := fun x => x.1 * x.2) continuous_mul

theorem Bdd.const (x : X) : Bdd fun _ : Q => x := ⟨{x}, isCompact_singleton, fun _ => rfl⟩

theorem bdd_matrix {m n : Type} {f : Q → Matrix m n X} {K : Set X} (hK : IsCompact K) (h : ∀ q i j, f q i j ∈ K) :
    Bdd f := ⟨Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun q i _ j _ => h q i j⟩

theorem Bdd.entries {m n : Type} [Finite m] [Finite n] {f : Q → Matrix m n X} (h : Bdd f) :
    ∃ K, IsCompact K ∧ ∀ q i j, f q i j ∈ K :=
  let ⟨K, hK, h⟩ := h
  ⟨⋃ i, ⋃ j, (fun M : Matrix m n X => M i j) '' K, isCompact_iUnion fun i => isCompact_iUnion fun j =>
    hK.image (continuous_id.matrix_elem i j), fun q i j => Set.mem_iUnion₂.2 ⟨i, j, _, h q, rfl⟩⟩

theorem bdd_units [Monoid X] [T1Space X] [ContinuousMul X] {f : Q → Xˣ} (h : Bdd fun q => (f q).1)
    (h' : Bdd fun q => (f q)⁻¹.1) : Bdd f :=
  let ⟨K, hK, h⟩ := h.prod (h'.map MulOpposite.continuous_op)
  ⟨_, Units.isClosedEmbedding_embedProduct.isCompact_preimage hK, h⟩

end Bounded

section Count

variable {E A : Type} [Field E] [CommRing A] [Nontrivial A] (j : E →+* A) {n ι : Type} [Fintype n] [DecidableEq n]
  [Fintype ι] [DecidableEq ι] (e : n ⊕ n ≃ ι)

theorem mem_rat {g : GL ι A} : g ∈ (bc j).range ↔ ∀ a b, g.1 a b ∈ j.range := by
  refine ⟨by rintro ⟨x, rfl⟩ a b; exact ⟨_, rfl⟩, fun h => ?_⟩
  choose x hx using h
  have h1 : (of x).map j = g.1 := by ext a b; exact hx a b
  have h2 : (of x).det ≠ 0 := fun h => by
    have := (isUnit_iff_isUnit_det _).1 g.isUnit
    rw [← h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero] at this
    exact not_isUnit_zero this
  exact ⟨GeneralLinearGroup.mkOfDetNeZero _ h2, Units.ext h1⟩

theorem blocks_mem {R : Subring A} {a b c d : Matrix n n A} (ha : ∀ i k, a i k ∈ R) (hb : ∀ i k, b i k ∈ R)
    (hc : ∀ i k, c i k ∈ R) (hd : ∀ i k, d i k ∈ R) (x y : ι) : (fromBlocks a b c d).submatrix e.symm e.symm x y ∈ R := by
  obtain ⟨x | x, rfl⟩ := e.surjective x <;> obtain ⟨y | y, rfl⟩ := e.surjective y <;> simp [*]

theorem one_mem_entries (R : Subring A) (i k : n) : (1 : Matrix n n A) i k ∈ R := by
  rw [one_apply]; split_ifs; exacts [one_mem _, zero_mem _]

theorem uni_rat (S : Matrix n n E) : uni e (S.map j) ∈ (bc j).range :=
  (mem_rat j).2 (blocks_mem e (one_mem_entries _) (fun _ _ => ⟨_, rfl⟩) (fun _ _ => zero_mem _) (one_mem_entries _))

theorem blk_rat {a d : GL n A} (ha : a ∈ (bc j).range) (hd : d ∈ (bc j).range) : blkGL e (a, d) ∈ (bc j).range :=
  (mem_rat j).2 (blocks_mem e ((mem_rat j).1 ha) (fun _ _ => zero_mem _) (fun _ _ => zero_mem _) ((mem_rat j).1 hd))

theorem cayley_rat [Invertible (2 : A)] : cayley e ∈ (bc j).range :=
  (mem_rat j).2 (blocks_mem e (one_mem_entries _) (one_mem_entries _) (one_mem_entries _)
    fun _ _ => neg_mem (one_mem_entries _ _ _))

theorem cti_rat {σ : A →+* A} (hσ : ∀ x ∈ j.range, σ x ∈ j.range) {a : GL n A} (ha : a ∈ (bc j).range) :
    cti σ a ∈ (bc j).range := (mem_rat j).2 fun x y => hσ _ ((mem_rat j).1 (inv_mem ha) y x)

variable [TopologicalSpace A] [IsTopologicalRing A]

theorem exists_card_le (hF : ∀ Ω : Set A, IsCompact Ω → {x : E | j x ∈ Ω}.Finite) {Q : Type} {Z w : Q → GL ι A}
    (hZ : ∀ q, Z q ∈ (bc j).range) (hi : Function.Injective Z) (hw : Bdd w) :
    ∃ N : ℕ, ∀ (z : GL ι A) (T : Finset Q), (∀ q ∈ T, Z q = z * w q) → T.card ≤ N := by
  obtain ⟨Ω, hΩ, h⟩ := ((((hw.comp Prod.fst).map continuous_inv).mul (hw.comp Prod.snd)).map
    Units.continuous_val).entries
  have h1 : {g : GL ι A | ∀ a b, g.1 a b ∈ j '' {x : E | j x ∈ Ω}}.Finite :=
    (Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => (hF Ω hΩ).image j).preimage
      (f := fun g : GL ι A => (g.1 : ι → ι → A)) fun _ _ _ _ h => Units.ext h
  refine ⟨h1.toFinset.card, fun z T hT => ?_⟩
  rcases T.eq_empty_or_nonempty with rfl | ⟨q₀, h₀⟩
  · simp
  refine Finset.card_le_card_of_injOn (fun q => (Z q₀)⁻¹ * Z q) (fun q hq => ?_) fun q _ q' _ h => hi (mul_left_cancel h)
  refine h1.mem_toFinset.2 fun a b => ?_
  obtain ⟨x, hx⟩ := (mem_rat j).1 (mul_mem (inv_mem (hZ q₀)) (hZ q)) a b
  refine ⟨x, ?_, hx⟩
  rw [Set.mem_setOf_eq, hx, hT q hq, hT q₀ h₀, show (z * w q₀)⁻¹ * (z * w q) = (w q₀)⁻¹ * w q by group]
  exact h (q₀, q) a b

omit [Nontrivial A] in
theorem continuous_uni : Continuous (uni (A := A) e) :=
  Units.continuous_iff.2 ⟨(continuous_const.matrix_fromBlocks continuous_id continuous_const
    continuous_const).matrix_submatrix _ _, (continuous_const.matrix_fromBlocks continuous_neg continuous_const
    continuous_const).matrix_submatrix _ _⟩

omit [Nontrivial A] in
theorem continuous_cti {σ : A →+* A} (hσ : Continuous σ) : Continuous (cti (n := n) σ) :=
  Units.continuous_iff.2 ⟨(Units.continuous_coe_inv.matrix_map hσ).matrix_transpose,
    (Units.continuous_val.matrix_map hσ).matrix_transpose⟩

end Count

section Core

variable {E A : Type} [Field E] [CommRing A] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

def dg (s : Aˣ) (l : n → ℤ) : GL n A :=
  ⟨diagonal fun i => (s ^ l i).1, diagonal fun i => (s ^ l i)⁻¹.1, by simp, by simp⟩

theorem cti_dg {σ : A →+* A} {s : Aˣ} (hs : σ s.1 = s.1) (l : n → ℤ) : cti σ (dg s l) = (dg s l)⁻¹ := by
  have h : Units.map σ.toMonoidHom s = s := Units.ext hs
  have h1 : ∀ i, σ (s ^ l i)⁻¹.1 = (s ^ l i)⁻¹.1 := fun i => by
    have := congrArg Units.val (map_inv (Units.map σ.toMonoidHom) (s ^ l i))
    rwa [map_zpow, h] at this
  refine Units.ext ?_
  change ((diagonal fun i => (s ^ l i)⁻¹.1).map σ)ᵀ = diagonal fun i => (s ^ l i)⁻¹.1
  rw [diagonal_map (map_zero σ), diagonal_transpose]
  exact congrArg diagonal (funext h1)

theorem det_dg (s : Aˣ) (l : n → ℤ) : GeneralLinearGroup.det (dg s l) = ∏ i, s ^ l i :=
  Units.ext (by simp [dg])

theorem det_cti (σ : A →+* A) (g : GL n A) :
    GeneralLinearGroup.det (cti σ g) = Units.map σ.toMonoidHom (GeneralLinearGroup.det g⁻¹) :=
  Units.ext ((det_transpose _).trans (σ.map_det _).symm)

variable [Nontrivial A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Invertible (2 : A)]

theorem core (j : E →+* A) (e : n ⊕ n ≃ ι) {σ : A →+* A} (hσc : Continuous σ) (hσ : ∀ x, σ (σ x) = x)
    (hσj : ∀ x ∈ j.range, σ x ∈ j.range) {s : Aˣ} (hs : σ s.1 = s.1) {ν : Aˣ →* ℝ≥0} (hν : Continuous ν)
    (hνσ : ∀ x, ν (Units.map σ.toMonoidHom x) = ν x) (hνj : ∀ x : Aˣ, x.1 ∈ j.range → ν x = 1) {b : ℝ} (hb : 0 < b)
    (hνs : (ν s : ℝ) = b⁻¹)
    (hD : ∀ Ω : Set A, IsCompact Ω → {x : E | j x ∈ Ω}.Finite ∧
      ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, j x = s.1 ^ m * ω → x = 0)
    (hR : ∃ Ω : Set A, IsCompact Ω ∧ ∀ β : GL n A, ∃ (δ : GL n E) (l : n → ℤ) (c : GL n A),
      (∀ i k, c.1 i k ∈ Ω ∧ c⁻¹.1 i k ∈ Ω) ∧ δ.1.map j * β.1 = diagonal (fun i => (s ^ l i).1) * c.1)
    (hC : ∃ (Ω : Set A) (C : ℝ), IsCompact Ω ∧ ∀ m : n → ℕ, ∃ Y : Finset (Matrix n n A),
      (Y.card : ℝ) ≤ C * ∏ i, b ^ (Fintype.card n * m i) ∧ ∀ S : Matrix n n A, cT σ S = -S → ∃ S₀ : Matrix n n E, ∃ y ∈ Y,
        ∃ ω : Matrix n n A, (∀ i k, ω i k ∈ Ω) ∧
          S = S₀.map j + y + diagonal (fun i => s.1 ^ m i) * ω * diagonal (fun i => s.1 ^ m i))
    {U : GL n A} (hU : cT σ U.1 = U.1) (hUj : U ∈ (bc j).range) {Q : Type} {p k : Q → GL ι A}
    (hp : ∀ q, p q ∈ UJ σ (dblGram e U.1)) (hp' : ∀ q, KeepsDiag e (p q).1) (hk : Bdd k)
    (hγ : ∀ q, p q * k q ∈ (bc j).range)
    (hi : ∀ q q', p q' * k q' * (p q * k q)⁻¹ ∈ stabGL (diagSub A e) → q = q') :
    ∃ (C : ℝ) (m : Q → n → ℕ), (∀ q (x : Aˣ), x.1 = (leviMat e (p q).1).det → (ν x : ℝ) ≤ C * ∏ i, (b ^ m q i)⁻¹) ∧
      ∀ (μ : n → ℕ) (T : Finset Q), (∀ q ∈ T, m q = μ) → (T.card : ℝ) ≤ C * ∏ i, b ^ (Fintype.card n * μ i) := by
  classical
  have hcc : ∀ X : Matrix n n A, cT σ (cT σ X) = X := fun X => by ext i j; exact hσ _
  choose β S hS hα hdec using fun q => exists_decomp e hσ hU (hp q) (hp' q)
  obtain ⟨Ω₁, hΩ₁, hR⟩ := hR
  choose δ l c hc hred using fun q => hR (β q)
  replace hred : ∀ q, bc j (δ q) * β q = dg s (l q) * c q := fun q => Units.ext (hred q)
  have hcb : Bdd c := bdd_units (bdd_matrix hΩ₁ fun q i k => (hc q i k).1) (bdd_matrix hΩ₁ fun q i k => (hc q i k).2)
  set w₁ : Q → GL ι A := fun q => blkGL e (cti σ (c q) * U, c q) * cayley e * k q with hw₁
  have hw₁b : Bdd w₁ := (((((hcb.map (continuous_cti hσc)).mul (Bdd.const U)).prod hcb).map
    (continuous_blkGL e)).mul (Bdd.const _)).mul hk
  set L : Q → GL ι A := fun q => blkGL e (cti σ (bc j (δ q)), bc j (δ q)) * blkGL e (1, U) with hL
  have hLj : ∀ q, L q * cayley e * (p q * k q) ∈ (bc j).range := fun q =>
    mul_mem (mul_mem (mul_mem (blk_rat j e (cti_rat j hσj ⟨_, rfl⟩) ⟨_, rfl⟩) (blk_rat j e (one_mem _) hUj))
      (cayley_rat j e)) (hγ q)
  set S' : Q → Matrix n n A := fun q => (cti σ (bc j (δ q))).1 * S q * (bc j (δ q))⁻¹.1 with hS'
  have hS'' : ∀ q, cT σ (S' q) = -S' q := fun q => by
    simp only [hS', val_cti, cT_mul, hcc, hS, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have h1 : ∀ q, L q * cayley e * (p q * k q) = uni e (S' q) * blkGL e ((dg s (l q))⁻¹, dg s (l q)) * w₁ q := fun q => by
    calc _ = blkGL e (cti σ (bc j (δ q)), bc j (δ q)) * (blkGL e (1, U) * cayley e * p q) * k q := by
          simp only [hL, mul_assoc]
      _ = uni e (S' q) * (blkGL e (cti σ (bc j (δ q)), bc j (δ q)) * blkGL e (cti σ (β q) * U, β q)) * cayley e * k q := by
          rw [hdec, ← mul_assoc, ← mul_assoc, blk_mul_uni, mul_assoc (uni e _)]
      _ = _ := by
          rw [← map_mul, Prod.mk_mul_mk, ← mul_assoc (cti σ _), ← map_mul, hred, map_mul (cti σ), cti_dg hs,
            mul_assoc _ (cti σ _), ← Prod.mk_mul_mk, map_mul]
          simp only [hw₁, mul_assoc]
  clear_value w₁ S'
  obtain ⟨Ω₂, hΩ₂, hw₂⟩ := (hw₁b.map Units.continuous_val).entries
  obtain ⟨m₀, hm₀⟩ := (hD Ω₂ hΩ₂).2
  have hl : ∀ q i, l q i ≤ m₀ := fun q i => by
    by_contra! hlt
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := l q i) (by omega)
    have h2 : ∀ x, (L q * cayley e * (p q * k q)).1 (e (.inr i)) x = 0 := fun x => by
      obtain ⟨y, hy⟩ := (mem_rat j).1 (hLj q) (e (.inr i)) x
      have h3 : j y = s.1 ^ m * (w₁ q).1 (e (.inr i)) x := by
        rw [hy, h1, Units.val_mul, Units.val_mul, val_uni, val_blkGL, blkMat, submatrix_mul_equiv, fromBlocks_multiply,
          mul_apply, ← e.sum_comp]
        simp [dg, diagonal_apply, hm]
      rw [← hy, hm₀ m (by omega) _ (hw₂ q _ _) y h3, map_zero]
    have := (isUnit_iff_isUnit_det _).1 (L q * cayley e * (p q * k q)).isUnit
    rw [det_eq_zero_of_row_eq_zero _ h2] at this
    exact not_isUnit_zero this
  set m : Q → n → ℕ := fun q i => (m₀ - l q i).toNat with hm
  have hlm : ∀ q i, l q i = m₀ - m q i := fun q i => by have := hl q i; simp only [hm]; omega
  obtain ⟨Ω₃, C, hΩ₃, hC⟩ := hC
  choose Y hY hC using hC
  choose S₀ y hy ω hω hcov using fun q => hC (m q) (S' q) (hS'' q)
  set w : Q → GL ι A := fun q => uni e ((s.1 ^ m₀ * s.1 ^ m₀) • ω q) * w₁ q with hw
  have hwb : Bdd w := (((bdd_matrix hΩ₃ hω).map (continuous_const_smul _)).map (continuous_uni e)).mul hw₁b
  set Z : Q → GL ι A := fun q => uni e ((-S₀ q).map j) * (L q * cayley e * (p q * k q)) with hZ
  have h4 : ∀ q, Z q = uni e (y q) * blkGL e ((dg s fun i => m₀ - m q i)⁻¹, dg s fun i => m₀ - m q i) * w q := fun q => by
    have h5 : ∀ i, (s ^ ((m₀ : ℤ) - m q i))⁻¹.1 * s.1 ^ m₀ = s.1 ^ m q i := fun i => by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast,
        ← _root_.zpow_neg, ← _root_.zpow_add]
      congr 2; ring
    simp only [hZ, hw]
    rw [h1, ← mul_assoc, ← mul_assoc, ← uni_add, ← mul_assoc, mul_assoc (uni e (y q)), blk_mul_uni, ← mul_assoc,
      ← uni_add, show l q = fun i => (m₀ : ℤ) - m q i from funext (hlm q), hcov]
    congr 3
    ext i k
    change _ = y q i k + (diagonal (fun i => (s ^ ((m₀ : ℤ) - m q i))⁻¹.1) * ((s.1 ^ m₀ * s.1 ^ m₀) • ω q) *
      diagonal (fun i => (s ^ ((m₀ : ℤ) - m q i))⁻¹.1)) i k
    simp only [Matrix.add_apply, map_apply, Matrix.neg_apply, map_neg, mul_diagonal, diagonal_mul, Matrix.smul_apply,
      smul_eq_mul, ← h5]
    ring
  have hZi : Function.Injective Z := fun q q' h => by
    have h6 : ∀ q, uni e ((-S₀ q).map j) * L q ∈ upper e := fun q =>
      mul_mem (uni_mem e _) (mul_mem (blk_mem e _ _) (blk_mem e _ _))
    refine hi q q' ?_
    convert (mem_upper e).1 (mul_mem (inv_mem (h6 q')) (h6 q)) using 1
    simp only [hZ] at h
    generalize p q * k q = g at *
    generalize p q' * k q' = g' at *
    rw [mul_inv_eq_iff_eq_mul]
    calc g' = (cayley e)⁻¹ * (uni e ((-S₀ q').map j) * L q')⁻¹ * (uni e ((-S₀ q').map j) * (L q' * cayley e * g')) := by
          group
      _ = _ := by rw [← h]; group
  obtain ⟨N, hN⟩ := exists_card_le j (fun Ω h => (hD Ω h).1) (Z := Z) (fun q => mul_mem (uni_rat j e _) (hLj q)) hZi hwb
  have hdet : Continuous (GeneralLinearGroup.det : GL n A → Aˣ) := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩
  obtain ⟨K, hK, hcK⟩ := (((hcb.map continuous_inv).map hdet).map hν).map NNReal.continuous_coe
  obtain ⟨B, hB⟩ := hK.bddAbove
  have hνd : ∀ g ∈ (bc (n := n) j).range, ν (GeneralLinearGroup.det g) = 1 := by
    rintro _ ⟨x, rfl⟩
    exact hνj _ ⟨x.1.det, j.map_det _⟩
  refine ⟨max (B * b ^ (m₀ * Fintype.card n)) (N * C), m, fun q x hx => ?_, fun μ T hT => ?_⟩
  · have h7 : x = GeneralLinearGroup.det (cti σ (β q) * U) := Units.ext (by rw [hx, hα]; rfl)
    have h8 : β q = (bc j (δ q))⁻¹ * (dg s (l q) * c q) := by rw [← hred, inv_mul_cancel_left]
    have h9 : (ν x : ℝ) = ν (GeneralLinearGroup.det (c q)⁻¹) * ∏ i, b ^ l q i := by
      rw [h7, map_mul, map_mul, hνd U hUj, mul_one, det_cti, hνσ, h8]
      simp only [_root_.mul_inv_rev, map_mul, map_inv, inv_inv, hνd _ ⟨δ q, rfl⟩, mul_one, det_dg, map_prod, map_zpow₀,
        map_zpow]
      push_cast
      simp only [hνs, _root_.inv_zpow, Finset.prod_inv_distrib, inv_inv]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    rw [h9, mul_assoc]
    refine mul_le_mul (hB (hcK q)) (le_of_eq ?_) (by positivity) ((NNReal.coe_nonneg _).trans (hB (hcK q)))
    simp only [hlm, zpow_sub₀ hb.ne', zpow_natCast, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, pow_mul]
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    have h10 : T.card ≤ N * (Y μ).card := Finset.card_le_mul_card_image_of_maps_to
      (fun q hq => hT q hq ▸ hy q) N fun z _ => hN (uni e z * blkGL e ((dg s fun i => m₀ - μ i)⁻¹, dg s fun i => m₀ - μ i)) _
        fun q hq => by rw [h4, (Finset.mem_filter.1 hq).2, hT q (Finset.mem_filter.1 hq).1]
    rw [mul_assoc]
    exact (Nat.cast_le.2 h10).trans (by push_cast; exact mul_le_mul_of_nonneg_left (hY μ) (Nat.cast_nonneg _))

end Core

end GlobalTheory.Eis.Conv

end
