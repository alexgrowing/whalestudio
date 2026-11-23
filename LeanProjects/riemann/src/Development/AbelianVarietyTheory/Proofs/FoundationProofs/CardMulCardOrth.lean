import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinsumNormNeg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneIntegerConjDiffPrimeTo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrameEmbeddingUniqueFixedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormCmPrimeInertPrimeSignStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCompSurjective
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.HermGauss

theorem sum_char {G : Type} [AddCommGroup G] [Fintype G] (f : G → ℂ) (h0 : f 0 = 1)
    (h : ∀ a b, f (a + b) = f a * f b) :
    ∑ a, f a = if ∀ a, f a = 1 then (Nat.card G : ℂ) else 0 := by
  split_ifs with hf
  · simp [hf]
  · push_neg at hf
    obtain ⟨a, ha⟩ := hf
    have e : ∑ b, f b = f a * ∑ b, f b := by
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addLeft a)]
      exact Finset.sum_congr rfl fun b _ => h a b
    have : (1 - f a) * ∑ b, f b = 0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha.symm)

section
variable {R : Type} [CommRing R] {σ : R →+* R} {M : Type} [AddCommGroup M] [Module R M]
  {φ : M → ℂ} {β : M → M → ℂ}

theorem beta_ne (h0 : ∀ x, φ x ≠ 0) (h1 : ∀ x y, φ (x + y) = φ x * φ y * β x y) (x y : M) :
    β x y ≠ 0 := fun h => h0 (x + y) (by rw [h1, h, mul_zero])

theorem beta_comm (h0 : ∀ x, φ x ≠ 0) (h1 : ∀ x y, φ (x + y) = φ x * φ y * β x y) (x y : M) :
    β x y = β y x := by
  have := h1 x y
  rw [add_comm, h1, mul_comm (φ y)] at this
  exact (mul_left_cancel₀ (mul_ne_zero (h0 x) (h0 y)) this).symm

theorem beta_zero (h0 : ∀ x, φ x ≠ 0) (h1 : ∀ x y, φ (x + y) = φ x * φ y * β x y)
    (h2 : ∀ x x' y, β (x + x') y = β x y * β x' y) (y : M) : β 0 y = 1 := by
  have := h2 0 0 y
  rw [add_zero] at this
  exact (mul_left_cancel₀ (beta_ne h0 h1 0 y) (by rw [mul_one]; exact this)).symm

theorem phi_zero (h0 : ∀ x, φ x ≠ 0) (h1 : ∀ x y, φ (x + y) = φ x * φ y * β x y)
    (h2 : ∀ x x' y, β (x + x') y = β x y * β x' y) : φ 0 = 1 := by
  have := h1 0 0
  rw [add_zero, beta_zero h0 h1 h2, mul_one] at this
  exact (mul_left_cancel₀ (h0 0) (by rw [mul_one]; exact this)).symm

theorem exists_orth (hz : ∀ y, β 0 y = 1) (h2 : ∀ x x' y, β (x + x') y = β x y * β x' y)
    (h3 : ∀ (a : R) x y, β (a • x) y = β x (σ a • y)) (X : Submodule R M) :
    ∃ Y : Submodule R M, ∀ y, y ∈ Y ↔ ∀ x ∈ X, β y x = 1 :=
  ⟨{ carrier := {y | ∀ x ∈ X, β y x = 1}
     add_mem' := fun {a b} ha hb x hx => by rw [h2, ha x hx, hb x hx, one_mul]
     zero_mem' := fun x _ => hz x
     smul_mem' := fun c a ha x hx => by rw [h3]; exact ha _ (X.smul_mem _ hx) }, fun _ => Iff.rfl⟩

theorem sum_beta [Fintype M] (hc : ∀ x y, β x y = β y x) (hz : ∀ y, β 0 y = 1)
    (h2 : ∀ x x' y, β (x + x') y = β x y * β x' y) {X Y : Submodule R M}
    (hY : ∀ y, y ∈ Y ↔ ∀ x ∈ X, β y x = 1) (y : M) :
    ∑ x : X, β y x = if y ∈ Y then (Nat.card X : ℂ) else 0 := by
  rw [sum_char (fun x : X => β y x) (by rw [hc]; exact hz y)
    (fun a b => by rw [hc y, hc y, hc y]; exact h2 _ _ _)]
  simp only [hY, Subtype.forall]

theorem card_mul_card_orth [Finite M] (hc : ∀ x y, β x y = β y x) (hz : ∀ y, β 0 y = 1)
    (h2 : ∀ x x' y, β (x + x') y = β x y * β x' y) (h4 : ∀ x, (∀ y, β x y = 1) → x = 0)
    {X Y : Submodule R M} (hY : ∀ y, y ∈ Y ↔ ∀ x ∈ X, β y x = 1) :
    Nat.card X * Nat.card Y = Nat.card M := by
  letI := Fintype.ofFinite M
  have e1 : ∑ y : M, ∑ x : X, β y x = (Nat.card X * Nat.card Y : ℕ) := by
    simp only [sum_beta hc hz h2 hY]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.cast_mul, mul_comm,
      Nat.card_eq_fintype_card (α := Y), Fintype.card_subtype]
  have e2 : ∑ x : X, ∑ y : M, β y x = (Nat.card M : ℕ) := by
    rw [Finset.sum_eq_single (0 : X)]
    · simp [hc _ 0, hz]
    · intro x _ hx
      rw [sum_char (fun y => β y x) (hz _) (fun a b => h2 _ _ _), if_neg]
      intro h
      exact hx (Subtype.ext (h4 _ fun y => by rw [hc]; exact h y))
    · simp
  rw [Finset.sum_comm, e2] at e1
  exact_mod_cast e1.symm

theorem sum_eq_sum_orth [Fintype M] (hc : ∀ x y, β x y = β y x) (hz : ∀ y, β 0 y = 1)
    (h1 : ∀ x y, φ (x + y) = φ x * φ y * β x y)
    (h2 : ∀ x x' y, β (x + x') y = β x y * β x' y) {X Y : Submodule R M}
    (hY : ∀ y, y ∈ Y ↔ ∀ x ∈ X, β y x = 1) (hX : ∀ x ∈ X, φ x = 1) :
    ∑ y, φ y = ∑ y : Y, φ y := by
  have hn : (Nat.card X : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := X)).ne'
  apply mul_left_cancel₀ hn
  have e1 : ∑ x : X, ∑ y : M, φ (y + x) = Nat.card X * ∑ y, φ y := by
    have e0 : ∀ x : M, ∑ y, φ (y + x) = ∑ y, φ y := fun x => Equiv.sum_comp (Equiv.addRight x) φ
    simp [e0]
  rw [← e1, Finset.sum_comm, Finset.mul_sum,
    ← Finset.sum_subtype (Finset.univ.filter (· ∈ Y)) (by simp) (fun y => (Nat.card X : ℂ) * φ y),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_congr rfl (g := fun x : X => φ y * β y x)
    (fun x _ => by rw [h1, hX _ x.2, mul_one]), ← Finset.mul_sum, sum_beta hc hz h2 hY]
  split_ifs <;> simp [mul_comm]

theorem sum_comp_surj {G Q : Type} [AddCommGroup G] [AddCommGroup Q] [Fintype G] [Fintype Q]
    (π : G →+ Q) (hπ : Function.Surjective π) (g : Q → ℂ) :
    ∃ n : ℕ, 0 < n ∧ ∑ y, g (π y) = n * ∑ q, g q := by
  first
  | exact @_root_.GlobalTheory.SumCompSurjective.sum_comp_surjective
  | exact _root_.GlobalTheory.SumCompSurjective.sum_comp_surjective
  | (apply _root_.GlobalTheory.SumCompSurjective.sum_comp_surjective <;> assumption)
  | (intros; apply _root_.GlobalTheory.SumCompSurjective.sum_comp_surjective <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SumCompSurjective.sum_comp_surjective <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SumCompSurjective.sum_comp_surjective ..)

end

def IsHerm {R : Type} [CommRing R] (σ : R →+* R) {M : Type} [AddCommGroup M] [Module R M]
    (φ : M → ℂ) (β : M → M → ℂ) : Prop :=
  (∀ x, φ x ≠ 0) ∧ (∀ x y, φ (x + y) = φ x * φ y * β x y) ∧ (∀ x x' y, β (x + x') y = β x y * β x' y) ∧
    (∀ (a : R) x y, β (a • x) y = β x (σ a • y)) ∧ (∀ x, (∀ y, β x y = 1) → x = 0) ∧
    (∀ x, ∃ χ : R → ℂ, (∀ a b, χ (a + b) = χ a * χ b) ∧ ∀ a, φ (a • x) = χ (a * σ a))

section
variable {R : Type} [CommRing R] {σ : R →+* R} {M : Type} [AddCommGroup M] [Module R M]
  {φ : M → ℂ} {β : M → M → ℂ}

theorem isotropic_step [Finite M] (h : IsHerm σ φ β) {X Y : Submodule R M}
    (hY : ∀ y, y ∈ Y ↔ ∀ x ∈ X, β y x = 1) (hX : ∀ x ∈ X, φ x = 1) :
    Nat.card M = Nat.card X * (Nat.card X * Nat.card (Y ⧸ X.submoduleOf Y)) ∧
    ∃ (φ' : (Y ⧸ X.submoduleOf Y) → ℂ) (β' : (Y ⧸ X.submoduleOf Y) → (Y ⧸ X.submoduleOf Y) → ℂ),
      IsHerm σ φ' β' ∧ ∃ n : ℕ, 0 < n ∧ ∑ᶠ x, φ x = n * ∑ᶠ q, φ' q := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  have hc := beta_comm h0 h1
  have hz := beta_zero h0 h1 h2
  have hXY : X ≤ Y := fun x hx => (hY x).2 fun x' hx' => by
    have := h1 x x'
    rwa [hX _ (X.add_mem hx hx'), hX _ hx, hX _ hx', one_mul, one_mul, eq_comm] at this
  have c1 := card_mul_card_orth hc hz h2 h4 hY
  have c2 : Nat.card Y = Nat.card X * Nat.card (Y ⧸ X.submoduleOf Y) := by
    rw [Submodule.card_eq_card_quotient_mul_card (X.submoduleOf Y),
      Nat.card_congr (Submodule.submoduleOfEquivOfLe hXY).toEquiv]
  obtain ⟨Z, hZ⟩ := exists_orth hz h2 h3 Y
  have c3 := card_mul_card_orth hc hz h2 h4 hZ
  have hXZ : X = Z := by
    have hle : X ≤ Z := fun x hx => (hZ x).2 fun y hy => by rw [hc]; exact (hY y).1 hy x hx
    have hcard : Nat.card Z = Nat.card X := by
      rw [← c1, mul_comm] at c3
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos c3
    exact SetLike.coe_injective (Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle hcard.le)
  refine ⟨by rw [← c1, c2], ?_⟩
  let π := (X.submoduleOf Y).mkQ
  have hπ : Function.Surjective π := Submodule.mkQ_surjective _
  have hout : ∀ y : Y, ∃ x ∈ X, ((Quotient.out (π y) : Y) : M) = y + x := fun y =>
    ⟨((Quotient.out (π y) - y : Y) : M),
      (Submodule.Quotient.eq (X.submoduleOf Y)).1 (Quotient.out_eq (π y)), by simp⟩
  let φ' : (Y ⧸ X.submoduleOf Y) → ℂ := fun q => φ (Quotient.out q : Y)
  let β' : (Y ⧸ X.submoduleOf Y) → (Y ⧸ X.submoduleOf Y) → ℂ :=
    fun p q => β (Quotient.out p : Y) (Quotient.out q : Y)
  have hφ : ∀ y : Y, φ' (π y) = φ y := fun y => by
    obtain ⟨x, hx, e⟩ := hout y
    simp only [φ']
    rw [e, h1, hX x hx, (hY y).1 y.2 x hx, mul_one, mul_one]
  have hβ : ∀ y y' : Y, β' (π y) (π y') = β y y' := fun y y' => by
    obtain ⟨x, hx, e⟩ := hout y
    obtain ⟨x', hx', e'⟩ := hout y'
    simp only [β']
    rw [e, h2, hc x, (hY _).1 (Quotient.out (π y') : Y).2 x hx, mul_one, e', hc, h2, hc x',
      (hY y).1 y.2 x' hx', mul_one, hc]
  refine ⟨φ', β', ⟨fun q => h0 _, fun p q => ?_, fun p p' q => ?_, fun a p q => ?_, fun p hp => ?_,
    fun p => ?_⟩, ?_⟩
  · obtain ⟨p, rfl⟩ := hπ p
    obtain ⟨q, rfl⟩ := hπ q
    rw [← map_add, hφ, hφ, hφ, hβ]; exact h1 _ _
  · obtain ⟨p, rfl⟩ := hπ p
    obtain ⟨p', rfl⟩ := hπ p'
    obtain ⟨q, rfl⟩ := hπ q
    rw [← map_add, hβ, hβ, hβ]; exact h2 _ _ _
  · obtain ⟨p, rfl⟩ := hπ p
    obtain ⟨q, rfl⟩ := hπ q
    rw [← map_smul, ← map_smul, hβ, hβ]; exact h3 _ _ _
  · obtain ⟨p, rfl⟩ := hπ p
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change (p : M) ∈ X
    rw [hXZ, hZ]
    intro y hy
    exact (hβ p ⟨y, hy⟩).symm.trans (hp _)
  · obtain ⟨p, rfl⟩ := hπ p
    obtain ⟨χ, hχ, hχ'⟩ := h5 (p : M)
    exact ⟨χ, hχ, fun a => by rw [← map_smul, hφ]; exact hχ' a⟩
  · letI := Fintype.ofFinite M
    haveI : Finite (Y ⧸ X.submoduleOf Y) := Finite.of_surjective _ hπ
    letI := Fintype.ofFinite (Y ⧸ X.submoduleOf Y)
    obtain ⟨n, hn, e⟩ := sum_comp_surj π.toAddMonoidHom hπ φ'
    refine ⟨n, hn, ?_⟩
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← e, sum_eq_sum_orth hc hz h1 h2 hY hX]
    exact Finset.sum_congr rfl fun y _ => (hφ y).symm

theorem split_step [Finite M] (h : IsHerm σ φ β) {X Y : Submodule R M}
    (hY : ∀ y, y ∈ Y ↔ ∀ x ∈ X, β y x = 1) (hd : X ⊓ Y = ⊥) :
    Nat.card M = Nat.card X * Nat.card Y ∧
      IsHerm σ (fun y : Y => φ y) (fun y y' : Y => β y y') ∧
      ∑ᶠ x, φ x = (∑ᶠ x : X, φ x) * ∑ᶠ y : Y, φ y := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  have hc := beta_comm h0 h1
  have hz := beta_zero h0 h1 h2
  have c1 := card_mul_card_orth hc hz h2 h4 hY
  have hinj : Function.Injective (fun p : X × Y => (p.1 : M) + p.2) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ e
    have e' : (a : M) - a' = b' - b := by
      simp only at e
      rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
    have hm : (a : M) - a' ∈ X ⊓ Y := ⟨X.sub_mem a.2 a'.2, e' ▸ Y.sub_mem b'.2 b.2⟩
    rw [hd, Submodule.mem_bot] at hm
    rw [hm] at e'
    exact Prod.ext (Subtype.ext (sub_eq_zero.1 hm)) (Subtype.ext (sub_eq_zero.1 e'.symm).symm)
  have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, c1])
  refine ⟨c1.symm, ⟨fun y => h0 _, fun _ _ => h1 _ _, fun _ _ _ => h2 _ _ _, fun _ _ _ => h3 _ _ _,
    fun y hy => Subtype.ext (h4 _ fun z => ?_), fun y => h5 _⟩, ?_⟩
  · obtain ⟨⟨a, b⟩, rfl⟩ := hbij.2 z
    simp only
    rw [hc, h2, hc a, hc b, (hY _).1 y.2 _ a.2, one_mul]
    exact hy b
  · letI := Fintype.ofFinite M
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← hbij.sum_comp φ, Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [h1, hc, (hY _).1 b.2 _ a.2, mul_one]

end

section
variable {R : Type} [CommRing R] {σ : R →+* R} {M : Type} [AddCommGroup M] [Module R M]
  {φ : M → ℂ} {β : M → M → ℂ}

theorem line_step (h : IsHerm σ φ β) (hσ : ∀ a, σ (σ a) = a) {w : R} (hw : w + σ w = 1) {x : M}
    {P : Ideal R} [hP : P.IsMaximal] [Finite (R ⧸ P)] (hx : ∀ a, a ∈ P ↔ a • x = 0) {a₀ : R}
    (ha : φ (a₀ • x) ≠ 1) :
    (∀ a ∈ P, σ a ∈ P) ∧ β ((a₀ * σ a₀) • x) (w • x) ≠ 1 ∧
      ((∃ a, a - σ a ∉ P) → ∃ m : ℝ, 0 < m ∧ ∑ᶠ q : R ⧸ P, φ (Quotient.out q • x) = -(m : ℂ)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  have hz := beta_zero h0 h1 h2
  obtain ⟨χ, hχ, hχ'⟩ := h5 x
  have hst : ∀ a ∈ P, σ a ∈ P := by
    intro p hp
    by_contra hn
    obtain ⟨c, p', hp', e⟩ := hP.exists_inv hn
    apply ha
    have e1 : a₀ • x = (a₀ * (c * σ p)) • x := by
      rw [mul_smul, eq_sub_of_add_eq e, sub_smul, one_smul, (hx _).1 hp', sub_zero]
    have e2 : (a₀ * (σ c * p)) • x = 0 := (hx _).1 (P.mul_mem_left _ (P.mul_mem_left _ hp))
    rw [e1, hχ', ← phi_zero h0 h1 h2, ← e2, hχ']
    congr 1
    simp only [map_mul, hσ]
    ring
  have hb : ∀ a b : R, β (a • x) (b • x) = χ (a * σ b + σ a * b) := fun a b => by
    have := h1 (a • x) (b • x)
    rw [← add_smul, hχ' (a + b), show (a + b) * σ (a + b) = a * σ a + b * σ b + (a * σ b + σ a * b) by
      rw [map_add]; ring, hχ, hχ, ← hχ', ← hχ'] at this
    exact (mul_left_cancel₀ (mul_ne_zero (h0 _) (h0 _)) this).symm
  have hn : ∀ a : R, β ((a * σ a) • x) (w • x) = φ (a • x) := fun a => by
    rw [hb, hχ']
    congr 1
    rw [map_mul, hσ]
    linear_combination (a * σ a) * hw
  refine ⟨hst, by rwa [hn], fun hne => ?_⟩
  obtain ⟨m, hm, e⟩ := GlobalTheory.NormGauss.finsum_norm_neg R σ P hσ hst hne (fun a => β (a • x) (w • x))
    (fun a b => by rw [add_smul, h2]) (fun a haP => by simp only [(hx a).1 haP, hz])
    ⟨a₀ * σ a₀ * w, by
      have : a₀ * σ a₀ * w + σ (a₀ * σ a₀ * w) = a₀ * σ a₀ := by
        simp only [map_mul, hσ]
        linear_combination (a₀ * σ a₀) * hw
      rwa [this, hn]⟩
  exact ⟨m, hm, by simpa only [hn] using e⟩

end

theorem gauss_sign {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) {w : R}
    (hw : w + σ w = 1) (s : ℕ → ℂ) (s1 : s 1 = 1) (ssq : ∀ n, s n * s n = 1)
    (smul : ∀ (A B : Type) [AddCommGroup A] [Module R A] [Finite A] [AddCommGroup B] [Module R B]
      [Finite B], s (Nat.card A * Nat.card B) = s (Nat.card A) * s (Nat.card B))
    (sP : ∀ P : Ideal R, P.IsMaximal → (∀ a ∈ P, σ a ∈ P) →
      s (Nat.card (R ⧸ P)) = -1 ∧ ∃ a, a - σ a ∉ P) (n : ℕ) :
    ∀ (M : Type) [AddCommGroup M] [Module R M] [Finite M] (φ : M → ℂ) (β : M → M → ℂ),
      Nat.card M = n → IsHerm σ φ β → ∃ r : ℝ, 0 < r ∧ ∑ᶠ x, φ x = s (Nat.card M) * (r : ℂ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ φ β hn h
  have h' := h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h'
  have hc := beta_comm h0 h1
  have hz := beta_zero h0 h1 h2
  rcases eq_bot_or_exists_atom_le (⊤ : Submodule R M) with htop | ⟨X, hX, -⟩
  · haveI : Subsingleton M := ⟨fun a b => by
      have ha : a - b ∈ (⊤ : Submodule R M) := trivial
      rwa [htop, Submodule.mem_bot, sub_eq_zero] at ha⟩
    haveI : Unique M := uniqueOfSubsingleton 0
    refine ⟨1, one_pos, ?_⟩
    rw [finsum_unique, Nat.card_unique, s1, Subsingleton.elim default (0 : M), phi_zero h0 h1 h2]
    simp
  obtain ⟨Y, hY⟩ := exists_orth hz h2 h3 X
  have hX1 : 1 < Nat.card X :=
    Finite.one_lt_card_iff_nontrivial.2 (Submodule.nontrivial_iff_ne_bot.2 hX.1)
  by_cases hφ : ∀ x ∈ X, φ x = 1
  · obtain ⟨c, φ', β', h', k, hk, e⟩ := isotropic_step h hY hφ
    haveI : Finite (Y ⧸ X.submoduleOf Y) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
    have hq : 0 < Nat.card (Y ⧸ X.submoduleOf Y) := Nat.card_pos
    obtain ⟨r, hr, e'⟩ := ih _ (by rw [← hn, c]; nlinarith [Nat.mul_pos hq (zero_lt_one.trans hX1)])
      _ φ' β' rfl h'
    refine ⟨k * r, by positivity, ?_⟩
    rw [e, e', c, ← Nat.card_prod, smul, Nat.card_prod, smul, ← mul_assoc (s _), ssq]
    push_cast
    ring
  · push_neg at hφ
    obtain ⟨x, hxX, hx1⟩ := hφ
    have hx0 : x ≠ 0 := by rintro rfl; exact hx1 (phi_zero h0 h1 h2)
    let f := LinearMap.toSpanSingleton R M x
    have hr : LinearMap.range f = X := by
      refine (hX.le_iff.1 ?_).resolve_left fun hb => hx0 ?_
      · rintro _ ⟨a, rfl⟩
        exact X.smul_mem a hxX
      · have : x ∈ LinearMap.range f := ⟨1, one_smul _ _⟩
        rwa [hb, Submodule.mem_bot] at this
    let P : Ideal R := LinearMap.ker f
    let e : (R ⧸ P) ≃ₗ[R] X := f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr)
    have he : ∀ q : R ⧸ P, ((e q : X) : M) = Quotient.out q • x := fun q => by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    haveI : IsSimpleModule R X := isSimpleModule_iff_isAtom.2 hX
    haveI : P.IsMaximal := Ideal.isMaximal_def.2 (isSimpleModule_iff_isCoatom.1 (IsSimpleModule.congr e))
    haveI : Finite (R ⧸ P) := Finite.of_equiv _ e.toEquiv.symm
    obtain ⟨hst, hnd, hsum⟩ := line_step h hσ hw (x := x) (P := P) (a₀ := 1) (fun a => Iff.rfl)
      (by rwa [one_smul])
    obtain ⟨hs, hne⟩ := sP P inferInstance hst
    obtain ⟨m, hm, hsum⟩ := hsum hne
    have hd : X ⊓ Y = ⊥ := (hX.le_iff.1 inf_le_left).resolve_right fun hh => hnd
      ((hY _).1 (inf_eq_left.1 hh (X.smul_mem _ hxX)) _ (X.smul_mem _ hxX))
    obtain ⟨c, h', e1⟩ := split_step h hY hd
    have hq : 0 < Nat.card Y := Nat.card_pos
    obtain ⟨r, hr, e'⟩ := ih _ (by rw [← hn, c]; nlinarith) Y _ _ rfl h'
    refine ⟨m * r, by positivity, ?_⟩
    have e2 : ∑ᶠ x : X, φ x = -(m : ℂ) := by
      rw [← hsum, ← finsum_comp_equiv e.toEquiv]
      exact finsum_congr fun q => congrArg φ (he q)
    rw [e1, e', e2, c, smul, ← Nat.card_congr e.toEquiv, hs]
    push_cast
    ring

theorem gauss_sum_sign : ∀ (D : D7) (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M] (φ : M → ℂ) (β : M → M → ℂ), (∀ x, φ x ≠ 0) → (∀ x y, φ (x + y) = φ x * φ y * β x y) → (∀ x x' y, β (x + x') y = β x y * β x' y) → (∀ (a : 𝓞 D.host.E) x y, β (a • x) y = β x (GlobalTheory.InertSign.sgO D a • y)) → (∀ x, (∀ y, β x y = 1) → x = 0) → (∀ x, ∃ χ : 𝓞 D.host.E → ℂ, (∀ a b, χ (a + b) = χ a * χ b) ∧ ∀ a, φ (a • x) = χ (a * GlobalTheory.InertSign.sgO D a)) → ∃ r : ℝ, 0 < r ∧ ∑ᶠ x, φ x = sgn D (Nat.card M) * (r : ℂ) := by
  intro D M _ _ _ φ β h0 h1 h2 h3 h4 h5
  obtain ⟨w, hw, -⟩ := GlobalTheory.TraceOne.exists_trace_one D 2 Nat.prime_two
  refine gauss_sign (GlobalTheory.InertSign.sgO D) (GlobalTheory.InertSign.sgO_sgO D) hw (sgn D) sgn_one sgn_mul_self
    (fun A B _ _ _ _ _ _ => sgn_mul (GlobalTheory.T.finite_module_sign_eq_neg_one_pow_length D A).1 (GlobalTheory.T.finite_module_sign_eq_neg_one_pow_length D B).1 Nat.card_pos.ne'
      Nat.card_pos.ne') (fun P hP hst => ?_) _ M φ β rfl ⟨h0, h1, h2, h3, h4, h5⟩
  have hfix : D.host.conj • P = P := by
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.2 fun a ha => hst a ha
    · intro a ha
      have := Ideal.mem_map_of_mem (GlobalTheory.InertSign.sgO D) (hst a ha)
      rwa [GlobalTheory.InertSign.sgO_sgO] at this
  obtain ⟨hs, q, -, hq, -, -, hqP, -⟩ := (GlobalTheory.T.absNorm_cmPrime_inertPrime_sign D P hP).2.1 hfix
  obtain ⟨v, -, hv⟩ := GlobalTheory.TraceOne.exists_trace_one D q hq
  refine ⟨?_, v, hv P hP.isPrime hqP⟩
  rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hs

end GlobalTheory.HermGauss
