import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrob

set_option autoImplicit false

noncomputable section

open GlobalTheory.RingChain GlobalTheory.PerfdLat GlobalTheory.RingChain.FrobLin Matrix
open scoped TensorProduct Pointwise

namespace GlobalTheory.RingChain.MatFrob

variable {A : Type} [CommRing A] {p : ℕ} {m r m₂ r₂ : ℕ}

theorem semi_mk {q : ℕ} {P : Type} [AddCommGroup P] [Module A P] (S : Submodule A (Fin m → A))
    (τ : ((Fin m → A) ⧸ S) →+ P) (hτ : ∀ (a : A) x, τ (a • x) = a ^ q • τ x) (x : Fin m → A) :
    τ (Submodule.Quotient.mk x) = ∑ i, x i ^ q • τ (Submodule.Quotient.mk (Pi.single i 1)) := by
  have : (Submodule.Quotient.mk x : (Fin m → A) ⧸ S) = ∑ i, x i • Submodule.Quotient.mk (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    change S.mkQ _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun i _ => hτ _ _

theorem exists_semi [Fact p.Prime] (k : ℕ) {P : Type} [AddCommGroup P] [Module A P] (R : Matrix (Fin m) (Fin r) A)
    (hp : ∀ y : P, (p : A) • y = 0) (v : Fin m → P) (hv : ∀ j, ∑ i, R i j ^ p ^ k • v i = 0) :
    ∃ τ : ((Fin m → A) ⧸ LinearMap.range (Matrix.mulVecLin R)) →+ P,
      ∀ x, τ (Submodule.Quotient.mk x) = ∑ i, x i ^ p ^ k • v i := by
  let φ : (Fin m → A) →+ P := AddMonoidHom.mk' (fun x => ∑ i, x i ^ p ^ k • v i) fun x y => by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨c, hc⟩ := exists_add_pow_prime_pow_eq (Fact.out : p.Prime) (x i) (y i) k
    rw [Pi.add_apply, hc, add_smul, add_smul]
    simp only [mul_assoc, mul_smul (p : A), hp, add_zero]
  have hφ : ∀ x, φ x = ∑ i, x i ^ p ^ k • v i := fun _ => rfl
  refine ⟨QuotientAddGroup.lift (LinearMap.range (Matrix.mulVecLin R)).toAddSubgroup φ ?_, fun x => rfl⟩
  rintro _ ⟨c, rfl⟩
  have : Matrix.mulVecLin R c = ∑ j, fun i => c j * R i j := by
    funext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [AddMonoidHom.mem_ker, this, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hφ]
  simp only [mul_pow, mul_smul]
  rw [← Finset.smul_sum, hv, smul_zero]

theorem rel_semi {q : ℕ} {P : Type} [AddCommGroup P] [Module A P] (R : Matrix (Fin m) (Fin r) A)
    (τ : ((Fin m → A) ⧸ LinearMap.range (Matrix.mulVecLin R)) →+ P) (hτ : ∀ (a : A) x, τ (a • x) = a ^ q • τ x) (j : Fin r) :
    ∑ i, R i j ^ q • τ (Submodule.Quotient.mk (Pi.single i 1)) = 0 := by
  have : (fun i => R i j) ∈ LinearMap.range (Matrix.mulVecLin R) := ⟨Pi.single j 1, funext fun i => by simp⟩
  rw [← semi_mk _ τ hτ (fun i => R i j), (Submodule.Quotient.mk_eq_zero _).2 this, map_zero]

theorem mk_mulVec (S : Submodule A (Fin m₂ → A)) (U : Matrix (Fin m₂) (Fin m) A) (x : Fin m → A) :
    (Submodule.Quotient.mk (U *ᵥ x) : (Fin m₂ → A) ⧸ S) = ∑ i, x i • Submodule.Quotient.mk (fun l => U l i) := by
  have : U *ᵥ x = ∑ i, x i • fun l => U l i := by
    funext l
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [this]
  change S.mkQ _ = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul _ _ _

theorem univ_of_mat [Fact p.Prime] (k : ℕ) (R₁ : Matrix (Fin m) (Fin r) A) (R₂ : Matrix (Fin m₂) (Fin r₂) A)
    (U : Matrix (Fin m₂) (Fin m) A) (V : Matrix (Fin m) (Fin m₂) A) (C₁ : Matrix (Fin r₂) (Fin m₂) A)
    (C₂ : Matrix (Fin r₂) (Fin r) A) (C₃ : Matrix (Fin r₂) (Fin m₂) A) (C₄ : Matrix (Fin r) (Fin r₂) A)
    (C₅ : Matrix (Fin m) (Fin r₂) A) (C₆ : Matrix (Fin r) (Fin m) A) (C₇ : Matrix (Fin m) (Fin m) A)
    (h₁ : R₂ * C₁ = (p : A) • (1 : Matrix (Fin m₂) (Fin m₂) A)) (h₂ : R₂ * C₂ = U * R₁.map (· ^ p ^ k))
    (h₃ : R₂ * C₃ = U * V - 1) (h₄ : R₁.map (· ^ p ^ k) * C₄ + (p : A) • C₅ = V * R₂)
    (h₅ : R₁.map (· ^ p ^ k) * C₆ + (p : A) • C₇ = V * U - 1) :
    ∃ ψ : ((Fin m → A) ⧸ LinearMap.range (Matrix.mulVecLin R₁)) →+ ((Fin m₂ → A) ⧸ LinearMap.range (Matrix.mulVecLin R₂)),
      Univ A p (p ^ k) ψ ∧ ∀ x, ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (U *ᵥ fun i => x i ^ p ^ k) := by
  have hp : ∀ y : (Fin m₂ → A) ⧸ LinearMap.range (Matrix.mulVecLin R₂), (p : A) • y = 0 := fun y => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨C₁ *ᵥ y, by rw [mulVecLin_apply, mulVec_mulVec, h₁, smul_mulVec, one_mulVec]⟩
  obtain ⟨ψ, hψ⟩ := exists_semi k R₁ hp (fun i => Submodule.Quotient.mk fun l => U l i) fun j => by
    rw [← mk_mulVec _ U (fun i => R₁ i j ^ p ^ k), Submodule.Quotient.mk_eq_zero]
    refine ⟨C₂ *ᵥ Pi.single j 1, ?_⟩
    rw [mulVecLin_apply, mulVec_mulVec, h₂, ← mulVec_mulVec]
    congr 1
    funext i
    simp
  have hψ' : ∀ x, ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (U *ᵥ fun i => x i ^ p ^ k) := fun x => by
    rw [hψ, mk_mulVec]
  have hq : p ^ k ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have he : ∀ i, ψ (Submodule.Quotient.mk (Pi.single i 1)) = Submodule.Quotient.mk fun l => U l i := fun i => by
    rw [hψ, Finset.sum_eq_single i (fun j _ h => by simp [h, zero_pow hq]) (by simp)]
    simp
  have hUV : ∀ y, (Submodule.Quotient.mk (U *ᵥ (V *ᵥ y)) : (Fin m₂ → A) ⧸ LinearMap.range (Matrix.mulVecLin R₂)) =
      Submodule.Quotient.mk y := fun y => by
    rw [Submodule.Quotient.eq]
    exact ⟨C₃ *ᵥ y, by rw [mulVecLin_apply, mulVec_mulVec, h₃, sub_mulVec, one_mulVec, mulVec_mulVec]⟩
  refine ⟨ψ, ⟨hp, fun a x => ?_, eq_top_iff.2 fun y _ => ?_, fun P _ _ τ hP hτ => ?_⟩, hψ'⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, hψ, hψ, Finset.smul_sum]
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, mul_smul]
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← hUV, mk_mulVec]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, he i⟩)
  · let L : (Fin m → A) →ₗ[A] P := Fintype.linearCombination A fun i => τ (Submodule.Quotient.mk (Pi.single i 1))
    have hL : ∀ x, L x = ∑ i, x i • τ (Submodule.Quotient.mk (Pi.single i 1)) := fun x =>
      Fintype.linearCombination_apply _ _ _
    have hK : ∀ {n : ℕ} (C : Matrix (Fin r) (Fin n) A) (D : Matrix (Fin m) (Fin n) A) (c : Fin n → A),
        L ((R₁.map (· ^ p ^ k) * C + (p : A) • D) *ᵥ c) = 0 := fun C D c => by
      rw [add_mulVec, smul_mulVec, map_add, map_smul, hP, add_zero, ← mulVec_mulVec]
      generalize C *ᵥ c = d
      have : R₁.map (· ^ p ^ k) *ᵥ d = ∑ j, d j • fun i => R₁ i j ^ p ^ k := by
        funext l
        simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [this, map_sum]
      exact Finset.sum_eq_zero fun j _ => by rw [map_smul, hL, rel_semi R₁ τ hτ, smul_zero]
    refine ⟨Submodule.liftQ _ (L ∘ₗ V.mulVecLin) ?_, fun x => ?_⟩
    · rintro _ ⟨c, rfl⟩
      have := hK C₄ C₅ c
      rwa [h₄, ← mulVec_mulVec] at this
    · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have := hK C₆ C₇ fun i => x i ^ p ^ k
      rw [h₅, sub_mulVec, one_mulVec, map_sub, sub_eq_zero, ← mulVec_mulVec] at this
      rw [hψ', Submodule.liftQ_apply, semi_mk _ τ hτ, ← hL]
      exact this

theorem exists_mul {n : ℕ} (R : Matrix (Fin m) (Fin r) A) (X : Matrix (Fin m) (Fin n) A)
    (h : ∀ c, X *ᵥ c ∈ LinearMap.range (Matrix.mulVecLin R)) : ∃ C, R * C = X := by
  choose c hc using fun j => h (Pi.single j 1)
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext i j
  exact (congrFun (hc j) i).trans (by simp)

theorem exists_mul_add {n : ℕ} (a : A) (R : Matrix (Fin m) (Fin r) A) (X : Matrix (Fin m) (Fin n) A)
    (h : ∀ c, X *ᵥ c ∈ LinearMap.range (Matrix.mulVecLin R) ⊔ a • ⊤) : ∃ C D, R * C + a • D = X := by
  have : ∀ j, ∃ c d, R *ᵥ c + a • d = X *ᵥ Pi.single j 1 := fun j => by
    obtain ⟨_, ⟨c, rfl⟩, y, hy, e⟩ := Submodule.mem_sup.1 (h (Pi.single j 1))
    obtain ⟨d, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    exact ⟨c, d, e⟩
  choose c d hc using this
  refine ⟨Matrix.of fun i j => c j i, Matrix.of fun i j => d j i, ?_⟩
  ext i j
  exact (congrFun (hc j) i).trans (by simp)

theorem mat_of_univ [Fact p.Prime] (k : ℕ) (R₁ : Matrix (Fin m) (Fin r) A) (R₂ : Matrix (Fin m₂) (Fin r₂) A)
    (ψ : ((Fin m → A) ⧸ LinearMap.range (Matrix.mulVecLin R₁)) →+ ((Fin m₂ → A) ⧸ LinearMap.range (Matrix.mulVecLin R₂)))
    (h : Univ A p (p ^ k) ψ) :
    ∃ (U : Matrix (Fin m₂) (Fin m) A) (V : Matrix (Fin m) (Fin m₂) A) (C₁ : Matrix (Fin r₂) (Fin m₂) A)
    (C₂ : Matrix (Fin r₂) (Fin r) A) (C₃ : Matrix (Fin r₂) (Fin m₂) A) (C₄ : Matrix (Fin r) (Fin r₂) A)
    (C₅ : Matrix (Fin m) (Fin r₂) A) (C₆ : Matrix (Fin r) (Fin m) A) (C₇ : Matrix (Fin m) (Fin m) A),
    R₂ * C₁ = (p : A) • (1 : Matrix (Fin m₂) (Fin m₂) A) ∧ R₂ * C₂ = U * R₁.map (· ^ p ^ k) ∧
    R₂ * C₃ = U * V - 1 ∧ R₁.map (· ^ p ^ k) * C₄ + (p : A) • C₅ = V * R₂ ∧
    R₁.map (· ^ p ^ k) * C₆ + (p : A) • C₇ = V * U - 1 ∧
      ∀ x, ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (U *ᵥ fun i => x i ^ p ^ k) := by
  obtain ⟨hp, hs, hsp, hU⟩ := h
  choose u hu using fun i : Fin m => Submodule.Quotient.mk_surjective _ (ψ (Submodule.Quotient.mk (Pi.single i 1)))
  let U : Matrix (Fin m₂) (Fin m) A := Matrix.of fun l i => u i l
  have hUx : ∀ x, (Submodule.Quotient.mk (U *ᵥ x) : (Fin m₂ → A) ⧸ LinearMap.range (Matrix.mulVecLin R₂)) =
      ∑ i, x i • ψ (Submodule.Quotient.mk (Pi.single i 1)) := fun x => by
    rw [mk_mulVec]
    exact Finset.sum_congr rfl fun i _ => congrArg _ (hu i)
  have hψ : ∀ x, ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (U *ᵥ fun i => x i ^ p ^ k) := fun x => by
    rw [hUx, semi_mk _ ψ hs]
  have hsurj : ∀ y : (Fin m₂ → A) ⧸ LinearMap.range (Matrix.mulVecLin R₂), ∃ x, Submodule.Quotient.mk (U *ᵥ x) = y :=
    fun y => by
      have : Submodule.span A (Set.range ψ) ≤ LinearMap.range (Submodule.mkQ _ ∘ₗ U.mulVecLin) := by
        rw [Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        exact ⟨_, (hψ x).symm⟩
      exact this (hsp ▸ Submodule.mem_top)
  choose v hv using fun l : Fin m₂ => hsurj (Submodule.Quotient.mk (Pi.single l 1))
  let V : Matrix (Fin m) (Fin m₂) A := Matrix.of fun i l => v l i
  have hUV : ∀ y, (Submodule.Quotient.mk (U *ᵥ (V *ᵥ y)) : (Fin m₂ → A) ⧸ LinearMap.range (Matrix.mulVecLin R₂)) =
      Submodule.Quotient.mk y := fun y => by
    rw [mulVec_mulVec, mk_mulVec]
    conv_rhs => rw [← one_mulVec y, mk_mulVec]
    refine Finset.sum_congr rfl fun l _ => congrArg _ ?_
    refine Eq.trans ?_ ((hv l).trans ?_)
    · rfl
    · congr 1
      funext i
      simp [Matrix.one_apply, Pi.single_apply]
  let K : Submodule A (Fin m → A) := LinearMap.range (Matrix.mulVecLin (R₁.map (· ^ p ^ k))) ⊔ (p : A) • ⊤
  have hK : ∀ y : (Fin m → A) ⧸ K, (p : A) • y = 0 := fun y => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_right (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  have h1 : ∀ x : Fin m → A, ∑ i, x i • (Submodule.Quotient.mk (Pi.single i 1) : (Fin m → A) ⧸ K) =
      Submodule.Quotient.mk x := fun x => by
    simpa using (semi_mk (q := 1) K (AddMonoidHom.id _) (by simp) x).symm
  obtain ⟨τ, hτ⟩ := exists_semi k R₁ hK (fun i => Submodule.Quotient.mk (Pi.single i 1)) fun j => by
    rw [h1 fun i => R₁ i j ^ p ^ k, Submodule.Quotient.mk_eq_zero]
    refine Submodule.mem_sup_left ⟨Pi.single j 1, ?_⟩
    funext i
    simp
  have hq : p ^ k ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  obtain ⟨g, hg⟩ := hU _ τ hK fun a x => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, hτ, hτ, Finset.smul_sum]
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, mul_smul]
  have hker : ∀ x, (Submodule.Quotient.mk (U *ᵥ x) : (Fin m₂ → A) ⧸ LinearMap.range (Matrix.mulVecLin R₂)) = 0 →
      x ∈ K := fun x hx => by
    rw [← Submodule.Quotient.mk_eq_zero, ← h1, ← map_zero g, ← hx, hUx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hg, hτ, Finset.sum_eq_single i (fun j _ h => by simp [h, zero_pow hq]) (by simp)]
    simp
  obtain ⟨C₁, h₁⟩ := exists_mul R₂ ((p : A) • (1 : Matrix (Fin m₂) (Fin m₂) A)) fun c => by
    rw [← Submodule.Quotient.mk_eq_zero, smul_mulVec, Submodule.Quotient.mk_smul, hp]
  obtain ⟨C₂, h₂⟩ := exists_mul R₂ (U * R₁.map (· ^ p ^ k)) fun c => by
    rw [← Submodule.Quotient.mk_eq_zero, mk_mulVec]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : (fun l => (U * R₁.map (· ^ p ^ k)) l j) = U *ᵥ fun i => R₁ i j ^ p ^ k := rfl
    rw [this, hUx, rel_semi R₁ ψ hs, smul_zero]
  obtain ⟨C₃, h₃⟩ := exists_mul R₂ (U * V - 1) fun c => by
    rw [sub_mulVec, one_mulVec, ← Submodule.Quotient.eq, ← mulVec_mulVec, hUV]
  obtain ⟨C₄, C₅, h₄⟩ := exists_mul_add (p : A) (R₁.map (· ^ p ^ k)) (V * R₂) fun c => hker _ (by
    rw [← mulVec_mulVec, hUV, Submodule.Quotient.mk_eq_zero]
    exact ⟨c, rfl⟩)
  obtain ⟨C₆, C₇, h₅⟩ := exists_mul_add (p : A) (R₁.map (· ^ p ^ k)) (V * U - 1) fun c => hker _ (by
    rw [sub_mulVec, one_mulVec, mulVec_sub, Submodule.Quotient.mk_sub, ← mulVec_mulVec, hUV, sub_self])
  exact ⟨U, V, C₁, C₂, C₃, C₄, C₅, C₆, C₇, h₁, h₂, h₃, h₄, h₅, hψ⟩

def ent {B : Type} {a b : ℕ} (X : Matrix (Fin a) (Fin b) B) : Set B := Set.range fun z : Fin a × Fin b => X z.1 z.2

theorem exists_map {A' B : Type} {a b : ℕ} (g : A' → B) (X : Matrix (Fin a) (Fin b) B) (h : ent X ⊆ Set.range g) :
    ∃ X' : Matrix (Fin a) (Fin b) A', X'.map g = X := by
  choose x hx using fun i j => h ⟨(i, j), rfl⟩
  exact ⟨Matrix.of x, Matrix.ext hx⟩

theorem main : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ) (B : Type) [CommRing B] (m₁ r₁ m₂ r₂ : ℕ) (R₁ : Matrix (Fin m₁) (Fin r₁) B) (R₂ : Matrix (Fin m₂) (Fin r₂) B) (ψ : ((Fin m₁ → B) ⧸ LinearMap.range (Matrix.mulVecLin R₁)) →+ ((Fin m₂ → B) ⧸ LinearMap.range (Matrix.mulVecLin R₂))), IsFrobLin B p (p ^ k) ψ → ∃ T : Set B, T.Finite ∧ ∀ (A' : Type) [CommRing A'] (g : A' →+* B), Function.Injective g → T ⊆ Set.range g → ∀ (R₁' : Matrix (Fin m₁) (Fin r₁) A') (R₂' : Matrix (Fin m₂) (Fin r₂) A'), R₁'.map g = R₁ → R₂'.map g = R₂ → ∃ ψ' : ((Fin m₁ → A') ⧸ LinearMap.range (Matrix.mulVecLin R₁')) →+ ((Fin m₂ → A') ⧸ LinearMap.range (Matrix.mulVecLin R₂')), IsFrobLin A' p (p ^ k) ψ' ∧ ∀ x y, ψ' (Submodule.Quotient.mk x) = Submodule.Quotient.mk y → ψ (Submodule.Quotient.mk (piMap g _ x)) = Submodule.Quotient.mk (piMap g _ y) := by
  intro p _ k B _ m₁ r₁ m₂ r₂ R₁ R₂ ψ h
  obtain ⟨U, V, C₁, C₂, C₃, C₄, C₅, C₆, C₇, h₁, h₂, h₃, h₄, h₅, hψ⟩ := mat_of_univ k R₁ R₂ ψ ((iff_univ' k ψ).1 h)
  refine ⟨ent U ∪ ent V ∪ ent C₁ ∪ ent C₂ ∪ ent C₃ ∪ ent C₄ ∪ ent C₅ ∪ ent C₆ ∪ ent C₇, by
    simp only [Set.finite_union, ent, Set.finite_range, and_self], fun A' _ g hg hT R₁' R₂' e₁ e₂ => ?_⟩
  simp only [Set.union_subset_iff] at hT
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨tU, tV⟩, t₁⟩, t₂⟩, t₃⟩, t₄⟩, t₅⟩, t₆⟩, t₇⟩ := hT
  obtain ⟨U, rfl⟩ := exists_map g U tU
  obtain ⟨V, rfl⟩ := exists_map g V tV
  obtain ⟨C₁, rfl⟩ := exists_map g C₁ t₁
  obtain ⟨C₂, rfl⟩ := exists_map g C₂ t₂
  obtain ⟨C₃, rfl⟩ := exists_map g C₃ t₃
  obtain ⟨C₄, rfl⟩ := exists_map g C₄ t₄
  obtain ⟨C₅, rfl⟩ := exists_map g C₅ t₅
  obtain ⟨C₆, rfl⟩ := exists_map g C₆ t₆
  obtain ⟨C₇, rfl⟩ := exists_map g C₇ t₇
  subst e₁ e₂
  have inj : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) A'), (∀ i j, g (X i j) = g (Y i j)) → X = Y :=
    fun X Y e => Matrix.ext fun i j => hg (e i j)
  obtain ⟨ψ', hu, hψ'⟩ := univ_of_mat (p := p) k R₁' R₂' U V C₁ C₂ C₃ C₄ C₅ C₆ C₇
    (inj _ _ fun i j => by simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite g] using congrFun₂ h₁ i j)
    (inj _ _ fun i j => by simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite g] using congrFun₂ h₂ i j)
    (inj _ _ fun i j => by simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite g] using congrFun₂ h₃ i j)
    (inj _ _ fun i j => by simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite g] using congrFun₂ h₄ i j)
    (inj _ _ fun i j => by simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite g] using congrFun₂ h₅ i j)
  refine ⟨ψ', (iff_univ' k ψ').2 hu, fun x y e => ?_⟩
  rw [hψ', Submodule.Quotient.eq] at e
  obtain ⟨c, hc⟩ := e
  rw [hψ, Submodule.Quotient.eq]
  refine ⟨fun j => g (c j), funext fun i => ?_⟩
  have := congrArg g (congrFun hc i)
  have hx : ∀ {n : ℕ} (z : Fin n → A') (l : Fin n), piMap g _ z l = g (z l) := fun _ _ => rfl
  simpa [Matrix.mulVec, dotProduct, hx] using this

end GlobalTheory.RingChain.MatFrob

end
