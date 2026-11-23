import Mathlib

noncomputable section

open NumberField Complex
open scoped nonZeroDivisors ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

variable (F : Type) [Field F] [NumberField F]

abbrev Emb : Type := F →+* ℝ

abbrev Frac : Type := (FractionalIdeal (𝓞 F)⁰ F)ˣ

def upperHalf : Set (Emb F → ℂ) := {z | ∀ τ, 0 < (z τ).im}

def dF : ℝ := |(discr F : ℝ)|

variable {F}

def latM (𝔞 : Frac F) : FractionalIdeal (𝓞 F)⁰ F :=
  ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (↑𝔞⁻¹ : FractionalIdeal (𝓞 F)⁰ F)

def nrm (𝔞 : Frac F) : ℝ := (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℝ)

open NumberField Complex in
open scoped nonZeroDivisors ContDiff in
variable (F : Type) [Field F] [NumberField F] in
variable {F} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual (𝔞 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 =
      FractionalIdeal.dual ℤ ℚ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
  rw [FractionalIdeal.dual_eq_mul_inv ℤ ℚ, coeIdeal_differentIdeal ℤ ℚ F (𝓞 F), inv_inv,
    Units.val_inv_eq_inv_val]

open NumberField Complex in
open scoped nonZeroDivisors ContDiff in
variable (F : Type) [Field F] [NumberField F] in
variable {F} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.unit_inv_mul (ε : (𝓞 F)ˣ) :
    (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((ε : 𝓞 F) : F) = 1 := by
  norm_cast; simp

def latPt (z : Emb F → ℂ) (p : F × F) : Emb F → ℂ :=
  fun τ => 2 * (Real.pi : ℂ) * I * ((τ p.1 : ℂ) + (τ p.2 : ℂ) * z τ)

def LatPair (𝔞 𝔟 : Frac F) : Type :=
  {p : F × F // p.1 ∈ latM 𝔞 ∧ p.2 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ p ≠ 0}

def latRel (𝔞 𝔟 : Frac F) : Setoid (LatPair 𝔞 𝔟) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1.1 = ((ε : 𝓞 F) : F) * p.1.1 ∧ q.1.2 = ((ε : 𝓞 F) : F) * p.1.2
  iseqv :=
    { refl := fun _ => ⟨1, by simp, by simp⟩
      symm := fun {p q} ⟨ε, h1, h2⟩ => ⟨ε⁻¹, by
          rw [h1, ← mul_assoc, unit_inv_mul, one_mul], by
          rw [h2, ← mul_assoc, unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h1, h2⟩ ⟨ε', h1', h2'⟩ => ⟨ε' * ε, by
          rw [h1', h1, ← mul_assoc]; simp, by
          rw [h2', h2, ← mul_assoc]; simp⟩ }

def eisTerm (k : ℕ) (σ : ℂ) (z : Emb F → ℂ) (p : F × F) : ℂ :=
  (∏ τ, latPt z p τ)⁻¹ ^ k * ((‖∏ τ, latPt z p τ‖ : ℝ) : ℂ) ^ (-2 * σ)

def eisClass (𝔞 𝔟 : Frac F) (k : ℕ) (σ : ℂ) (z : Emb F → ℂ) (c : Quotient (latRel 𝔞 𝔟)) : ℂ :=
  eisTerm k σ z c.out.1

def eisSum (𝔞 𝔟 : Frac F) (k : ℕ) (σ : ℂ) (z : Emb F → ℂ) : ℂ := ∑' c, eisClass 𝔞 𝔟 k σ z c

def QPair (𝔞 𝔟 : Frac F) : Type :=
  {p : F × F // p.1 ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ p.2 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧
    ∀ τ : Emb F, 0 < τ (p.1 * p.2)}

def qRel (𝔞 𝔟 : Frac F) : Setoid (QPair 𝔞 𝔟) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1.1 = (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * p.1.1 ∧ q.1.2 = ((ε : 𝓞 F) : F) * p.1.2
  iseqv :=
    { refl := fun _ => ⟨1, by simp, by simp⟩
      symm := fun {p q} ⟨ε, h1, h2⟩ => ⟨ε⁻¹, by
          rw [h1, inv_inv, ← mul_assoc, mul_comm ((ε : 𝓞 F) : F), unit_inv_mul, one_mul], by
          rw [h2, ← mul_assoc, unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h1, h2⟩ ⟨ε', h1', h2'⟩ => ⟨ε' * ε, by
          rw [h1', h1, ← mul_assoc, mul_inv]; simp, by
          rw [h2', h2, ← mul_assoc]; simp⟩ }

def qPow (ξ : F) (z : Emb F → ℂ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I * ∑ τ, (τ ξ : ℂ) * z τ)

def qTerm (𝔞 : Frac F) (k : ℕ) (z : Emb F → ℂ) (p : F × F) : ℂ :=
  (((|(Algebra.norm ℚ p.1 : ℝ)| / nrm 𝔞) ^ (k - 1) : ℝ) : ℂ) * qPow (p.1 * p.2) z

def qClass (𝔞 𝔟 : Frac F) (k : ℕ) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : ℂ := qTerm 𝔞 k z c.out.1

def IsPartialZeta (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re →
    HasSum (fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} =>
      ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s)) (Z s)

def cK (F : Type) [Field F] [NumberField F] (k : ℕ) : ℝ :=
  ((k - 1).factorial : ℝ) ^ Module.finrank ℚ F * dF F ^ (((k : ℝ) - 1) / 2)

def omegaFactor (𝔞 : Frac F) : ℝ := dF F ^ ((1 : ℝ) / 2) * nrm 𝔞

def HasExpansion (𝔞 𝔟 : Frac F) (k : ℕ) (g : (Emb F → ℂ) → ℂ) : Prop :=
  ∃ Z : ℂ → ℂ, IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧ ∀ z ∈ upperHalf F,
    Summable (qClass 𝔞 𝔟 k z) ∧
      (cK F k : ℂ) * g z / (omegaFactor 𝔞 : ℂ) ^ k =
        (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) + ∑' c, qClass 𝔞 𝔟 k z c

open Classical in

def wirt {Φ : Type} [Fintype Φ] (τ : Φ) (bar : Bool) (g : (Φ → ℂ) → ℂ) : (Φ → ℂ) → ℂ := fun z =>
  (fderiv ℝ g z (Pi.single τ 1) + (if bar then I else -I) * fderiv ℝ g z (Pi.single τ I)) / 2

def wirtWord {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (g : (Φ → ℂ) → ℂ) : (Φ → ℂ) → ℂ :=
  ws.foldr (fun w h => wirt w.1 w.2 h) g

theorem wirtWord_nil {Φ : Type} [Fintype Φ] (g : (Φ → ℂ) → ℂ) : wirtWord [] g = g := rfl

theorem wirtWord_cons {Φ : Type} [Fintype Φ] (w : Φ × Bool) (ws : List (Φ × Bool)) (g : (Φ → ℂ) → ℂ) :
    wirtWord (w :: ws) g = wirt w.1 w.2 (wirtWord ws g) := rfl

def halfPlane : Set ℂ := {σ | -1 / 2 < σ.re}

def IsContinuation (𝔞 𝔟 : Frac F) (G : ℂ → (Emb F → ℂ) → ℂ) : Prop :=
  (∀ σ : ℂ, 0 < σ.re → ∀ z ∈ upperHalf F, Summable (eisClass 𝔞 𝔟 2 σ z) ∧ G σ z = eisSum 𝔞 𝔟 2 σ z) ∧
  (∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (G σ) (upperHalf F)) ∧
  (∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) z) halfPlane)

def HeckeWeightTwo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ 𝔞 𝔟 : Frac F,
    ∃ G : ℂ → (Emb F → ℂ) → ℂ, IsContinuation 𝔞 𝔟 G ∧
      DifferentiableOn ℂ (G 0) (upperHalf F) ∧ HasExpansion 𝔞 𝔟 2 (G 0)

open NumberField Complex in
open scoped nonZeroDivisors ContDiff in
variable (F : Type) [Field F] [NumberField F] in
variable {F} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.prod_emb [IsTotallyReal F] (x : F) :
    ∏ τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, ((τ x : ℝ) : ℂ) = ((Algebra.norm ℚ x : ℚ) : ℂ) := by
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [eq_ratCast] at h1
  rw [h1]
  have h2 : ∏ σ : F →ₐ[ℚ] ℂ, σ x = ∏ φ : F →+* ℂ, φ x :=
    Fintype.prod_bijective (fun σ : F →ₐ[ℚ] ℂ => (σ : F →+* ℂ))
      (RingHom.equivRatAlgHom F ℂ).symm.bijective _ _ (fun _ => rfl)
  have h3 : ∏ τ : F →+* ℝ, ((τ x : ℝ) : ℂ) = ∏ φ : F →+* ℂ, φ x := by
    refine Fintype.prod_bijective (fun τ : F →+* ℝ => Complex.ofRealHom.comp τ) ⟨?_, ?_⟩ _ _
      (fun _ => rfl)
    · intro a b h
      ext y
      have := congrArg (fun f : F →+* ℂ => f y) h
      simpa using this
    · intro φ
      have hφ : ComplexEmbedding.IsReal φ :=
        InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
      exact ⟨hφ.embedding, by ext y; simp [ComplexEmbedding.IsReal.coe_embedding_apply]⟩
  rw [h2, h3]

open NumberField Complex in
open scoped nonZeroDivisors ContDiff in
variable (F : Type) [Field F] [NumberField F] in
variable {F} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm_unit [IsTotallyReal F] {k : ℕ} (hk : Even k)
    (σ : ℂ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (ε : (𝓞 F)ˣ) (a b : F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z (a, b) := by
  have hprod : ∏ τ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt z (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) τ =
      ((Algebra.norm ℚ ((ε : 𝓞 F) : F) : ℚ) : ℂ) * ∏ τ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt z (a, b) τ := by
    rw [← _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.prod_emb, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt, map_mul]
    push_cast
    ring
  have hn : |Algebra.norm ℚ ((ε : 𝓞 F) : F)| = 1 := NumberField.Units.norm F ε
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm
  rw [hprod]
  rcases (abs_eq zero_le_one).mp hn with h | h <;> rw [h] <;>
    simp [hk.neg_pow, inv_neg, norm_neg]

open NumberField Complex in
open scoped nonZeroDivisors ContDiff in
variable (F : Type) [Field F] [NumberField F] in
variable {F} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass_mk [IsTotallyReal F] (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F)
    {k : ℕ} (hk : Even k) (σ : ℂ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ)
    (p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.LatPair 𝔞 𝔟) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k σ z (Quotient.mk _ p) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z p.1 := by
  have hrel := Quotient.mk_out (s := _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) p
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass
  generalize (Quotient.mk (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) p).out = q at hrel ⊢
  obtain ⟨ε, h1, h2⟩ := hrel
  have hp : p.1 = (((ε : 𝓞 F) : F) * q.1.1, ((ε : 𝓞 F) : F) * q.1.2) := Prod.ext h1 h2
  rw [hp, _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm_unit hk]

open NumberField Complex in
open scoped nonZeroDivisors ContDiff in
variable (F : Type) [Field F] [NumberField F] in
variable {F} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass_mk (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ)
    (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.QPair 𝔞 𝔟) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z (Quotient.mk _ p) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z p.1 := by
  have hrel := Quotient.mk_out (s := _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qRel 𝔞 𝔟) p
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass
  generalize (Quotient.mk (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qRel 𝔞 𝔟) p).out = q at hrel ⊢
  obtain ⟨ε, h1, h2⟩ := hrel
  have hu : |Algebra.norm ℚ (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)| = 1 := NumberField.Units.norm F ε⁻¹
  have hmul : p.1.1 * p.1.2 = q.1.1 * q.1.2 := by
    rw [h1, h2, mul_mul_mul_comm, _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.unit_inv_mul, one_mul]
  have hn : |((Algebra.norm ℚ p.1.1 : ℚ) : ℝ)| = |((Algebra.norm ℚ q.1.1 : ℚ) : ℝ)| := by
    rw [h1, map_mul, Rat.cast_mul, abs_mul, ← Rat.cast_abs, hu, Rat.cast_one, one_mul]
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm
  rw [hn, hmul]

open NumberField Complex in
open scoped nonZeroDivisors ContDiff in
variable (F : Type) [Field F] [NumberField F] in
variable {F} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt_ne_zero {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) {p : F × F} (hp : p ≠ 0) (τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt z p τ ≠ 0 := by
  intro h
  have h2 : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rcases mul_eq_zero.mp h with h' | h'
  · exact h2 h'
  · by_cases hb : p.2 = 0
    · have ha : p.1 ≠ 0 := fun ha => hp (Prod.ext ha hb)
      rw [hb, map_zero] at h'
      simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_eq_zero,
        map_eq_zero] at h'
      exact ha h'
    · have him := congrArg Complex.im h'
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        zero_mul, add_zero, zero_add, Complex.zero_im] at him
      rcases mul_eq_zero.mp him with h1 | h1
      · exact hb ((map_eq_zero τ).mp h1)
      · exact (hz τ).ne' h1

example (z : Unit → ℂ) : wirt () false (fun w => w ()) z = 1 ∧ wirt () true (fun w => w ()) z = 0 := by
  have h : fderiv ℝ (fun w : Unit → ℂ => w ()) z = ContinuousLinearMap.proj () :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Unit => ℂ) ()).fderiv
  constructor <;> simp [wirt, h]

end GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
