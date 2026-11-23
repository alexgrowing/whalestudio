import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.SiegelAssemble

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

variable (F E) in

abbrev phiInf : AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)

variable (F E) in

abbrev phiFin : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)

omit [NumberField E] in

theorem tens_ext {z z' : AF F ⊗[F] E} (h₁ : phiInf F E z = phiInf F E z') (h₂ : phiFin F E z = phiFin F E z') :
    z = z' := by
  obtain ⟨y, hy⟩ : ∃ y : AF F ⊗[F] E, y = z - z' + 1 := ⟨_, rfl⟩
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1)
    (Matrix.of fun _ _ => y)
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      change phiInf F E y = 1
      rw [hy, map_add, map_sub, h₁, sub_self, zero_add, map_one])
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      change phiFin F E y = 1
      rw [hy, map_add, map_sub, h₂, sub_self, zero_add, map_one])
  have h3 : z - z' + 1 = 1 := hy.symm.trans (congrFun (congrFun this 0) 0)
  exact sub_eq_zero.1 (add_right_cancel (h3.trans (zero_add 1).symm))

omit [NumberField E] in
theorem matrix_tens_ext {a b : Type} {P Q : Matrix a b (AF F ⊗[F] E)} (h₁ : P.map (phiInf F E) = Q.map (phiInf F E))
    (h₂ : P.map (phiFin F E) = Q.map (phiFin F E)) : P = Q :=
  Matrix.ext fun i j => tens_ext (congrFun (congrFun h₁ i) j) (congrFun (congrFun h₂ i) j)

omit [NumberField E] in
theorem mat_projInf (g : GAd σ J) : (matHom _ σ J (projInf σ J g)).1 = (matHom _ σ J g).1.map (phiInf F E) := rfl

omit [NumberField E] in
theorem mat_projFin (g : GAd σ J) : (matHom _ σ J (projFin σ J g)).1 = (matHom _ σ J g).1.map (phiFin F E) := rfl

theorem mem_minPar_of_parts {p q : GAd σ J} (hp : p ∈ minPar σ J X) (h₁ : projInf σ J q = projInf σ J p)
    (h₂ : projFin σ J q = 1) : q ∈ minPar σ J X := by
  obtain ⟨B, hB, e⟩ := hp
  let e₀ : AF F ⊗[F] E := (((1 : Ainf F), (0 : Af F)) : AF F) ⊗ₜ[F] (1 : E)
  have e₁ : phiInf F E e₀ = 1 := rfl
  have e₂ : phiFin F E e₀ = 0 := TensorProduct.zero_tmul _ _
  let B' : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) :=
    Matrix.of fun i j => (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) i j +
      e₀ * (B i j - (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) i j)
  have b₁ : B'.map (phiInf F E) = B.map (phiInf F E) := Matrix.ext fun i j => by
    simp [B', e₁]
  have b₂ : B'.map (phiFin F E) = 1 := Matrix.ext fun i j => by
    by_cases hij : i = j
    · subst hij; simp [B', e₂]
    · simp [B', e₂, Matrix.one_apply_ne hij]
  refine ⟨B', fun i j hij => ?_, matrix_tens_ext ?_ ?_⟩
  · have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    simp [B', hB hij, Matrix.one_apply_ne hne]
  · rw [Matrix.map_mul, Matrix.map_mul, ← mat_projInf, h₁, mat_projInf, b₁, ← Matrix.map_mul, e, Matrix.map_mul]
  · rw [Matrix.map_mul, Matrix.map_mul, ← mat_projFin, h₂, b₂]
    simp

theorem commute_of_mem {a b : GAd σ J} (ha : a ∈ infPts σ J) (hb : b ∈ finPts σ J) : Commute a b := by
  have ha' : a ∈ (ofInf σ J).range := by rw [range_ofInf]; exact ha
  have hb' : b ∈ (ofFin σ J).range := by rw [range_ofFin]; exact hb
  obtain ⟨x, rfl⟩ := ha'
  obtain ⟨y, rfl⟩ := hb'
  exact commute_ofInf_ofFin σ J x y

theorem mul_mem_leviMin {a b : GAd σ J} (ha : a ∈ leviMin σ J X Y) (hb : b ∈ leviMin σ J X Y) :
    a * b ∈ leviMin σ J X Y := by
  obtain ⟨d₁, d₁', e₁, e₁'⟩ := ha
  obtain ⟨d₂, d₂', e₂, e₂'⟩ := hb
  refine ⟨d₁ * d₂, d₁' * d₂', ?_, ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂, ← Matrix.mul_assoc, e₁, Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂', ← Matrix.mul_assoc, e₁', Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl

def prodSub (K₁ K₂ : Subgroup (GAd σ J)) (h₁ : K₁ ≤ infPts σ J) (h₂ : K₂ ≤ finPts σ J) : Subgroup (GAd σ J) where
  carrier := (K₁ : Set (GAd σ J)) * (K₂ : Set (GAd σ J))
  one_mem' := ⟨1, K₁.one_mem, 1, K₂.one_mem, one_mul 1⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
    have c : b * a' = a' * b := ((commute_of_mem (h₁ ha') (h₂ hb)).eq).symm
    change a * a' * (b * b') = a * b * (a' * b')
    rw [mul_assoc a b, ← mul_assoc b, c, mul_assoc a', mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
    change a⁻¹ * b⁻¹ = (a * b)⁻¹
    rw [_root_.mul_inv_rev]
    exact ((commute_of_mem (h₁ (K₁.inv_mem ha)) (h₂ (K₂.inv_mem hb))).eq)

end GlobalTheory.CompanionTheory.SiegelAssemble

open GlobalTheory.CompanionTheory.SiegelAssemble in

theorem GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ K₁ K₂ : Subgroup (GAd σ J), K₁ ≤ infPts σ J → K₂ ≤ finPts σ J → IsCompact (K₁ : Set (GAd σ J)) → IsCompact (K₂ : Set (GAd σ J)) → (∀ g ∈ infPts σ J, ∃ p ∈ minPar σ J X, p ∈ infPts σ J ∧ ∃ k ∈ K₁, g = p * k) → (∀ g ∈ finPts σ J, ∃ p ∈ minPar σ J X, p ∈ finPts σ J ∧ ∃ k ∈ K₂, g = p * k) → (∀ p ∈ minPar σ J X, p ∈ K₁ → p ∈ leviMin σ J X Y) → GoodPosition σ J X Y K₂ → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ (∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) ∧ GoodPosition σ J X Y K := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW K₁ K₂ h₁ h₂ c₁ c₂ iw₁ iw₂ hlev hgood
  refine ⟨prodSub K₁ K₂ h₁ h₂, (show IsCompact ((K₁ : Set (GAd σ J)) * (K₂ : Set (GAd σ J))) from c₁.mul c₂), fun g => ?_, ?_⟩
  · obtain ⟨p₁, hp₁, hp₁', k₁, hk₁, e₁⟩ := iw₁ (ofInf σ J (projInf σ J g)) (mem_infPts.2 (by simp))
    obtain ⟨p₂, hp₂, hp₂', k₂, hk₂, e₂⟩ := iw₂ (ofFin σ J (projFin σ J g)) (mem_finPts.2 (by simp))
    refine ⟨p₁ * p₂, mul_mem_minimal_parabolic hp₁ hp₂, k₁ * k₂, ⟨k₁, hk₁, k₂, hk₂, rfl⟩, ?_⟩
    have c : k₁ * p₂ = p₂ * k₁ := (commute_of_mem (h₁ hk₁) hp₂').eq
    calc g = ofInf σ J (projInf σ J g) * ofFin σ J (projFin σ J g) := (ofInf_projInf_mul_ofFin_projFin σ J g).symm
      _ = p₁ * (k₁ * p₂) * k₂ := by rw [e₁, e₂]; simp only [mul_assoc]
      _ = p₁ * p₂ * (k₁ * k₂) := by rw [c]; simp only [mul_assoc]
  · rintro _ hp ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have i₁ : projFin σ J k₁ = 1 := mem_infPts.1 (h₁ hk₁)
    have i₂ : projInf σ J k₂ = 1 := mem_finPts.1 (h₂ hk₂)
    have m₁ : k₁ ∈ minPar σ J X := mem_minPar_of_parts hp (by simp [i₂]) i₁
    have m₂ : k₂ ∈ minPar σ J X := by
      have := mul_mem_minimal_parabolic (inv_mem_minimal_parabolic h hJ hW m₁) hp
      simpa using this
    obtain ⟨m, hm, hmK, u, hu, huK, rfl⟩ := hgood k₂ m₂ hk₂
    exact ⟨k₁ * m, mul_mem_leviMin (hlev k₁ m₁ hk₁) hm, ⟨k₁, hk₁, m, hmK, rfl⟩, u, hu,
      ⟨1, K₁.one_mem, u, huK, one_mul u⟩, by simp only [mul_assoc]⟩

end
