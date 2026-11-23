import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
open scoped TensorProduct

namespace GlobalTheory.FockSplit

def jR (P Q R S : ℕ) : Ln P Q R 0 → Ln P Q R S := fun v => (v.1, Sum.elim Sum.inl (fun e => e.elim0) v.2)

def jS (P Q R S : ℕ) : Ln P Q 0 S → Ln P Q R S := fun v => (v.1, Sum.elim (fun e => e.elim0) Sum.inr v.2)

variable {P Q R S : ℕ}

theorem jR_injective : Function.Injective (jR P Q R S) := by
  rintro ⟨a, c | c⟩ ⟨a', c' | c'⟩ h
  · simp only [jR, Sum.elim_inl, Prod.mk.injEq, Sum.inl.injEq] at h; rw [h.1, h.2]
  · exact c'.elim0
  · exact c.elim0
  · exact c.elim0

theorem jS_injective : Function.Injective (jS P Q R S) := by
  rintro ⟨a, c | c⟩ ⟨a', c' | c'⟩ h
  · exact c.elim0
  · exact c.elim0
  · exact c'.elim0
  · simp only [jS, Sum.elim_inr, Prod.mk.injEq, Sum.inr.injEq] at h; rw [h.1, h.2]

theorem linePos_jR (l : Ln P Q R 0) : linePos (jR P Q R S l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> first | exact c.elim0 | rfl

theorem linePos_jS (l : Ln P Q 0 S) : linePos (jS P Q R S l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> first | exact c.elim0 | rfl

theorem jR_ne_jS (k : Ln P Q R 0) (m : Ln P Q 0 S) : jR P Q R S k ≠ jS P Q R S m := by
  rcases k with ⟨a, c | c⟩ <;> rcases m with ⟨a', e | e⟩
  · exact e.elim0
  · simp [jR, jS]
  · exact c.elim0
  · exact c.elim0

section General

variable {R' S' : ℕ} (j : Ln P Q R' S' → Ln P Q R S)

theorem pderiv_rename_eq_zero {σ τ : Type*} (i : σ → τ) (v : τ) (hv : ∀ m, i m ≠ v) (g : MvPolynomial σ ℂ) :
    pderiv v (rename i g) = 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p m hp => simp [hp, pderiv_X, Pi.single_apply, hv m]

theorem pderiv_rename_mul (hj : Function.Injective j) (k : Ln P Q R' S') (f : Pol P Q R' S') (G : Pol P Q R S)
    (hG : pderiv (j k) G = 0) : pderiv (j k) (rename j f * G) = rename j (pderiv k f) * G := by
  rw [Derivation.leibniz, hG, smul_zero, zero_add, pderiv_rename hj, smul_eq_mul, mul_comm]

theorem raiB_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    raiB (j l) (rename j f * G) = rename j (raiB l f) * G := by
  unfold raiB; rw [hpos l]
  split_ifs
  · simp [mul_assoc]
  · simp [pderiv_rename_mul j hj l f G (hG l)]

theorem lowB_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    lowB (j l) (rename j f * G) = rename j (lowB l f) * G := by
  unfold lowB; rw [hpos l]
  split_ifs
  · simp [pderiv_rename_mul j hj l f G (hG l)]
  · simp [mul_assoc]

theorem omE_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l l' : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    omE (j l) (j l') (rename j f * G) = rename j (omE l l' f) * G := by
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply, lowB_rename_mul j hj hpos l' f G hG,
    raiB_rename_mul j hj hpos l _ G hG, hj.eq_iff]
  split_ifs <;> simp [add_mul, smul_mul_assoc]

end General

theorem fockAct1_Eab_mul (a b : Ix P Q) (f : Pol P Q R 0) (g : Pol P Q 0 S) :
    fockAct1 P Q R S (Eab a b) (rename (jR P Q R S) f * rename (jS P Q R S) g) =
      rename (jR P Q R S) (fockAct1 P Q R 0 (Eab a b) f) * rename (jS P Q R S) g +
        rename (jR P Q R S) f * rename (jS P Q R S) (fockAct1 P Q 0 S (Eab a b) g) := by
  rw [fockAct1_Eab, fockAct1_Eab, fockAct1_Eab]
  simp only [LinearMap.sum_apply, LinearMap.add_apply, Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add,
    map_sum, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    exact omE_rename_mul (jR P Q R S) jR_injective linePos_jR (a, .inl c) (b, .inl c) f _
      (fun k => pderiv_rename_eq_zero _ _ (fun m => (jR_ne_jS k m).symm) g)
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm, mul_comm (rename _ f)]
    exact omE_rename_mul (jS P Q R S) jS_injective linePos_jS (a, .inr c) (b, .inr c) g _
      (fun k => pderiv_rename_eq_zero _ _ (fun m => jR_ne_jS m k) f)

end GlobalTheory.FockSplit

namespace GlobalTheory.FockSplit

variable {P Q R S : ℕ}

theorem fockAct1_rename_mul (Z : Mat P Q) (f : Pol P Q R 0) (g : Pol P Q 0 S) :
    fockAct1 P Q R S Z (rename (jR P Q R S) f * rename (jS P Q R S) g) =
      rename (jR P Q R S) (fockAct1 P Q R 0 Z f) * rename (jS P Q R S) g +
        rename (jR P Q R S) f * rename (jS P Q R S) (fockAct1 P Q 0 S Z g) := by
  have hZ : Z = ∑ a, ∑ b, Z a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp only [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hZ]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fockAct1_Eab_mul, smul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

def toTens (P Q R S : ℕ) (v : Ln P Q R S) : Pol P Q R 0 ⊗[ℂ] Pol P Q 0 S :=
  Sum.elim (fun c => X (v.1, Sum.inl c) ⊗ₜ 1) (fun e => 1 ⊗ₜ X (v.1, Sum.inr e)) v.2

theorem hasForm_of_pairing : ∀ (P Q R S : ℕ) (x : ℚ) (b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ), b ≠ 0 →
    (∀ Z f g, b (fockAct1 P Q R 0 Z f) g + b f (fockAct1 P Q 0 S Z g) = (x : ℂ) * Z.trace * b f g) →
    GlobalTheory.RealLift.HasForm P Q R S x := by
  intro P Q R S x b hb hinv
  let φ : Pol P Q R S →ₐ[ℂ] Pol P Q R 0 ⊗[ℂ] Pol P Q 0 S := aeval (toTens P Q R S)
  let μ : Pol P Q R 0 ⊗[ℂ] Pol P Q 0 S →ₐ[ℂ] Pol P Q R S :=
    Algebra.TensorProduct.productMap (rename (jR P Q R S)) (rename (jS P Q R S))
  have hμ : ∀ f g, μ (f ⊗ₜ g) = rename (jR P Q R S) f * rename (jS P Q R S) g := fun f g =>
    Algebra.TensorProduct.productMap_apply_tmul _ _ _ _
  have hφR : ∀ f, φ (rename (jR P Q R S) f) = f ⊗ₜ 1 := by
    intro f
    have : φ.comp (rename (jR P Q R S)) = Algebra.TensorProduct.includeLeft := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, c | c⟩
      · simp [φ, toTens, jR]
      · exact c.elim0
    simpa using congrArg (fun h => h f) this
  have hφS : ∀ g, φ (rename (jS P Q R S) g) = 1 ⊗ₜ g := by
    intro g
    have : φ.comp (rename (jS P Q R S)) = Algebra.TensorProduct.includeRight := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, c | c⟩
      · exact c.elim0
      · simp [φ, toTens, jS]
    simpa using congrArg (fun h => h g) this
  have hφ : ∀ f g, φ (rename (jR P Q R S) f * rename (jS P Q R S) g) = f ⊗ₜ g := by
    intro f g; rw [map_mul, hφR, hφS, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hμφ : μ.comp φ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, c | c⟩
    · simp [φ, μ, toTens, jR]
    · simp [φ, μ, toTens, jS]
  let l : Pol P Q R S →ₗ[ℂ] ℂ := TensorProduct.lift b ∘ₗ φ.toLinearMap
  have hl : ∀ f g, l (rename (jR P Q R S) f * rename (jS P Q R S) g) = b f g := by
    intro f g; simp [l, hφ]
  refine ⟨l, ?_, ?_⟩
  · intro h0
    apply hb
    refine LinearMap.ext fun f => LinearMap.ext fun g => ?_
    have := congrArg (fun m => m (rename (jR P Q R S) f * rename (jS P Q R S) g)) h0
    simpa [hl] using this
  · intro Z F
    have key : ∀ t, l (fockAct1 P Q R S Z (μ t)) = (x : ℂ) * Z.trace * l (μ t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul f g => rw [hμ, fockAct1_rename_mul, map_add, hl, hl, hl, hinv]
      | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂, mul_add]
    have hF : μ (φ F) = F := by simpa using congrArg (fun h => h F) hμφ
    simpa [hF] using key (φ F)

end GlobalTheory.FockSplit
