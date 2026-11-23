import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsMulMinusculeTopTerm
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace GlobalTheory.Hk3.MinuscTopLocal

theorem ov_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Formalism.UG.Ov F v = Formalism.UG.intL (v.adicCompletion F) := by
  ext x
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) v).trans Iff.rfl

theorem zpow_int {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) (m : ℤ) :
    ϖ ^ m ∈ Formalism.UG.intL (v.adicCompletion F) ↔ 0 ≤ m := by
  rw [← ov_eq]
  show ϖ ^ m ∈ v.adicCompletionIntegers F ↔ 0 ≤ m
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_zpow₀, hϖ, ← WithZero.coe_zpow,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zero, Multiplicative.ofAdd_le,
    smul_eq_mul]
  omega

def dU {L : Type} [Field L] {n : ℕ} {ϖ : L} (h0 : ϖ ≠ 0) (e : Fin n → ℤ) : GL (Fin n) L where
  val := Matrix.diagonal fun i => ϖ ^ e i
  inv := Matrix.diagonal fun i => ϖ ^ (-e i)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ h0]; simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ h0]; simp

theorem intM_mul {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) :
    ∀ i j, (A * B) i j ∈ Formalism.UG.intL L := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA _ _) (hB _ _)

theorem intM_diag {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) {e : Fin n → ℤ} (he : ∀ i, 0 ≤ e i) :
    ∀ i j, (Matrix.diagonal fun i => ϖ ^ e i) i j ∈ Formalism.UG.intL (v.adicCompletion F) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · exact (zpow_int hϖ _).2 (he i)
  · exact zero_mem _

theorem unif_ne_zero {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) : ϖ ≠ 0 := by
  intro h
  rw [Formalism.UG.IsUnifV, h, map_zero] at hϖ
  exact WithZero.zero_ne_coe hϖ

theorem cartan_top_step : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F), Formalism.UG.IsUnifV F v ϖ → ∀ (d : Fin n → ℤ) (k : ℕ), Antitone d → (∀ i, 0 ≤ d i) → (∀ i : Fin n, 0 < d i ↔ (i : ℕ) < k) → ∀ a₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₃ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ d' : Fin n → ℤ, Antitone d' → ∀ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), (a₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if 0 < d i then d i - 1 else d i) * (a₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if (i : ℕ) < k then 1 else 0) * (a₃ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ d' * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (∀ i, 0 ≤ d' i) ∧ (d' = d ∨ (∑ i, d' i = ∑ i, d i ∧ ∑ i, d' i ^ 2 < ∑ i, d i ^ 2)) := by
  intro F _ _ v n ϖ hϖ d k hd hd0 hk a₁ ha₁ a₂ ha₂ a₃ ha₃ d' hd' k₁ hk₁ k₂ hk₂ e
  have h0 : ϖ ≠ 0 := unif_ne_zero hϖ
  rw [ov_eq] at ha₁ ha₂ ha₃ hk₁ hk₂
  have hm0 : ∀ i, 0 ≤ (fun i => if 0 < d i then d i - 1 else d i) i := fun i => by
    have := hd0 i; dsimp only; split_ifs <;> omega
  have hw0 : ∀ i : Fin n, 0 ≤ (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) i := fun i => by
    dsimp only; split_ifs <;> omega
  have hG : a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
      dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃ = k₁ * dU h0 d' * k₂ :=
    Units.ext (by simp only [Units.val_mul]; exact e)
  have hD : k₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
      dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * k₂⁻¹ = dU h0 d' := by
    rw [hG]; group
  have hd'0 : ∀ i, 0 ≤ d' i := by
    intro i
    have hI : ∀ a b, ((k₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
        dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * k₂⁻¹ : GL (Fin n) _) :
          Matrix (Fin n) (Fin n) _) a b ∈ Formalism.UG.intL (v.adicCompletion F) := by
      simp only [Units.val_mul]
      refine intM_mul (intM_mul (GlobalTheory.Hk3.MinuscTop.glint_entry (inv_mem hk₁)) ?_)
        (GlobalTheory.Hk3.MinuscTop.glint_entry (inv_mem hk₂))
      refine intM_mul (intM_mul (intM_mul (intM_mul (GlobalTheory.Hk3.MinuscTop.glint_entry ha₁) ?_)
        (GlobalTheory.Hk3.MinuscTop.glint_entry ha₂)) ?_) (GlobalTheory.Hk3.MinuscTop.glint_entry ha₃)
      · exact intM_diag hϖ hm0
      · exact intM_diag hϖ hw0
    have := hI i i
    rw [hD] at this
    change (Matrix.diagonal fun i => ϖ ^ d' i) i i ∈ _ at this
    rw [Matrix.diagonal_apply_eq] at this
    exact (zpow_int hϖ _).1 this
  obtain ⟨dN, hdN⟩ : ∃ f : Fin n → ℕ, ∀ i, (f i : ℤ) = d i :=
    ⟨fun i => (d i).toNat, fun i => Int.toNat_of_nonneg (hd0 i)⟩
  obtain ⟨d'N, hd'N⟩ : ∃ f : Fin n → ℕ, ∀ i, (f i : ℤ) = d' i :=
    ⟨fun i => (d' i).toNat, fun i => Int.toNat_of_nonneg (hd'0 i)⟩
  have hdA : Antitone dN := fun i j h => by have := hd h; have := hdN i; have := hdN j; omega
  have hd'A : Antitone d'N := fun i j h => by have := hd' h; have := hd'N i; have := hd'N j; omega
  have hkN : ∀ i : Fin n, 0 < dN i ↔ (i : ℕ) < k := fun i => by rw [← hk i, ← hdN i]; omega
  have hg : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i => ϖ ^ (dN i - 1) := by
    refine ⟨a₁⁻¹, inv_mem ha₁, a₂⁻¹, inv_mem ha₂, ?_⟩
    have : a₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) * a₂⁻¹ =
        dU h0 (fun i => if 0 < d i then d i - 1 else d i) := by group
    rw [this]
    change (Matrix.diagonal fun i => ϖ ^ (if 0 < d i then d i - 1 else d i)) = _
    congr 1; funext i
    rw [← zpow_natCast]; congr 1
    have := hdN i
    split_ifs <;> omega
  have ha : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i : Fin n => if (i : ℕ) < k then ϖ else 1 := by
    refine ⟨1, one_mem _, a₃⁻¹, inv_mem ha₃, ?_⟩
    have : 1 * (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * a₃⁻¹ =
        dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) := by group
    rw [this]
    change (Matrix.diagonal fun i : Fin n => ϖ ^ (if (i : ℕ) < k then (1 : ℤ) else 0)) = _
    congr 1; funext i
    split_ifs <;> simp
  have hga : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * ((a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) *
        (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃)) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i => ϖ ^ d'N i := by
    refine ⟨k₁⁻¹, inv_mem hk₁, k₂⁻¹, inv_mem hk₂, ?_⟩
    rw [← mul_assoc (a₁ * _ * a₂), hD]
    change (Matrix.diagonal fun i => ϖ ^ d' i) = _
    congr 1; funext i
    rw [← hd'N i, zpow_natCast]
  have key := GlobalTheory.Hk3.MinuscTop.elemDiv_mul_minuscule (v.adicCompletion F) ϖ n hϖ dN k hdA hkN _ _ hg ha
    d'N hd'A hga
  refine ⟨hd'0, ?_⟩
  have s1 : ∑ i, d' i = ((∑ i, d'N i : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => (hd'N i).symm
  have s2 : ∑ i, d i = ((∑ i, dN i : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => (hdN i).symm
  have s3 : ∑ i, d' i ^ 2 = ((∑ i, d'N i ^ 2 : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => by rw [hd'N i]
  have s4 : ∑ i, d i ^ 2 = ((∑ i, dN i ^ 2 : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => by rw [hdN i]
  rcases key with h | ⟨h1, h2⟩
  · left; funext i; rw [← hd'N i, ← hdN i, h]
  · right
    rw [s1, s2, s3, s4]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

end GlobalTheory.Hk3.MinuscTopLocal
