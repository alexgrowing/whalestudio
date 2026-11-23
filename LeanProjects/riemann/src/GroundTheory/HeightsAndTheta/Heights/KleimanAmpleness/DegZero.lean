import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

noncomputable section

namespace EulerSES

variable {F : Type} [Field F] {A : ℕ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)]

def cyc (C : ∀ n, Submodule F (A n)) (d : ∀ n, A n →ₗ[F] A (n + 1)) (n : ℕ) : Submodule F (A n) :=
  C n ⊓ LinearMap.ker (d n)

def bnd (C : ∀ n, Submodule F (A n)) (d : ∀ n, A n →ₗ[F] A (n + 1)) : (n : ℕ) → Submodule F (A n)
  | 0 => ⊥
  | n + 1 => (C n).map (d n)

abbrev coh (C : ∀ n, Submodule F (A n)) (d : ∀ n, A n →ₗ[F] A (n + 1)) (n : ℕ) : Type :=
  ↥(cyc C d n) ⧸ (bnd C d n).comap (cyc C d n).subtype

end EulerSES

open EulerSES

def EulerSES.Statement : Prop :=
  ∀ (F : Type) [Field F] (A B C : ℕ → Type) [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module F (B n)] [∀ n, AddCommGroup (C n)] [∀ n, Module F (C n)]
    (CA : ∀ n, Submodule F (A n)) (CB : ∀ n, Submodule F (B n)) (CC : ∀ n, Submodule F (C n))
    (dA : ∀ n, A n →ₗ[F] A (n + 1)) (dB : ∀ n, B n →ₗ[F] B (n + 1)) (dC : ∀ n, C n →ₗ[F] C (n + 1))
    (f : ∀ n, A n →ₗ[F] B n) (g : ∀ n, B n →ₗ[F] C n) (N : ℕ),
    (∀ n, ∀ x ∈ CA n, dA n x ∈ CA (n + 1)) → (∀ n, ∀ x ∈ CB n, dB n x ∈ CB (n + 1)) →
    (∀ n, ∀ x ∈ CC n, dC n x ∈ CC (n + 1)) →
    (∀ n, ∀ x ∈ CA n, dA (n + 1) (dA n x) = 0) → (∀ n, ∀ x ∈ CB n, dB (n + 1) (dB n x) = 0) →
    (∀ n, ∀ x ∈ CC n, dC (n + 1) (dC n x) = 0) →
    (∀ n, ∀ x ∈ CA n, f n x ∈ CB n) → (∀ n, ∀ y ∈ CB n, g n y ∈ CC n) →
    (∀ n, ∀ x ∈ CA n, dB n (f n x) = f (n + 1) (dA n x)) →
    (∀ n, ∀ y ∈ CB n, dC n (g n y) = g (n + 1) (dB n y)) →
    (∀ n, ∀ x ∈ CA n, f n x = 0 → x = 0) →
    (∀ n, ∀ x ∈ CA n, g n (f n x) = 0) →
    (∀ n, ∀ y ∈ CB n, g n y = 0 → ∃ x ∈ CA n, f n x = y) →
    (∀ n, ∀ z ∈ CC n, ∃ y ∈ CB n, g n y = z) →
    (∀ n, FiniteDimensional F (coh CA dA n)) → (∀ n, FiniteDimensional F (coh CB dB n)) →
    (∀ n, FiniteDimensional F (coh CC dC n)) →
    Subsingleton (coh CA dA (N + 1)) →
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (Module.finrank F (coh CB dB n) : ℤ) =
      ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (Module.finrank F (coh CA dA n) : ℤ) +
        ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (Module.finrank F (coh CC dC n) : ℤ)

def EulerSES.degZero (n : ℕ) : Submodule ℚ ℚ := if n = 0 then ⊤ else ⊥

theorem EulerSES.hyps :
    let CA : ∀ _ : ℕ, Submodule ℚ ℚ := fun _ => ⊥
    let CB : ∀ _ : ℕ, Submodule ℚ ℚ := EulerSES.degZero
    let d : ∀ n : ℕ, (fun _ : ℕ => ℚ) n →ₗ[ℚ] (fun _ : ℕ => ℚ) (n + 1) := fun _ => 0
    let f : ∀ n : ℕ, (fun _ : ℕ => ℚ) n →ₗ[ℚ] (fun _ : ℕ => ℚ) n := fun _ => 0
    let g : ∀ n : ℕ, (fun _ : ℕ => ℚ) n →ₗ[ℚ] (fun _ : ℕ => ℚ) n := fun _ => LinearMap.id
    (∀ n, ∀ x ∈ CA n, d n x ∈ CA (n + 1)) ∧ (∀ n, ∀ x ∈ CB n, d n x ∈ CB (n + 1)) ∧
    (∀ n, ∀ x ∈ CA n, d (n + 1) (d n x) = 0) ∧ (∀ n, ∀ x ∈ CB n, d (n + 1) (d n x) = 0) ∧
    (∀ n, ∀ x ∈ CA n, f n x ∈ CB n) ∧ (∀ n, ∀ y ∈ CB n, g n y ∈ CB n) ∧
    (∀ n, ∀ x ∈ CA n, d n (f n x) = f (n + 1) (d n x)) ∧
    (∀ n, ∀ y ∈ CB n, d n (g n y) = g (n + 1) (d n y)) ∧
    (∀ n, ∀ x ∈ CA n, f n x = 0 → x = 0) ∧
    (∀ n, ∀ x ∈ CA n, g n (f n x) = 0) ∧
    (∀ n, ∀ y ∈ CB n, g n y = 0 → ∃ x ∈ CA n, f n x = y) ∧
    (∀ n, ∀ z ∈ CB n, ∃ y ∈ CB n, g n y = z) ∧
    (∀ n, FiniteDimensional ℚ (coh CA d n)) ∧ (∀ n, FiniteDimensional ℚ (coh CB d n)) ∧
    Subsingleton (coh CA d 1) ∧ Module.finrank ℚ (coh CB d 0) = 1 := by
  intro CA CB d f g
  refine ⟨fun _ _ _ => zero_mem _, fun _ _ _ => zero_mem _, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => zero_mem _, fun _ _ h => h, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ x hx _ => (Submodule.mem_bot ℚ).1 hx, fun _ _ _ => rfl,
    fun _ y _ hy => ⟨0, zero_mem _, hy.symm⟩, fun _ z hz => ⟨z, hz, rfl⟩,
    fun _ => inferInstance, fun _ => inferInstance, ?_, ?_⟩
  · refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    have ha := (Submodule.mem_bot ℚ).1 (Submodule.mem_inf.1 a.2).1
    have hb := (Submodule.mem_bot ℚ).1 (Submodule.mem_inf.1 b.2).1
    congr 1
    exact Subtype.ext (ha.trans hb.symm)
  · have hcyc : cyc CB d 0 = ⊤ := by
      simp [cyc, CB, EulerSES.degZero, d]
    have hbnd : bnd CB d 0 = ⊥ := rfl
    rw [Submodule.Quotient.equiv _ ⊥ (LinearEquiv.ofTop _ hcyc) (by
      rw [hbnd, Submodule.comap_bot, Submodule.map_eq_bot_iff, Submodule.ker_subtype]) |>.finrank_eq]
    rw [(Submodule.quotEquivOfEqBot ⊥ rfl).finrank_eq, Module.finrank_self]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
