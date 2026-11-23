import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance

open Formalism.L2.Col

section Defs

variable {E : Type} [Field E] [NumberField E]

theorem intAt_zero (P : HeightOneSpectrum (𝓞 E)) : IntAt P (0 : E) :=
  ⟨0, 1, one_notMem P, by simp⟩

theorem intAt_add {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨s' * r + s * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']
  ring

theorem intAt_mul {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a * b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨r * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_mul, map_mul, ← h, ← h']
  ring

theorem intAt_neg {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, h⟩ := ha
  exact ⟨-r, s, hs, by rw [map_neg, ← h]; ring⟩

theorem intAt_algebraMap (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) : IntAt P (algebraMap (𝓞 E) E r) :=
  ⟨r, 1, one_notMem P, by simp⟩

def DegOneUnram (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  (qOf P).Prime ∧ ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2

def IsLatAt (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (abelian₂ : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  (∀ u : E, IntAt P u → ∀ v ∈ abelian₂, u • v ∈ abelian₂) ∧
    ∃ m : ℕ, (∀ v : Fin N → E, (∀ l, IntAt P (v l)) → ((qOf P : E) ^ m) • v ∈ abelian₂) ∧
      ∀ v ∈ abelian₂, ∀ l, IntAt P ((qOf P : E) ^ m * v l)

def adaptedVector (E : Type) [Field E] (n c i : ℕ) : Fin (n + c) → E := Loc.eN E (n + c) (n + (i - 1))

def unfoldedCoordinate {n c : ℕ} (i : ℕ) (v : Fin (n + c) → E) : E := Loc.atN v (n + (i - 1))

def srcGen (P : HeightOneSpectrum (𝓞 E)) (n' c' : ℕ) (e' : ℕ → ℤ) (z' : Fin n' → E) (i : ℕ) : Fin (n' + c') → E :=
  ((qOf P : E) ^ e' i) • (if i = 1 then adaptedVector E n' c' 1 + Loc.inX E n' c' z' else adaptedVector E n' c' i)

def srcLat (P : HeightOneSpectrum (𝓞 E)) {n' : ℕ} (c' : ℕ) (L' : Submodule (𝓞 E) (Fin n' → E)) (e' : ℕ → ℤ) (z' : Fin n' → E) :
    Submodule (𝓞 E) (Fin (n' + c') → E) where
  carrier := {v | ∃ l ∈ L', ∃ u : ℕ → E, (∀ i, IntAt P (u i)) ∧
    v = Loc.inX E n' c' l + ∑ i ∈ Finset.Icc 1 c', u i • srcGen P n' c' e' z' i}
  add_mem' := by
    rintro _ _ ⟨l, hl, u, hu, rfl⟩ ⟨l', hl', u', hu', rfl⟩
    refine ⟨l + l', L'.add_mem hl hl', fun i => u i + u' i, fun i => intAt_add (hu i) (hu' i), ?_⟩
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    abel
  zero_mem' := ⟨0, L'.zero_mem, fun _ => 0, fun _ => intAt_zero P, by simp⟩
  smul_mem' := by
    rintro r _ ⟨l, hl, u, hu, rfl⟩
    refine ⟨r • l, L'.smul_mem r hl, fun i => algebraMap (𝓞 E) E r * u i,
      fun i => intAt_mul (intAt_algebraMap P r) (hu i), ?_⟩
    rw [← algebraMap_smul E r, ← algebraMap_smul E r l, smul_add, map_smul, Finset.smul_sum]
    simp only [mul_smul]

def CondOOn {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (M : AddSubgroup E) : Prop :=
  (∀ a : E, IntAt P ((qOf P : E) * a) → a ∈ M) ∧ (∀ a ∈ M, ∀ b ∈ M, psi (a + b) = psi a * psi b) ∧
    (∀ a : E, IntAt P a → psi a = 1) ∧ psi ((qOf P : E)⁻¹) ≠ 1

def depthSub (P : HeightOneSpectrum (𝓞 E)) (D : ℕ) : AddSubgroup E where
  carrier := {a | IntAt P ((qOf P : E) ^ D * a)}
  add_mem' := fun {a b} ha hb => by
    show IntAt P _
    rw [mul_add]
    exact intAt_add ha hb
  zero_mem' := by
    show IntAt P _
    rw [mul_zero]
    exact intAt_zero P
  neg_mem' := fun {a} ha => by
    show IntAt P _
    rw [mul_neg]
    exact intAt_neg ha

def SuppOn {K : Type} [Field K] {a b : ℕ} (Lam' : Submodule (𝓞 E) (Fin a → E)) (abelian₂ : Submodule (𝓞 E) (Fin b → E))
    (Psi : Loc.SF E K a b) : Prop :=
  ∀ x, Psi x ≠ 0 → ∀ v ∈ Lam', x v ∈ abelian₂

def InvUnder {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (Lam' : Submodule (𝓞 E) (Fin a → E))
    (abelian₂ : Submodule (𝓞 E) (Fin b → E)) (Psi : Loc.SF E K a b) : Prop :=
  ∀ x y : (Fin a → E) →ₗ[E] (Fin b → E), (∀ v ∈ Lam', y v ∈ abelian₂) → Psi (x + (qOf P : E) • y) = Psi x

def unfoldAB {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (A B : ℕ) {n' c' n c : ℕ}
    (Psi : Loc.SF E K (n' + c') (n + c)) : Loc.SF E K n' n :=
  Loc.E1 psi (LocE.valsQ E (qOf P) A B) (((qOf P : K) ^ B)⁻¹) Psi

def Bounds (P : HeightOneSpectrum (𝓞 E)) {n' n c : ℕ} (e' : ℕ → ℤ) (z' : Fin n' → E) (abelian₂ : Submodule (𝓞 E) (Fin (n + c) → E))
    (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) : Prop :=
  (∃ e : ℕ → ℤ, ∀ i, 1 ≤ i → i ≤ c →
    (∀ s : E, (∃ v ∈ abelian₂, v ∈ Loc.Ufl E n c i ∧ unfoldedCoordinate i v = s) ↔ ∃ u : E, IntAt P u ∧ s = (qOf P : E) ^ e i * u) ∧
      e' (i + 1) - 1 ≤ e i ∧ e i ≤ e' i) ∧
  ((qOf P : E) ^ e' 1) • (adaptedVector E n c 1 + Loc.inX E n c (xj z')) ∈ abelian₂

end Defs

def UnfoldedBounds : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)), DegOneUnram P →
  ∀ (psi : E → K) (M : AddSubgroup E), CondOOn P psi M →
  ∀ (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 →
  ∀ (L' : Submodule (𝓞 E) (Fin n' → E)), IsLatAt P L' →
  ∀ (e' : ℕ → ℤ) (z' : Fin n' → E) (abelian₂ : Submodule (𝓞 E) (Fin (n + c) → E)), IsLatAt P abelian₂ →
  ∀ (Psi : Loc.SF E K (n' + c') (n + c)), SuppOn (srcLat P c' L' e' z') abelian₂ Psi → InvUnder P (srcLat P c' L' e' z') abelian₂ Psi →
  ∃ A₀ B₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → B₀ ≤ B → ∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E),
    (∀ t : Loc.FC n' c' n c → E, Psi (Loc.xx1 xj t) ≠ 0 → Loc.chArg (Loc.xx1 xj t) ∈ M) →
    unfoldAB P psi A B Psi xj ≠ 0 → Bounds P e' z' abelian₂ xj

example {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) :
    IsLatAt P ({ carrier := {v | ∀ l, IntAt P (v l)}
                 add_mem' := fun ha hb l => intAt_add (ha l) (hb l)
                 zero_mem' := fun _ => intAt_zero P
                 smul_mem' := fun r v hv l => by
                   have := intAt_mul (intAt_algebraMap P r) (hv l)
                   simpa [Algebra.smul_def] using this } : Submodule (𝓞 E) (Fin N → E)) :=
  ⟨fun _ hu _ hv l => intAt_mul hu (hv l), 0, fun v hv l => by simpa using hv l, fun v hv l => by simpa using hv l⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance
