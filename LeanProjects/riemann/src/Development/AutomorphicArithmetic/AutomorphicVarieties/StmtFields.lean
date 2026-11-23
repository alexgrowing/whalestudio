import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN

noncomputable section

open NumberField Polynomial

namespace UpperTheory.V

open Formalism.HC UpperTheory.Top

structure AbF where
  m : ℕ
  pos : 0 < m
  H : Subgroup (ZMod m)ˣ

namespace AbF

def ker (A : AbF) (a : ℕ) : Prop := ∃ u ∈ A.H, ((u : (ZMod A.m)ˣ) : ZMod A.m) = (a : ZMod A.m)

def deg (A : AbF) : ℕ := A.H.index

def HasMu (A : AbF) (l : ℕ) : Prop := l ∣ A.m ∧ ∀ a : ℕ, A.ker a → a ≡ 1 [MOD l]

def ofChar (ψ : PChar) : AbF := ⟨ψ.N, NeZero.pos _, ψ.χ.toUnitHom.ker⟩

def cyc (m : ℕ) : AbF := ⟨max m 1, by omega, ⊥⟩

end AbF

def IsAbField (A : AbF) (L : Type) [Field L] [NumberField L] : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (j : L →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ),
    A.m ∣ N ∧ IsPrimitiveRoot ζ N ∧
    ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : L, τ (j x) = j x) ↔ A.ker a)

def IsCompField (A : AbF) (e q d : ℕ) (E : Type) [Field E] [NumberField E] : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ),
    2 ^ (e + 2) ∣ N ∧ A.m ∣ N ∧ q ∣ N ∧ d ∣ N ∧ IsPrimitiveRoot ζ N ∧
    ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : E, τ (j x) = j x) ↔
        (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧
          jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1)

def condF (E : Type) [Field E] [NumberField E] : ℕ :=
  sInf {N : ℕ | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)}

def IsLayer (l j : ℕ) (L L' : Type) [Field L] [Field L'] [Algebra L L'] : Prop :=
  (∃ k : ℕ, IsCyclotomicExtension {l ^ k} L L') ∧ Module.finrank L L' = l ^ j

def Kstar (p : ℕ) : Type := (X ^ 2 + C (p : ℚ) : ℚ[X]).SplittingField

instance (p : ℕ) : Field (Kstar p) := inferInstanceAs (Field (X ^ 2 + C (p : ℚ) : ℚ[X]).SplittingField)

instance (p : ℕ) : NumberField (Kstar p) :=
  NumberField.of_module_finite ℚ (X ^ 2 + C (p : ℚ) : ℚ[X]).SplittingField

def ordC (ψ : PChar) : ℕ := orderOf ψ.χ

def pK (ψ : PChar) : ℕ := sInf {p : ℕ | p.Prime ∧ p % 4 = 3 ∧ 7 ≤ p ∧ p.Coprime ψ.N}

def hStar (ψ : PChar) : ℕ := classNumber (Kstar (pK ψ))

def pOne (ψ : PChar) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ p ≡ 1 [MOD ordCompl[2] (ordC ψ)] ∧ p.Coprime (2 * ψ.N * pK ψ)}

def Bchi (ψ : PChar) : Finset ℕ :=
  insert 3 ((ordC ψ * ψ.N * pK ψ * hStar ψ * pOne ψ).primeFactors.erase 2)

def minusBound (C : ℝ) (o n N t : ℕ) : ℝ :=
  3 * n * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * N) +
    C * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * l * N) ^ 2

theorem AbF.ker_ofChar (ψ : PChar) (a : ℕ) : (AbF.ofChar ψ).ker a ↔ ψ.val a = 1 := by
  show (∃ u ∈ ψ.χ.toUnitHom.ker, ((u : (ZMod ψ.N)ˣ) : ZMod ψ.N) = (a : ZMod ψ.N)) ↔
    ψ.χ (a : ZMod ψ.N) = 1
  constructor
  · rintro ⟨u, hu, hua⟩
    rw [← hua]
    have := congrArg (fun v : ℂˣ => (v : ℂ)) (MonoidHom.mem_ker.mp hu)
    simpa [MulChar.coe_toUnitHom] using this
  · intro h
    have hu : IsUnit (a : ZMod ψ.N) := by
      by_contra hn
      rw [MulChar.map_nonunit ψ.χ hn] at h
      exact zero_ne_one h
    refine ⟨hu.unit, ?_, hu.unit_spec⟩
    rw [MonoidHom.mem_ker]
    ext
    simpa [MulChar.coe_toUnitHom] using h

theorem isCompField_ofChar (ψ : PChar) (e q d : ℕ) (E : Type) [Field E] [NumberField E] :
    IsCompField (AbF.ofChar ψ) e q d E ↔ IsChiField ψ e q d E := by
  simp only [IsCompField, IsChiField, AbF.ker_ofChar]
  rfl

theorem AbF.hasMu_cyc {l q : ℕ} (hl : 0 < l) (hq : 0 < q) : (AbF.cyc (l * q)).HasMu l := by
  have hm : max (l * q) 1 = l * q :=
    max_eq_left (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hl hq).ne')
  show (l ∣ max (l * q) 1) ∧ ∀ a : ℕ,
    (∃ u ∈ (⊥ : Subgroup (ZMod (max (l * q) 1))ˣ),
      ((u : (ZMod (max (l * q) 1))ˣ) : ZMod (max (l * q) 1)) = (a : ZMod (max (l * q) 1))) →
      a ≡ 1 [MOD l]
  refine ⟨?_, ?_⟩
  · rw [hm]
    exact dvd_mul_right l q
  · rintro a ⟨u, hu, hua⟩
    rw [Subgroup.mem_bot] at hu
    subst hu
    have h1 : ((a : ℕ) : ZMod (max (l * q) 1)) = ((1 : ℕ) : ZMod (max (l * q) 1)) := by
      simpa using hua.symm
    rw [ZMod.natCast_eq_natCast_iff, hm] at h1
    exact Nat.ModEq.of_mul_right q h1

theorem prime_of_mem_Bchi {ψ : PChar} {l : ℕ} (h : l ∈ Bchi ψ) : l.Prime ∧ l ≠ 2 := by
  unfold Bchi at h
  rcases Finset.mem_insert.mp h with rfl | h
  · exact ⟨Nat.prime_three, by decide⟩
  · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp h
    exact ⟨Nat.prime_of_mem_primeFactors hmem, hne⟩

end UpperTheory.V

end
