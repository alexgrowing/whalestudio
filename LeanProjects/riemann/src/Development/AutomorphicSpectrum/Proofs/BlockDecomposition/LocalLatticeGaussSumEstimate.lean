import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem pow_mul_mem_submodule (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E))
    {t : R ⊗[F] E} (ht : t ∈ O) (k : ℕ) {x : R ⊗[F] E} (hx : x ∈ L) : t ^ k * x ∈ L := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact L.smul_mem (⟨t, ht⟩ : O) ih

theorem sum_mul_mem_submodule (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E)) {n : ℕ}
    (x a : Fin n → R ⊗[F] E) (hx : ∀ i, x i ∈ L) (ha : ∀ i, a i ∈ O) : ∑ i, x i * a i ∈ L := by
  refine L.sum_mem fun i _ => ?_
  rw [mul_comm]
  exact L.smul_mem (⟨a i, ha i⟩ : O) (hx i)

theorem nearNF_anti (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E))
    {t : R ⊗[F] E} (ht : t ∈ O) {M n : ℕ} {j j' : ℕ} (h : j ≤ j') :
    nearNF (M := M) (n := n) R (O : Set (R ⊗[F] E)) (L : Set (R ⊗[F] E)) t j' ⊆
      nearNF R (O : Set (R ⊗[F] E)) (L : Set (R ⊗[F] E)) t j := by
  rintro X ⟨hX, l, a, ha, hl, hk⟩
  refine ⟨hX, l, a, ha, hl, fun k => ?_⟩
  obtain ⟨y, hy, hyk⟩ := hk k
  refine ⟨t ^ (j' - j) * y, pow_mul_mem_submodule R O L ht _ hy, ?_⟩
  rw [← hyk]
  change t ^ j * (t ^ (j' - j) * y) = t ^ j' * y
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

theorem goodT_mono (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E))
    (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) (hS : ∀ p ∈ S, (p.1 : R ⊗[F] E) ∈ O) (M n : ℕ) :
    Monotone (fun j => goodT (M := M) (n := n) R (O : Set (R ⊗[F] E)) (L : Set (R ⊗[F] E)) S j) := by
  intro j j' h X hX
  refine ⟨hX.1, fun hmem => hX.2 ?_⟩
  simp only [Set.mem_iUnion] at hmem ⊢
  obtain ⟨p, hp, hXp⟩ := hmem
  exact ⟨p, hp, nearNF_anti R O L (hS p hp) h hXp⟩

theorem goodT_free (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E))
    (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E)))
    (hfix : ∀ p ∈ S, ∀ x, p.2 * x = 0 → (p.1 : R ⊗[F] E) * x = x) {M n : ℕ}
    (hdet : ∀ X : Fin n → Fin M → R ⊗[F] E, ¬ LinearIndependent (R ⊗[F] E) X →
      ∃ p ∈ S, ∃ (l : Fin n) (a : Fin n → R ⊗[F] E), (∀ i, a i ∈ O) ∧ a l = 1 ∧
        ∀ k, p.2 * ∑ i, X i k * a i = 0) (j : ℕ) :
    goodT (M := M) (n := n) R (O : Set (R ⊗[F] E)) (L : Set (R ⊗[F] E)) S j ⊆
      {X | LinearIndependent (R ⊗[F] E) X} := by
  intro X hX
  by_contra hli
  obtain ⟨p, hp, l, a, ha, hl, hk⟩ := hdet X hli
  refine hX.2 ?_
  simp only [Set.mem_iUnion]
  refine ⟨p, hp, hX.1, l, a, ha, hl, fun k => ?_⟩
  have hxL : ∑ i, X i k * a i ∈ L :=
    sum_mul_mem_submodule R O L (fun i => X i k) a (fun i => hX.1 i k) ha
  refine ⟨_, hxL, ?_⟩
  have hfx := hfix p hp _ (hk k)
  have hpow : ∀ m : ℕ, (p.1 : R ⊗[F] E) ^ m * ∑ i, X i k * a i = ∑ i, X i k * a i := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_assoc, hfx, ih]
  exact hpow j

end Gen

theorem goodT_mono_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ), Monotone (fun j => (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j)) ∧ ∀ j, (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} := by
  intro F E _ _ _ _ _ σ _ d b v lv _ O S hO L _ _ n M
  obtain ⟨-, -, -, hS, hdet⟩ := hO
  exact ⟨goodT_mono (Fv F v) O L S (fun p hp => (hS p hp).1) M n,
    fun j => goodT_free (Fv F v) O L S (fun p hp => (hS p hp).2.2.1) (hdet n M) j⟩

end GlobalTheory.CompanionTheory.AvgFree
