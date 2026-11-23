import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory

theorem stabGL_iff_conj_stdLat {A : Type} [CommRing A] (S : Subring A) {n : Type} [Fintype n]
    [DecidableEq n] (b : GL n A) (Λ : Submodule S (n → A))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ S) (g : GL n A) :
    g ∈ stabGL Λ ↔ b⁻¹ * g * b ∈ stabGL (stdLat (n := n) (A := A) S) := by
  have key : ∀ x : n → A, x ∈ Λ ↔ (b⁻¹).1 *ᵥ x ∈ stdLat (n := n) (A := A) S := fun x => by
    rw [hΛ, Formalism.UG.P.afsplit_mem_stdLat]
  constructor
  · intro hg y
    have h := hg (b.1 *ᵥ y)
    rw [key, key] at h
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Units.val_mul,
      Matrix.mul_assoc] using h
  · intro hg x
    have h := hg ((b⁻¹).1 *ᵥ x)
    rw [key, key]
    simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.mul_one, Units.val_mul,
      Matrix.mul_assoc] using h

theorem conj_mem_UJ_one {A : Type} [CommRing A] (τ : A →+* A) {n : Type} [Fintype n]
    [DecidableEq n] (J : Matrix n n A) (b : GL n A) (hb : cT τ b.1 * J * b.1 = 1)
    (g : GL n A) (hg : g ∈ UJ τ J) : b⁻¹ * g * b ∈ UJ τ (1 : Matrix n n A) := by
  have hg' : cT τ g.1 * J * g.1 = J := hg
  have cm : ∀ M N : Matrix n n A, cT τ (M * N) = cT τ N * cT τ M := fun M N => by
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  have c1 : cT τ (1 : Matrix n n A) = 1 := by
    simp only [cT, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one]
  have hJ : cT τ (b⁻¹).1 * (b⁻¹).1 = J := by
    calc cT τ (b⁻¹).1 * (b⁻¹).1 = cT τ (b⁻¹).1 * (cT τ b.1 * J * b.1) * (b⁻¹).1 := by
          rw [hb, Matrix.mul_one]
      _ = cT τ (b.1 * (b⁻¹).1) * J * (b.1 * (b⁻¹).1) := by
          rw [cm]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, c1, Matrix.one_mul, Matrix.mul_one]
  change cT τ (b⁻¹ * g * b).1 * 1 * (b⁻¹ * g * b).1 = 1
  calc cT τ (b⁻¹ * g * b).1 * 1 * (b⁻¹ * g * b).1
      = cT τ b.1 * (cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1) * b.1 := by
        simp only [Units.val_mul, cm, Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [hJ, hg', hb]

theorem split_stabGL_iff_mem_range :
    ∀ (A K : Type) [CommRing A] [Field K] (O : ValuationSubring K) (S : Subring A) (τ : A →+* A) (φ : A ≃+* K × K), (∀ x, φ (τ x) = swapR K (φ x)) → (∀ x, x ∈ S ↔ (φ x).1 ∈ O ∧ (φ x).2 ∈ O) → ∀ (n : Type) [Fintype n] [DecidableEq n] (J : Matrix n n A) (b : GL n A) (Λ : Submodule S (n → A)), cT τ b.1 * J * b.1 = 1 → (∀ x, x ∈ Λ ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ S) → ∀ g ∈ UJ τ J, g ∈ stabGL Λ ↔ (bc ((RingHom.fst K K).comp φ.toRingHom) b)⁻¹ * bc ((RingHom.fst K K).comp φ.toRingHom) g * bc ((RingHom.fst K K).comp φ.toRingHom) b ∈ (bc (n := n) (algebraMap O K)).range := by
  intro A K _ _ O S τ φ hτ hS n _ _ J b Λ hb hΛ g hg
  have hU := conj_mem_UJ_one τ J b hb g hg
  rw [stabGL_iff_conj_stdLat S b Λ hΛ g, ← map_inv, ← map_mul, ← map_mul]
  generalize b⁻¹ * g * b = h at hU
  have hinj : Function.Injective (algebraMap O K) := Subtype.val_injective
  have hOr : ∀ x : K, x ∈ Set.range (algebraMap O K) ↔ x ∈ O :=
    fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rw [Formalism.UG.P.afsplit_stab_iff, Formalism.UG.P.levelvsplit_mem_range_iff _ hinj, ← map_inv,
    Formalism.UG.P.levelvsplit_coe_bc, Formalism.UG.P.levelvsplit_coe_bc]
  simp only [hOr, hS]
  have main : ∀ k : GL n A, k ∈ UJ τ (1 : Matrix n n A) → ∀ i j,
      (φ (k.1 i j)).2 = (φ ((k⁻¹).1 j i)).1 := by
    intro k hk i j
    have rel := Formalism.UG.P.levelvsplit_unitary τ φ hτ _ k hk
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at rel
    have hk1 : k.1.map ((RingHom.fst K K).comp φ.toRingHom) *
        (k⁻¹).1.map ((RingHom.fst K K).comp φ.toRingHom) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have s := Formalism.UG.P.levelvsplit_solve 1 1 _ _ _ (Matrix.mul_one _) hk1 rel
    rw [Matrix.one_mul, Matrix.mul_one] at s
    exact congrFun (congrFun s i) j
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => (h1 i j).1, fun i j => (h2 i j).1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ⟨h1 i j, ?_⟩, fun i j => ⟨h2 i j, ?_⟩⟩
    · rw [main h hU]; exact h2 j i
    · rw [main h⁻¹ (inv_mem hU), inv_inv]; exact h1 j i

end GlobalTheory
