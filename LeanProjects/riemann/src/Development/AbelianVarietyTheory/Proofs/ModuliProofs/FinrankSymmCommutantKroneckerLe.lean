import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SymmCommutant

open Matrix in

theorem entry_of_commute {K : Type} [Field K] {h : ℕ}
    (Ψ : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)
    (H : ∀ v : Fin 8, Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) * Ψ =
      Ψ * Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K)) (1 : Matrix (Fin h) (Fin h) K))
    (v b : Fin 8) (i j : Fin h) :
    Ψ (v, i) (b, j) = if v = b then Ψ (0, i) (0, j) else 0 := by
  have := congrFun (congrFun (H v) (0, i)) (b, j)
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.single_apply, Matrix.one_apply, ite_and] using this

open Matrix in
theorem core {K : Type} [Field K] {h : ℕ} (A B : Matrix (Fin 8) (Fin 8) K)
    (hA : A.IsSymm) (hBA : B * A = 1)
    (Θ : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K) (hΘ : Θ.IsSymm)
    (H : ∀ v : Fin 8, Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) * Θ =
      Θ * (Matrix.kronecker (B * (Matrix.single (0 : Fin 8) v (1 : K)).transpose * A)
        (1 : Matrix (Fin h) (Fin h) K)).transpose) :
    (∀ a b i j, Θ (a, i) (b, j) =
      B a b * (Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K)) (0, i) (0, j)) ∧
    ∀ i j, (Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K)) (0, i) (0, j) =
      (Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K)) (0, j) (0, i) := by
  have hAB : A * B = 1 := mul_eq_one_comm.mp hBA
  have hBtA : Bᵀ * A = 1 := by
    have : (Aᵀ * B)ᵀ = 1 := by rw [hA.eq, hAB, Matrix.transpose_one]
    simpa [Matrix.transpose_mul] using this
  have kmul : ∀ X Y : Matrix (Fin 8) (Fin 8) K,
      Matrix.kronecker X (1 : Matrix (Fin h) (Fin h) K) *
        Matrix.kronecker Y (1 : Matrix (Fin h) (Fin h) K) =
      Matrix.kronecker (X * Y) (1 : Matrix (Fin h) (Fin h) K) := by
    intro X Y
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have ktr : ∀ X : Matrix (Fin 8) (Fin 8) K,
      (Matrix.kronecker X (1 : Matrix (Fin h) (Fin h) K))ᵀ =
      Matrix.kronecker Xᵀ (1 : Matrix (Fin h) (Fin h) K) := by
    intro X
    simp only [Matrix.kronecker]
    rw [← Matrix.kroneckerMap_transpose, Matrix.transpose_one]
  set Ψ := Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K) with hΨ
  have hc : ∀ v : Fin 8, Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) * Ψ =
      Ψ * Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) := by
    intro v
    rw [hΨ, ← Matrix.mul_assoc, H v, ktr, Matrix.mul_assoc, Matrix.mul_assoc Θ, kmul, kmul]
    congr 2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq,
      Matrix.mul_assoc, Matrix.mul_assoc, hBtA, Matrix.mul_one]
  have he := entry_of_commute Ψ hc
  have hΘΨ : Θ = Ψ * Matrix.kronecker B (1 : Matrix (Fin h) (Fin h) K) := by
    rw [hΨ, Matrix.mul_assoc, kmul, hAB]
    simp [Matrix.kronecker]
  have h1 : ∀ a b i j, Θ (a, i) (b, j) = B a b * Ψ (0, i) (0, j) := by
    intro a b i j
    have := congrFun (congrFun hΘΨ (a, i)) (b, j)
    rw [this, Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [he a]
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, mul_comm]
  refine ⟨h1, fun i j => ?_⟩
  have h00 : ∑ b, A 0 b * B b 0 = 1 := by
    have := congrFun (congrFun hAB 0) 0
    simpa [Matrix.mul_apply] using this
  calc Ψ (0, i) (0, j) = ∑ b, Θ (0, i) (b, j) * A b 0 := by
        rw [hΨ, Matrix.mul_apply, Fintype.sum_prod_type]
        simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
    _ = ∑ b, (A 0 b * B b 0) * Ψ (0, j) (0, i) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← hΘ.apply (0, i) (b, j), h1, hA.apply b 0]
        ring
    _ = Ψ (0, j) (0, i) := by rw [← Finset.sum_mul, h00, _root_.one_mul]

end GlobalTheory.ZM.SymmCommutant

namespace GlobalTheory.ZM

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma entry_eq_sum_of_mul_eq_mul_kronecker (K : Type) [Field K] (h : ℕ)
    (Ei Em : Matrix (Fin 8) (Fin 8) ℤ) (Θ : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)
    (hΘ : ∀ u v : Fin 8, Matrix.kronecker ((Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K))
      (1 : Matrix (Fin h) (Fin h) K) * Θ = Θ * (Matrix.kronecker ((Ei * (Matrix.single u v
      (1 : ℤ)).transpose * Em).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)).transpose)
    (v c : Fin 8) (i j : Fin h) :
    Θ (v, i) (c, j) = (Ei c v : K) * ∑ d, Θ (0, i) (d, j) * (Em 0 d : K) := by
  have hX : ∀ u v : Fin 8, (Ei * (Matrix.single u v (1 : ℤ)).transpose * Em).map
      (Int.cast : ℤ → K) = Matrix.of fun c d => (Ei c v : K) * (Em u d : K) := by
    intro u v; ext c d
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.transpose_apply, Finset.sum_ite_eq',
      Finset.sum_ite_eq, ite_and]
  have hA : ∀ u v : Fin 8, (Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K) =
      Matrix.single u v (1 : K) := by
    intro u v; ext a b
    simp only [Matrix.map_apply, Matrix.single_apply]
    split_ifs <;> simp
  have e := congrFun (congrFun (hΘ 0 v) (0, i)) (c, j)
  rw [hA, hX] at e
  simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    Matrix.of_apply, Fintype.sum_prod_type, Matrix.single_apply, Matrix.one_apply] at e
  simpa [Finset.mul_sum, _root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc] using e

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.ZM.finrank_symm_commutant_le : ∀ (K : Type) [Field K] (h : ℕ) (Em Ei : Matrix (Fin 8) (Fin 8) ℤ) (V : Submodule K (Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)), Em.IsSymm → Ei * Em = 1 → (∀ Θ ∈ V, Θ.IsSymm ∧ ∀ u v : Fin 8, Matrix.kronecker ((Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K) * Θ = Θ * (Matrix.kronecker ((Ei * (Matrix.single u v (1 : ℤ)).transpose * Em).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)).transpose) → Module.finrank K V ≤ h * (h + 1) / 2 := by
  intro K _ h Em Ei V hEm hEiEm hV
  let B : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K → Fin h → Fin h → K :=
    fun Θ i j => ∑ d, Θ (0, i) (d, j) * (Em 0 d : K)
  have key : ∀ Θ ∈ V, ∀ v c i j, Θ (v, i) (c, j) = (Ei c v : K) * B Θ i j :=
    fun Θ hΘ v c i j => entry_eq_sum_of_mul_eq_mul_kronecker K h Ei Em Θ (hV Θ hΘ).2 v c i j
  have hsum : ∑ d, (Ei 0 d : K) * (Em 0 d : K) = 1 := by
    have e := congrFun (congrFun hEiEm 0) 0
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at e
    have e' : ∑ d, Ei 0 d * Em 0 d = 1 := by
      rw [← e]; exact Finset.sum_congr rfl fun d _ => by rw [hEm.apply 0 d]
    have e'' := congrArg (Int.cast : ℤ → K) e'
    push_cast at e''
    exact e''
  have symmB : ∀ Θ ∈ V, ∀ i j, B Θ i j = B Θ j i := by
    intro Θ hΘ i j
    calc B Θ i j = ∑ d, (Ei 0 d : K) * B Θ j i * (Em 0 d : K) :=
          Finset.sum_congr rfl fun d _ => by
            rw [← key Θ hΘ d 0 j i, (hV Θ hΘ).1.apply (0, i) (d, j)]
      _ = B Θ j i * ∑ d, (Ei 0 d : K) * (Em 0 d : K) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
      _ = B Θ j i := by rw [hsum, _root_.mul_one]
  let L : V →ₗ[K] (Sym2 (Fin h) → K) :=
    { toFun := fun Θ s => B Θ (Quot.out s).1 (Quot.out s).2
      map_add' := by
        intro x y; funext s
        simp [B, Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro r x; funext s
        simp [B, Finset.mul_sum, _root_.mul_assoc] }
  have inj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro Θ hΘ0
    have hB : ∀ i j, B Θ i j = 0 := by
      intro i j
      have hs := congrFun hΘ0 s(i, j)
      have hout : s((Quot.out s(i, j)).1, (Quot.out s(i, j)).2) = s(i, j) := Quot.out_eq _
      rcases Sym2.eq_iff.1 hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : B Θ (Quot.out s(i, j)).1 (Quot.out s(i, j)).2 = 0 := hs
        rwa [h1, h2] at this
      · have : B Θ (Quot.out s(i, j)).1 (Quot.out s(i, j)).2 = 0 := hs
        rw [h1, h2] at this
        rwa [symmB Θ Θ.2] at this
    apply Subtype.ext
    ext ⟨v, i⟩ ⟨c, j⟩
    rw [key Θ Θ.2, hB]
    simp
  calc Module.finrank K V ≤ Module.finrank K (Sym2 (Fin h) → K) :=
        LinearMap.finrank_le_finrank_of_injective inj
    _ = h * (h + 1) / 2 := by
        rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin, Nat.choose_two_right,
          Nat.add_sub_cancel, mul_comm]

end GlobalTheory.ZM
