import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipNormOne

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

section Gen

variable {C : Type} [Field C]

def ZP (C : Type) [Field C] (σ : Type) : Subring (MvPolynomial σ C) := (MvPolynomial.map (Int.castRingHom C)).range

theorem X_mem_ZP {σ : Type} (x : σ) : (MvPolynomial.X x : MvPolynomial σ C) ∈ ZP C σ :=
  RingHom.mem_range.2 ⟨MvPolynomial.X x, MvPolynomial.map_X _ _⟩

theorem rename_mem_ZP {σ τ : Type} (k : σ → τ) {P : MvPolynomial σ C} (h : P ∈ ZP C σ) :
    MvPolynomial.rename k P ∈ ZP C τ := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  exact RingHom.mem_range.2 ⟨MvPolynomial.rename k Q, MvPolynomial.map_rename _ _ _⟩

theorem coeff_mem_of_ZP {σ : Type} {P : MvPolynomial σ C} (h : P ∈ ZP C σ) (O : Subring C) (m : σ →₀ ℕ) :
    P.coeff m ∈ O := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  rw [MvPolynomial.coeff_map, eq_intCast]
  exact intCast_mem O _

theorem det_mem {R : Type} [CommRing R] (S : Subring R) {k : ℕ} (M : Matrix (Fin k) (Fin k) R) (h : ∀ i j, M i j ∈ S) :
    M.det ∈ S := by
  rw [Matrix.det_apply]
  refine S.sum_mem fun s _ => ?_
  rw [Units.smul_def]
  exact S.zsmul_mem (S.prod_mem fun i _ => h _ _) _

theorem minorK_mem_ZP (N N' k : ℕ) : minorK C N N' k ∈ ZP C (Fin N × Fin N') := by
  unfold minorK
  split_ifs with h
  · exact det_mem _ _ fun i j => X_mem_ZP _
  · exact one_mem _

theorem minorMonomial_mem_ZP (N N' : ℕ) (e : ℕ → ℕ) : monP C N N' e ∈ ZP C (Fin N × Fin N') := by
  unfold monP
  exact prod_mem fun k _ => pow_mem (minorK_mem_ZP N N' k) _

end Gen

theorem poly_mem_ZP {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X) (b : GlobalTheory d) : b.poly X F ∈ ZP C _ := by
  unfold GlobalTheory.poly
  cases b with
  | bi g a i y =>
    exact mul_mem (pow_mem (rename_mem_ZP _ (minorK_mem_ZP _ _ _)) _)
      (pow_mem (rename_mem_ZP _ (minorK_mem_ZP _ _ _)) _)
  | ch g a u => exact pow_mem (rename_mem_ZP _ (minorK_mem_ZP _ _ _)) _
  | mon g e N => exact prod_mem fun a _ => rename_mem_ZP _ (minorMonomial_mem_ZP _ _ _)

theorem blkProd_mem_ZP {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
    {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n) : blkProd X F n L pl ∈ ZP C _ := by
  unfold blkProd toAll prodAll
  exact prod_mem fun o _ => rename_mem_ZP _ (prod_mem fun i _ => rename_mem_ZP _ (poly_mem_ZP _ _ _))

theorem norm_one_integral : NormOneIntegral := by
  intro C _ V d _ T r cc a Orb _ tau J _ X F Z ga n L pl _ O m
  exact coeff_mem_of_ZP (rename_mem_ZP _ (blkProd_mem_ZP _ _ _ _ _)) O m

end Formalism.L2.FormalSeriesBounds.RF
