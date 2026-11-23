import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeMapsOfFunctorComparison
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

def ExistsIO : Prop :=
  ∀ (K : Type) [Field K] (S α : Type) [Fintype S] [DecidableEq S] (TT : Finset S)
    (i : TT → MvPolynomial α K →ₗ[K] MvPolynomial (Bool × α) K),
    ∃ IO : MvPolynomial (S × α) K →ₗ[K] MvPolynomial ((TT × Bool) × α) K, ∀ P : S → MvPolynomial α K,
      (∀ s, s ∉ TT → P s = 1) → IO (∏ s, rename (fun v => (s, v)) (P s)) =
        ∏ s : TT, rename (fun v : Bool × α => ((s, v.1), v.2)) (i s (P s.val))

def ExistsPR : Prop :=
  ∀ (K : Type) [Field K] (S α : Type) [Fintype S] [DecidableEq S] (TT : Finset S)
    (pr : TT → MvPolynomial (Bool × α) K →ₗ[K] MvPolynomial α K),
    ∃ PR : MvPolynomial ((TT × Bool) × α) K →ₗ[K] MvPolynomial (S × α) K, ∀ Y : TT → MvPolynomial (Bool × α) K,
      PR (∏ s : TT, rename (fun v : Bool × α => ((s, v.1), v.2)) (Y s)) =
        ∏ s : TT, rename (fun v => (s.val, v)) (pr s (Y s))

def RegroupP : Prop :=
  ∀ (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (T α : Type) [Fintype T] [DecidableEq T]
    (N : T × Bool → Submodule R (MvPolynomial α K)) (y : T → MvPolynomial (Bool × α) K),
    (∀ s, y s ∈ Submodule.span R {P | ∃ F : Bool → MvPolynomial α K, (∀ b, F b ∈ N (s, b)) ∧
      P = ∏ b, rename (fun v => (b, v)) (F b)}) →
    ∏ s, rename (fun v : Bool × α => ((s, v.1), v.2)) (y s) ∈
      Submodule.span R {P | ∃ F : T × Bool → MvPolynomial α K, (∀ x, F x ∈ N x) ∧
        P = ∏ x, rename (fun v => (x, v)) (F x)}

section Abs

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {n' k n : ℕ} (TT : Finset (Fin n'))

theorem prodSmulPowT {σ ι : Type} [Fintype ι] (c : K) (w : ι → MvPolynomial σ K) :
    ∏ s, (c • w s) = c ^ Fintype.card ι • ∏ s, w s := by
  simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    map_pow]

theorem genRegroupT (F : TT × Bool → MvPolynomial (Fin k × Fin n) K) :
    ∏ x, blockEmb K x (F x) =
      ∏ s : TT, rename (fun v : Bool × (Fin k × Fin n) => ((s, v.1), v.2)) (∏ b, blockEmb K b (F (s, b))) := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun b _ =>
    (MvPolynomial.rename_rename (R := K) (fun v : Fin k × Fin n => (b, v))
      (fun v : Bool × (Fin k × Fin n) => ((s, v.1), v.2)) (F (s, b))).symm

theorem prodTopsT (G : TT → MvPolynomial (Fin k × Fin n) K) :
    ∏ s : TT, rename (fun v => (s.val, v)) (G s) =
      ∏ s : Fin n', blockEmb K s (if h : s ∈ TT then G ⟨s, h⟩ else 1) := by
  symm
  rw [← Finset.prod_subset (Finset.subset_univ TT)]
  · rw [← Finset.prod_coe_sort TT]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [dif_pos s.2]
    rfl
  · intro s _ hs
    rw [dif_neg hs, map_one]

theorem ioMem (hK2 : RegroupP) (i : TT → MvPolynomial (Fin k × Fin n) K →ₗ[K] MvPolynomial (Bool × (Fin k × Fin n)) K)
    (IO : MvPolynomial (Fin n' × (Fin k × Fin n)) K →ₗ[K] MvPolynomial ((TT × Bool) × (Fin k × Fin n)) K)
    (hIO : ∀ P : Fin n' → MvPolynomial (Fin k × Fin n) K, (∀ s, s ∉ TT → P s = 1) →
      IO (∏ s, rename (fun v => (s, v)) (P s)) =
        ∏ s : TT, rename (fun v : Bool × (Fin k × Fin n) => ((s, v.1), v.2)) (i s (P s.val)))
    (Nv : Fin n' → Submodule A (MvPolynomial (Fin k × Fin n) K))
    (N2 : TT × Bool → Submodule A (MvPolynomial (Fin k × Fin n) K)) (c : K)
    (h1 : ∀ s : TT, ∀ y ∈ Nv s.val, c • i s y ∈ tensorLat A K (fun b => N2 (s, b)))
    (h0 : ∀ s, s ∉ TT → ∀ y ∈ Nv s, ∃ a : A, y = C (algebraMap A K a)) :
    ∀ y ∈ tensorLat A K Nv, c ^ TT.card • IO y ∈ tensorLat A K N2 := by
  have hcomm : ∀ (a : A) (z : MvPolynomial ((TT × Bool) × (Fin k × Fin n)) K),
      c ^ TT.card • a • z = a • c ^ TT.card • z := fun a z => by
    rw [← algebraMap_smul K a z, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    classical
    let a' : Fin n' → A := fun s =>
      if h : s ∈ TT then 1 else Classical.choose (h0 s h (F s) (hF s))
    let P : Fin n' → MvPolynomial (Fin k × Fin n) K := fun s => if s ∈ TT then F s else 1
    have hP : ∀ s, s ∉ TT → P s = 1 := fun s hs => if_neg hs
    have hPF : ∀ s : TT, P s.val = F s.val := fun s => if_pos s.2
    have hterm : ∀ s, blockEmb K s (F s) =
        MvPolynomial.C (algebraMap A K (a' s)) * rename (fun v : Fin k × Fin n => (s, v)) (P s) := by
      intro s
      by_cases h : s ∈ TT
      · simp [a', P, h, blockEmb]
      · have e := Classical.choose_spec (h0 s h (F s) (hF s))
        simp only [a', P, dif_neg h, if_neg h, map_one, mul_one]
        conv_lhs => rw [e]
        exact MvPolynomial.rename_C _ _
    have hy : ∏ s, blockEmb K s (F s) =
        (∏ s, a' s) • ∏ s, rename (fun v : Fin k × Fin n => (s, v)) (P s) := by
      rw [Finset.prod_congr rfl fun s _ => hterm s, Finset.prod_mul_distrib, Algebra.smul_def,
        MvPolynomial.algebraMap_apply]
      simp only [map_prod]
    have hmem := hK2 A K TT (Fin k × Fin n) N2 (fun s => c • i s (P s.val))
      (fun s => by
        simp only [hPF s]
        exact h1 s (F s.val) (hF s.val))
    have hc : ∀ w : TT → MvPolynomial ((TT × Bool) × (Fin k × Fin n)) K,
        c ^ TT.card • ∏ s, w s = ∏ s, c • w s := fun w => by
      rw [prodSmulPowT, Fintype.card_coe]
    rw [hy, LinearMap.map_smul_of_tower, hcomm]
    refine Submodule.smul_mem _ _ ?_
    rw [hIO P hP, hc]
    simp only [map_smul] at hmem
    exact hmem
  | zero =>
    rw [map_zero, smul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    rw [map_add, smul_add]
    exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
    rw [LinearMap.map_smul_of_tower, hcomm]
    exact Submodule.smul_mem _ a ih

theorem prMem (pr : TT → MvPolynomial (Bool × (Fin k × Fin n)) K →ₗ[K] MvPolynomial (Fin k × Fin n) K)
    (PR : MvPolynomial ((TT × Bool) × (Fin k × Fin n)) K →ₗ[K] MvPolynomial (Fin n' × (Fin k × Fin n)) K)
    (hPR : ∀ Y : TT → MvPolynomial (Bool × (Fin k × Fin n)) K,
      PR (∏ s : TT, rename (fun v : Bool × (Fin k × Fin n) => ((s, v.1), v.2)) (Y s)) =
        ∏ s : TT, rename (fun v => (s.val, v)) (pr s (Y s)))
    (Nv : Fin n' → Submodule A (MvPolynomial (Fin k × Fin n) K))
    (N2 : TT × Bool → Submodule A (MvPolynomial (Fin k × Fin n) K)) (c : K)
    (h1 : ∀ s : TT, ∀ x ∈ tensorLat A K (fun b => N2 (s, b)), c • pr s x ∈ Nv s.val)
    (h0 : ∀ s, s ∉ TT → (1 : MvPolynomial (Fin k × Fin n) K) ∈ Nv s) :
    ∀ x ∈ tensorLat A K N2, c ^ TT.card • PR x ∈ tensorLat A K Nv := by
  have hcomm : ∀ (a : A) (z : MvPolynomial (Fin n' × (Fin k × Fin n)) K),
      c ^ TT.card • a • z = a • c ^ TT.card • z := fun a z => by
    rw [← algebraMap_smul K a z, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
  have hc : ∀ w : TT → MvPolynomial (Fin n' × (Fin k × Fin n)) K,
      c ^ TT.card • ∏ s, w s = ∏ s, c • w s := fun w => by
    rw [prodSmulPowT, Fintype.card_coe]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have ht := prodTopsT TT (fun s => c • pr s (∏ b, blockEmb K b (F (s, b))))
    simp only [map_smul] at ht
    rw [genRegroupT, hPR, hc, ht]
    refine Submodule.subset_span ⟨fun s => if h : s ∈ TT then
      c • pr ⟨s, h⟩ (∏ b, blockEmb K b (F (⟨s, h⟩, b))) else 1, fun s => ?_, rfl⟩
    dsimp only
    by_cases h : s ∈ TT
    · rw [dif_pos h]
      exact h1 ⟨s, h⟩ _ (Submodule.subset_span ⟨fun b => F (⟨s, h⟩, b), fun b => hF _, rfl⟩)
    · rw [dif_neg h]
      exact h0 s h
  | zero =>
    rw [map_zero, smul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    rw [map_add, smul_add]
    exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
    rw [LinearMap.map_smul_of_tower, hcomm]
    exact Submodule.smul_mem _ a ih

end Abs

end Formalism.MainNotions.flipOneThree.Pf

end
