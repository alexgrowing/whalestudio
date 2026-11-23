import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums

open Semi

theorem sameSum_of_factor_loc {Y X : Scheme.{0}} {K K' J : Type} [Fintype K] [Fintype K']
    [Fintype J] [DecidableEq J] (P : J → (Y ⟶ X)) (f : K → J) (f' : K' → J) (ε : K → ℤ)
    (ε' : K' → ℤ)
    (h : ∀ j₀ : J, (∑ k, if f k = j₀ then ε k else 0) = ∑ k', if f' k' = j₀ then ε' k' else 0) :
    LB.SameSum (fun k => P (f k)) ε (fun k' => P (f' k')) ε' := by
  classical
  intro ψ
  have key : ∀ {L : Type} [Fintype L] (g : L → J) (δ : L → ℤ),
      (∑ k, if P (g k) = ψ then δ k else 0) =
        ∑ j, if P j = ψ then (∑ k, if g k = j then δ k else 0) else 0 := by
    intro L _ g δ
    calc (∑ k, if P (g k) = ψ then δ k else 0)
        = ∑ k, ∑ j, (if g k = j then (if P j = ψ then δ k else 0) else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_ite_eq Finset.univ (g k) (fun j => if P j = ψ then δ k else 0)]
          simp
      _ = ∑ j, ∑ k, (if g k = j then (if P j = ψ then δ k else 0) else 0) := Finset.sum_comm
      _ = ∑ j, if P j = ψ then (∑ k, if g k = j then δ k else 0) else 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : P j = ψ
          · simp only [hj, if_true]
          · simp only [hj, if_false, ite_self, Finset.sum_const_zero]
  have e1 := key f ε
  have e2 := key f' ε'
  convert e1.trans ((Finset.sum_congr rfl fun j _ => by rw [h j]).trans e2.symm) using 2

section Prod

variable {S : Scheme.{0}} (H : Over S) [GrpObj H] [IsCommMonObj H]

theorem psum_eq_prod {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ H)) (I : Finset (Fin n)) :
    psum H x I = ∏ i ∈ I, x i := by
  classical
  have hf : ∀ l : List (Fin n), l.foldr (fun k acc => padd H (x k) acc) (pzero H T) =
      (l.map x).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, ih]
      rfl
  unfold psum
  rw [hf, ← List.prod_toFinset x ((List.nodup_finRange n).filter _)]
  congr 1
  ext i
  simp

theorem comp_prod {T T' : Over S} (a : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ H))
    (I : Finset (Fin n)) : a ≫ ∏ i ∈ I, x i = ∏ i ∈ I, (a ≫ x i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact MonObj.comp_one a
  | insert b s hb ih => rw [Finset.prod_insert hb, Finset.prod_insert hb, MonObj.comp_mul, ih]

theorem fam_eq {T : Over S} (a : T ⟶ G3 H) {m : ℕ} (y : Fin m → (T ⟶ H))
    (A : Fin 3 → Finset (Fin m)) (hA : ∀ i, a ≫ x3 H i = ∏ j ∈ A i, y j)
    (hdis : ∀ i i', i ≠ i' → Disjoint (A i) (A i')) (k : thK) :
    a.left ≫ thφ H (x3 H) k = (∏ j ∈ k.down.biUnion A, y j).left := by
  classical
  show a.left ≫ (psum H (x3 H) k.down).left = _
  rw [← Over.comp_left, psum_eq_prod, comp_prod, Finset.prod_biUnion]
  · exact congrArg Over.Hom.left (Finset.prod_congr rfl fun i _ => hA i)
  · intro i _ i' _ hii'
    exact hdis i i' hii'

theorem th_eq (k : thK) : thφ H (x3 H) k = (∏ j ∈ k.down, x3 H j).left := by
  show (psum H (x3 H) k.down).left = _
  rw [psum_eq_prod]

end Prod

section Sums

variable {S : Scheme.{0}} (H : Over S) [GrpObj H] [IsCommMonObj H]

def faceA : Fin 3 → Fin 3 → Finset (Fin 2) := ![![∅, {0}, {1}], ![{0}, ∅, {1}], ![{0}, {1}, ∅]]

theorem face_hA (i j : Fin 3) : faceMap H i ≫ x3 H j = ∏ l ∈ faceA i j, x2 H l := by
  fin_cases i <;> fin_cases j <;>
    simp [faceMap, x3, x2, faceA, pzero, Hom.one_def]

theorem face_hdis (i : Fin 3) : ∀ j j', j ≠ j' → Disjoint (faceA i j) (faceA i j') := by
  fin_cases i <;> decide

theorem face_fib (i : Fin 3) : ∀ J₀ : Finset (Fin 2),
    (∑ k : thK, if k.down.biUnion (faceA i) = J₀ then thε k else 0) =
      ∑ k' : PEmpty, if (PEmpty.elim k' : Finset (Fin 2)) = J₀ then (PEmpty.elim k' : ℤ) else 0 := by
  fin_cases i <;> decide

def swapFirstTwoSubsets : Fin 3 → Finset (Fin 3) := ![{1}, {0}, {2}]
def swapLastTwoSubsets : Fin 3 → Finset (Fin 3) := ![{0}, {2}, {1}]

theorem swapFirstTwo_proj_prod (j : Fin 3) :
    lift (x3 H 1) (lift (x3 H 0) (x3 H 2)) ≫ x3 H j = ∏ l ∈ swapFirstTwoSubsets j, x3 H l := by
  fin_cases j <;> simp [x3, swapFirstTwoSubsets]

theorem swapLastTwo_proj_prod (j : Fin 3) :
    lift (x3 H 0) (lift (x3 H 2) (x3 H 1)) ≫ x3 H j = ∏ l ∈ swapLastTwoSubsets j, x3 H l := by
  fin_cases j <;> simp [x3, swapLastTwoSubsets]

theorem swapFirstTwo_fiber_sum : ∀ J₀ : Finset (Fin 3),
    (∑ k : thK, if k.down = J₀ then thε k else 0) =
      ∑ k : thK, if k.down.biUnion swapFirstTwoSubsets = J₀ then thε k else 0 := by
  decide

theorem swapLastTwo_fiber_sum : ∀ J₀ : Finset (Fin 3),
    (∑ k : thK, if k.down = J₀ then thε k else 0) =
      ∑ k : thK, if k.down.biUnion swapLastTwoSubsets = J₀ then thε k else 0 := by
  decide

def c1A : Fin 3 → Finset (Fin 4) := ![{0, 1}, {2}, {3}]
def c2A : Fin 3 → Finset (Fin 4) := ![{0}, {1}, {3}]
def c3A : Fin 3 → Finset (Fin 4) := ![{0}, {1, 2}, {3}]
def c4A : Fin 3 → Finset (Fin 4) := ![{1}, {2}, {3}]

theorem cubeFaceFirst_proj_prod (j : Fin 3) :
    lift (padd H (x4 H 0) (x4 H 1)) (lift (x4 H 2) (x4 H 3)) ≫ x3 H j = ∏ l ∈ c1A j, x4 H l := by
  fin_cases j
  · simp only [x3, c1A, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, lift_fst]
    rw [Finset.prod_pair (by decide)]
    rfl
  · simp [x3, c1A]
  · simp [x3, c1A]

theorem cubeFaceOmit_proj_prod (j : Fin 3) :
    lift (x4 H 0) (lift (x4 H 1) (x4 H 3)) ≫ x3 H j = ∏ l ∈ c2A j, x4 H l := by
  fin_cases j <;> simp [x3, c2A]

theorem cubeFaceMiddle_proj_prod (j : Fin 3) :
    lift (x4 H 0) (lift (padd H (x4 H 1) (x4 H 2)) (x4 H 3)) ≫ x3 H j = ∏ l ∈ c3A j, x4 H l := by
  fin_cases j
  · simp [x3, c3A]
  · simp only [x3, c3A, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      lift_snd_assoc, lift_fst]
    rw [Finset.prod_pair (by decide)]
    rfl
  · simp [x3, c3A]

theorem cubeFaceLast_proj_prod (j : Fin 3) :
    lift (x4 H 1) (lift (x4 H 2) (x4 H 3)) ≫ x3 H j = ∏ l ∈ c4A j, x4 H l := by
  fin_cases j <;> simp [x3, c4A]

theorem coc_fib : ∀ J₀ : Finset (Fin 4),
    (∑ s : thK ⊕ thK, if Sum.elim (fun k : thK => k.down.biUnion c1A) (fun k : thK => k.down.biUnion c2A) s = J₀
        then Sum.elim thε thε s else 0) =
      ∑ s : thK ⊕ thK, if Sum.elim (fun k : thK => k.down.biUnion c3A) (fun k : thK => k.down.biUnion c4A) s = J₀
        then Sum.elim thε thε s else 0 := by
  decide

end Sums

end ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums

namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf

open Semi CubeCoordinateSums

section Sums

variable {S : Scheme.{0}} (H : Over S) [GrpObj H] [IsCommMonObj H]

theorem face_sameSum (i : Fin 3) :
    LB.SameSum (fun k : thK => (faceMap H i).left ≫ thφ H (x3 H) k) thε
      (PEmpty.elim : PEmpty → ((G2 H).left ⟶ H.left)) PEmpty.elim := by
  classical
  have hfam : (fun k : thK => (faceMap H i).left ≫ thφ H (x3 H) k) =
      fun k => (fun J : Finset (Fin 2) => (∏ l ∈ J, x2 H l).left) (k.down.biUnion (faceA i)) :=
    funext fun k => fam_eq H (faceMap H i) (x2 H) (faceA i) (face_hA H i) (face_hdis i) k
  have hE : (PEmpty.elim : PEmpty → ((G2 H).left ⟶ H.left)) =
      fun k' => (fun J : Finset (Fin 2) => (∏ l ∈ J, x2 H l).left) (PEmpty.elim k') :=
    funext fun k' => k'.elim
  rw [hfam, hE]
  exact sameSum_of_factor_loc (fun J : Finset (Fin 2) => (∏ l ∈ J, x2 H l).left)
    (fun k : thK => k.down.biUnion (faceA i)) (PEmpty.elim : PEmpty → Finset (Fin 2)) thε
    PEmpty.elim (face_fib i)

theorem swap_first_two_same_sum :
    LB.SameSum (thφ H (x3 H)) thε
      (fun k => (lift (x3 H 1) (lift (x3 H 0) (x3 H 2))).left ≫ thφ H (x3 H) k) thε := by
  classical
  have h1 : thφ H (x3 H) = fun k => (fun J : Finset (Fin 3) => (∏ l ∈ J, x3 H l).left) k.down :=
    funext fun k => th_eq H k
  have h2 : (fun k => (lift (x3 H 1) (lift (x3 H 0) (x3 H 2))).left ≫ thφ H (x3 H) k) =
      fun k => (fun J : Finset (Fin 3) => (∏ l ∈ J, x3 H l).left) (k.down.biUnion swapFirstTwoSubsets) :=
    funext fun k => fam_eq H _ (x3 H) swapFirstTwoSubsets (swapFirstTwo_proj_prod H) (by decide) k
  rw [h2, h1]
  exact sameSum_of_factor_loc (fun J : Finset (Fin 3) => (∏ l ∈ J, x3 H l).left)
    (fun k : thK => k.down) (fun k : thK => k.down.biUnion swapFirstTwoSubsets) thε thε swapFirstTwo_fiber_sum

theorem swap_last_two_same_sum :
    LB.SameSum (thφ H (x3 H)) thε
      (fun k => (lift (x3 H 0) (lift (x3 H 2) (x3 H 1))).left ≫ thφ H (x3 H) k) thε := by
  classical
  have h1 : thφ H (x3 H) = fun k => (fun J : Finset (Fin 3) => (∏ l ∈ J, x3 H l).left) k.down :=
    funext fun k => th_eq H k
  have h2 : (fun k => (lift (x3 H 0) (lift (x3 H 2) (x3 H 1))).left ≫ thφ H (x3 H) k) =
      fun k => (fun J : Finset (Fin 3) => (∏ l ∈ J, x3 H l).left) (k.down.biUnion swapLastTwoSubsets) :=
    funext fun k => fam_eq H _ (x3 H) swapLastTwoSubsets (swapLastTwo_proj_prod H) (by decide) k
  rw [h2, h1]
  exact sameSum_of_factor_loc (fun J : Finset (Fin 3) => (∏ l ∈ J, x3 H l).left)
    (fun k : thK => k.down) (fun k : thK => k.down.biUnion swapLastTwoSubsets) thε thε swapLastTwo_fiber_sum

theorem cocycle_sameSum :
    LB.SameSum
      (Sum.elim (fun k => (lift (padd H (x4 H 0) (x4 H 1)) (lift (x4 H 2) (x4 H 3))).left ≫
          thφ H (x3 H) k)
        (fun k => (lift (x4 H 0) (lift (x4 H 1) (x4 H 3))).left ≫ thφ H (x3 H) k))
      (Sum.elim thε thε)
      (Sum.elim (fun k => (lift (x4 H 0) (lift (padd H (x4 H 1) (x4 H 2)) (x4 H 3))).left ≫
          thφ H (x3 H) k)
        (fun k => (lift (x4 H 1) (lift (x4 H 2) (x4 H 3))).left ≫ thφ H (x3 H) k))
      (Sum.elim thε thε) := by
  classical
  have h1 : Sum.elim (fun k => (lift (padd H (x4 H 0) (x4 H 1)) (lift (x4 H 2) (x4 H 3))).left ≫
          thφ H (x3 H) k)
        (fun k => (lift (x4 H 0) (lift (x4 H 1) (x4 H 3))).left ≫ thφ H (x3 H) k) =
      fun s => (fun J : Finset (Fin 4) => (∏ l ∈ J, x4 H l).left)
        (Sum.elim (fun k : thK => k.down.biUnion c1A) (fun k : thK => k.down.biUnion c2A) s) := by
    funext s
    rcases s with k | k
    · exact fam_eq H _ (x4 H) c1A (cubeFaceFirst_proj_prod H) (by decide) k
    · exact fam_eq H _ (x4 H) c2A (cubeFaceOmit_proj_prod H) (by decide) k
  have h2 : Sum.elim (fun k => (lift (x4 H 0) (lift (padd H (x4 H 1) (x4 H 2)) (x4 H 3))).left ≫
          thφ H (x3 H) k)
        (fun k => (lift (x4 H 1) (lift (x4 H 2) (x4 H 3))).left ≫ thφ H (x3 H) k) =
      fun s => (fun J : Finset (Fin 4) => (∏ l ∈ J, x4 H l).left)
        (Sum.elim (fun k : thK => k.down.biUnion c3A) (fun k : thK => k.down.biUnion c4A) s) := by
    funext s
    rcases s with k | k
    · exact fam_eq H _ (x4 H) c3A (cubeFaceMiddle_proj_prod H) (by decide) k
    · exact fam_eq H _ (x4 H) c4A (cubeFaceLast_proj_prod H) (by decide) k
  rw [h1, h2]
  exact sameSum_of_factor_loc (fun J : Finset (Fin 4) => (∏ l ∈ J, x4 H l).left) _ _ _ _ coc_fib

end Sums

end ReciprocityTheory.ChartRestriction.G.Out.CubePf
