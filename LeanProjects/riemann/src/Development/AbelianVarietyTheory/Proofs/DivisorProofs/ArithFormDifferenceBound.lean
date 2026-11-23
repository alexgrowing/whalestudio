import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TopPowDiff

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

theorem nonneg_of_span {D : ℕ} (F : MultilinearMap ℝ (fun _ : Fin D => E) ℝ) (G : Set E)
    (hF : ∀ N : Fin D → E, (∀ j, N j ∈ G) → 0 ≤ F N) :
    ∀ N : Fin D → E, (∀ j, N j ∈ Submodule.span NNReal G) → 0 ≤ F N := by
  classical
  suffices key : ∀ (S : Finset (Fin D)) (N : Fin D → E), (∀ j ∈ S, N j ∈ Submodule.span NNReal G) →
      (∀ j ∉ S, N j ∈ G) → 0 ≤ F N by
    intro N hN
    exact key Finset.univ N (fun j _ => hN j) (fun j hj => absurd (Finset.mem_univ j) hj)
  intro S
  induction S using Finset.induction_on with
  | empty => intro N _ hN; exact hF N fun j => hN j (Finset.notMem_empty j)
  | insert i S hi ih =>
    intro N hS hG
    have hc : ∀ c ∈ Submodule.span NNReal G, 0 ≤ F (Function.update N i c) := by
      intro c hc
      induction hc using Submodule.span_induction with
      | mem c hc =>
        apply ih
        · intro j hj
          rw [Function.update_of_ne (by rintro rfl; exact hi hj)]
          exact hS j (Finset.mem_insert_of_mem hj)
        · intro j hj
          by_cases hji : j = i
          · subst hji; simpa using hc
          · rw [Function.update_of_ne hji]
            exact hG j (by simp [hji, hj])
      | zero => rw [F.map_update_zero]
      | add a c _ _ ha hc => rw [F.map_update_add]; exact add_nonneg ha hc
      | smul t c _ hc =>
        rw [NNReal.smul_def, F.map_update_smul, smul_eq_mul]
        exact mul_nonneg t.2 hc
    simpa using hc (N i) (hS i (Finset.mem_insert_self i S))

theorem cons_congr_rad {D : ℕ} (num : GlobalTheory.VertForm.Form E D) (a : E) {N N' : Fin D → E}
    (h : ∀ j, N j - N' j ∈ GlobalTheory.VertForm.rad num) : num (Fin.cons a N) = num (Fin.cons a N') := by
  apply GlobalTheory.VertForm.map_congr_rad
  intro j
  cases j using Fin.cases with
  | zero => simp
  | succ j => simpa using h j

theorem nonneg_of_cone {D : ℕ} (num : GlobalTheory.VertForm.Form E D) (G : Set E)
    (F : MultilinearMap ℝ (fun _ : Fin D => E) ℝ)
    (hrad : ∀ N N' : Fin D → E, (∀ j, N j - N' j ∈ GlobalTheory.VertForm.rad num) → F N = F N')
    (hF : ∀ N : Fin D → E, (∀ j, N j ∈ G) → 0 ≤ F N) :
    ∀ N : Fin D → E, (∀ j, N j ∈ GlobalTheory.VertForm.cone num G) → 0 ≤ F N := by
  intro N hN
  choose z hz hzr using hN
  rw [hrad N z hzr]
  exact nonneg_of_span F G hF z hz

theorem abs_le_on_cone {D : ℕ} (num : GlobalTheory.VertForm.Form E D) (G : Set E) (a c : E) (b : ℝ)
    (hG : ∀ N : Fin D → E, (∀ j, N j ∈ G) → |num (Fin.cons a N)| ≤ b * num (Fin.cons c N)) :
    ∀ N : Fin D → E, (∀ j, N j ∈ GlobalTheory.VertForm.cone num G) →
      |num (Fin.cons a N)| ≤ b * num (Fin.cons c N) := by
  intro N hN
  let fa : MultilinearMap ℝ (fun _ : Fin D => E) ℝ := num.curryLeft a
  let fc : MultilinearMap ℝ (fun _ : Fin D => E) ℝ := num.curryLeft c
  have hfa : ∀ M, fa M = num (Fin.cons a M) := fun M => MultilinearMap.curryLeft_apply num a M
  have hfc : ∀ M, fc M = num (Fin.cons c M) := fun M => MultilinearMap.curryLeft_apply num c M
  have h1 := nonneg_of_cone num G (b • fc - fa)
    (fun N N' h => by
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, hfa, hfc,
        cons_congr_rad num a h, cons_congr_rad num c h])
    (fun N hN => by
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, hfa, hfc, smul_eq_mul]
      have := abs_le.mp (hG N hN); linarith) N hN
  have h2 := nonneg_of_cone num G (b • fc + fa)
    (fun N N' h => by
      simp only [MultilinearMap.add_apply, MultilinearMap.smul_apply, hfa, hfc,
        cons_congr_rad num a h, cons_congr_rad num c h])
    (fun N hN => by
      simp only [MultilinearMap.add_apply, MultilinearMap.smul_apply, hfa, hfc, smul_eq_mul]
      have := abs_le.mp (hG N hN); linarith) N hN
  simp only [MultilinearMap.sub_apply, MultilinearMap.add_apply, MultilinearMap.smul_apply, hfa, hfc,
    smul_eq_mul] at h1 h2
  rw [abs_le]; constructor <;> linarith

theorem abs_sub_le_add {D : ℕ} (f g : MultilinearMap ℝ (fun _ : Fin D => E) ℝ) (K : Set E)
    (hK : ∀ N : Fin D → E, (∀ j, N j ∈ K) → |f N| ≤ g N) (P Q : Fin D → E)
    (hP : ∀ j, P j ∈ K) (hQ : ∀ j, Q j ∈ K) : |f (P - Q)| ≤ g (P + Q) := by
  classical
  suffices key : ∀ (S : Finset (Fin D)) (A B : Fin D → E),
      (∀ j ∈ S, A j = P j - Q j ∧ B j = P j + Q j) → (∀ j ∉ S, A j = B j ∧ A j ∈ K) → |f A| ≤ g B by
    exact key Finset.univ _ _ (fun j _ => ⟨rfl, rfl⟩) (fun j hj => absurd (Finset.mem_univ j) hj)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro A B _ h
    have hAB : A = B := funext fun j => (h j (Finset.notMem_empty j)).1
    subst hAB
    exact hK A fun j => (h j (Finset.notMem_empty j)).2
  | insert i S hi ih =>
    intro A B hS hK'
    obtain ⟨hA, hB⟩ := hS i (Finset.mem_insert_self i S)
    have eA : A = Function.update A i (P i - Q i) := by rw [← hA, Function.update_eq_self]
    have eB : B = Function.update B i (P i + Q i) := by rw [← hB, Function.update_eq_self]
    have side : ∀ c ∈ K, |f (Function.update A i c)| ≤ g (Function.update B i c) := by
      intro c hc
      apply ih
      · intro j hj
        have hji : j ≠ i := by rintro rfl; exact hi hj
        rw [Function.update_of_ne hji, Function.update_of_ne hji]
        exact hS j (Finset.mem_insert_of_mem hj)
      · intro j hj
        by_cases hji : j = i
        · subst hji; simp [hc]
        · rw [Function.update_of_ne hji, Function.update_of_ne hji]
          exact hK' j (by simp [hji, hj])
    rw [eA, eB, f.map_update_sub, g.map_update_add]
    calc |f (Function.update A i (P i)) - f (Function.update A i (Q i))|
        ≤ |f (Function.update A i (P i))| + |f (Function.update A i (Q i))| := abs_sub _ _
      _ ≤ _ := add_le_add (side _ (hP i)) (side _ (hQ i))

theorem congr_of_update_zero {D : ℕ} (g : MultilinearMap ℝ (fun _ : Fin D => E) ℝ) (d : E)
    (hd : ∀ (v : Fin D → E) (j : Fin D), g (Function.update v j d) = 0) {v w : Fin D → E}
    (h : ∀ j, v j = w j ∨ v j - w j = d) : g v = g w := by
  classical
  have key (S : Finset (Fin D)) : g (S.piecewise v w) = g w := by
    induction S using Finset.induction_on with
    | empty => rw [Finset.piecewise_empty]
    | insert j S hj ih =>
      rw [Finset.piecewise_insert]
      rcases h j with e | e
      · rw [e, ← Finset.piecewise_eq_of_notMem S v w hj, Function.update_eq_self, ih]
      · have e' : v j = d + w j := by rw [← e]; abel
        rw [e', g.map_update_add, hd, zero_add, ← Finset.piecewise_eq_of_notMem S v w hj,
          Function.update_eq_self, ih]
  rw [← key Finset.univ, Finset.piecewise_univ]

theorem telescope {D : ℕ} (num : GlobalTheory.VertForm.Form E D) (hs : GlobalTheory.VertForm.IsSymm num) (x y : E) :
    num (fun _ => x) - num (fun _ => y) =
      ∑ i : Fin (D + 1), num (Fin.cons (x - y) fun j : Fin D => if (j : ℕ) < i then x else y) := by
  classical
  let vec : ℕ → Fin (D + 1) → E := fun k j => if (j : ℕ) < k then x else y
  have step : ∀ i : Fin (D + 1), num (vec ((i : ℕ) + 1)) - num (vec i) =
      num (Fin.cons (x - y) fun j : Fin D => if (j : ℕ) < i then x else y) := by
    intro i
    have e1 : vec ((i : ℕ) + 1) = Function.update (vec i) i x := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [vec]
      · rw [Function.update_of_ne hj]
        have : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
        simp only [vec]
        split_ifs <;> first | rfl | omega
    have hvi : vec i i = y := by simp [vec]
    have e2 : vec i = Function.update (vec i) i y := by rw [← hvi, Function.update_eq_self]
    have hr : i.removeNth (Function.update (vec i) i (x - y)) =
        fun j : Fin D => if (j : ℕ) < i then x else y := by
      funext j
      rw [Fin.removeNth_apply, Function.update_of_ne (Fin.succAbove_ne i j)]
      by_cases hj : (j : ℕ) < i
      · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hj)]
        simp [vec, hj]
      · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
        simp only [vec, Fin.val_succ]
        rw [if_neg (by omega), if_neg hj]
    calc num (vec ((i : ℕ) + 1)) - num (vec i)
        = num (Function.update (vec i) i x) - num (Function.update (vec i) i y) := by
          rw [← e1, ← e2]
      _ = num (Function.update (vec i) i (x - y)) := (num.map_update_sub _ _ _ _).symm
      _ = num (Function.update (vec i) i (x - y) ∘ i.cycleRange.symm) := (hs _ _).symm
      _ = _ := by
          rw [← Fin.cons_removeNth_eq_comp_cycleRange_symm, hr, Function.update_self]
  have hsum : ∑ i : Fin (D + 1), (num (vec ((i : ℕ) + 1)) - num (vec i)) =
      num (vec (D + 1)) - num (vec 0) :=
    (Fin.sum_univ_eq_sum_range (fun k => num (vec (k + 1)) - num (vec k)) (D + 1)).trans
      (Finset.sum_range_sub (fun k => num (vec k)) (D + 1))
  have hD : vec (D + 1) = fun _ => x := by funext j; simp [vec, j.isLt]
  have h0 : vec 0 = fun _ => y := by funext j; simp [vec]
  rw [← hD, ← h0, ← hsum]
  exact Finset.sum_congr rfl fun i _ => step i

end GlobalTheory.TopPowDiff

open GlobalTheory.TopPowDiff in

theorem GlobalTheory.TopPowDiff.abs_top_sub_le (E : Type 1) [AddCommGroup E] [Module ℝ E] (D : ℕ) (num : Form E D)
    (hs : IsSymm num) (G : Set E) (o x y h : E) (b : ℝ) (hx : x ∈ cone num G) (hyh : y + h ∈ cone num G)
    (hh : h ∈ cone num G)
    (hb : ∀ N : Fin D → E, (∀ j, N j ∈ G) → |num (Fin.cons (x - y) N)| ≤ b * num (Fin.cons o N))
    (hrep : ∀ (v : Fin D → E) (j : Fin D), num (Fin.cons o (Function.update v j (x - y))) = 0) :
    |num (fun _ => x) - num (fun _ => y)| ≤
      b * ∑ i : Fin (D + 1), num (Fin.cons o fun j : Fin D => if (j : ℕ) < i then y else y + (2 : ℝ) • h) := by
  rw [telescope num hs x y, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hcone := abs_le_on_cone num G (x - y) o b hb
  let fa : MultilinearMap ℝ (fun _ : Fin D => E) ℝ := num.curryLeft (x - y)
  let fo : MultilinearMap ℝ (fun _ : Fin D => E) ℝ := num.curryLeft o
  have hfa : ∀ M, fa M = num (Fin.cons (x - y) M) := fun M => MultilinearMap.curryLeft_apply num _ M
  have hfo : ∀ M, fo M = num (Fin.cons o M) := fun M => MultilinearMap.curryLeft_apply num _ M
  let P : Fin D → E := fun j => if (j : ℕ) < i then x else y + h
  let Q : Fin D → E := fun j => if (j : ℕ) < i then 0 else h
  have hPQ : (fun j : Fin D => if (j : ℕ) < i then x else y) = P - Q := by
    funext j; simp only [P, Q, Pi.sub_apply]; split_ifs <;> simp
  have hPQ' : P + Q = fun j : Fin D => if (j : ℕ) < i then x else y + (2 : ℝ) • h := by
    funext j; simp only [P, Q, Pi.add_apply]; split_ifs <;> simp [two_smul, add_assoc]
  have key := abs_sub_le_add fa (b • fo) (cone num G)
    (fun N hN => by simpa only [MultilinearMap.smul_apply, hfa, hfo, smul_eq_mul] using hcone N hN) P Q
    (fun j => by simp only [P]; split_ifs; exacts [hx, hyh])
    (fun j => by simp only [Q]; split_ifs; exacts [zero_mem_cone, hh])
  rw [MultilinearMap.smul_apply, hfa, hfo, smul_eq_mul, hPQ'] at key
  have hswap := congr_of_update_zero fo (x - y) (fun v j => by rw [hfo]; exact hrep v j)
    (v := fun j : Fin D => if (j : ℕ) < i then x else y + (2 : ℝ) • h)
    (w := fun j : Fin D => if (j : ℕ) < i then y else y + (2 : ℝ) • h)
    (fun j => by split_ifs <;> simp)
  rw [hfo, hfo] at hswap
  rw [hPQ, ← hswap]
  exact key
