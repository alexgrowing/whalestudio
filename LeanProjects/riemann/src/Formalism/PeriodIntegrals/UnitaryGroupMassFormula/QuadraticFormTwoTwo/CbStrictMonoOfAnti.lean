import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.InLieW

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cb_anti_of_succ {n : ℕ} {a : ℕ → ℝ} (ha : ∀ i, 1 ≤ i → i + 1 ≤ n → a (i + 1) < a i) :
    ∀ i j, 1 ≤ i → i < j → j ≤ n → a j < a i := by
  intro i j hi hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h : i < j
    · exact lt_trans (ha j (by omega) hj) (ih h (by omega))
    · have e : i = j := by omega
      rw [e]
      exact ha j (by omega) hj

theorem cb_mem_of_prod_eq {n : ℕ} {a b : ℕ → ℝ}
    (h : ∀ Y : ℂ, ∏ i ∈ Icc 1 n, (Y + (a i : ℂ)) = ∏ i ∈ Icc 1 n, (Y + (b i : ℂ))) :
    ∀ i ∈ Icc 1 n, ∃ j ∈ Icc 1 n, a i = b j := by
  intro i hi
  have h0 := h (-(a i : ℂ))
  have hl : ∏ l ∈ Icc 1 n, (-(a i : ℂ) + (a l : ℂ)) = 0 := Finset.prod_eq_zero hi (by ring)
  rw [hl] at h0
  obtain ⟨j, hj, hz⟩ := Finset.prod_eq_zero_iff.mp h0.symm
  refine ⟨j, hj, ?_⟩
  have e : ((b j : ℝ) : ℂ) = (a i : ℂ) := by linear_combination hz
  exact_mod_cast e.symm

theorem cb_range_sub_of_mem {n : ℕ} {a b : ℕ → ℝ} (hm : ∀ i ∈ Icc 1 n, ∃ j ∈ Icc 1 n, a i = b j) :
    Set.range (fun j : Fin n => -a (j.1 + 1)) ⊆ Set.range (fun j : Fin n => -b (j.1 + 1)) := by
  rintro x ⟨j, rfl⟩
  obtain ⟨l, hl, hab⟩ := hm (j.val + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩)
  have hl1 := (Finset.mem_Icc.mp hl).1
  have hl2 := (Finset.mem_Icc.mp hl).2
  refine ⟨⟨l - 1, by omega⟩, ?_⟩
  show -b (l - 1 + 1) = -a (j.val + 1)
  rw [hab, Nat.sub_add_cancel hl1]

theorem cb_strictMono_of_anti {n : ℕ} {a : ℕ → ℝ} (ha : ∀ i, 1 ≤ i → i + 1 ≤ n → a (i + 1) < a i) :
    StrictMono (fun j : Fin n => -a (j.1 + 1)) := by
  intro i j hij
  have h' : i.val < j.val := hij
  have hjn := j.isLt
  have := cb_anti_of_succ ha (i.val + 1) (j.val + 1) (by omega) (by omega) (by omega)
  show -a (i.val + 1) < -a (j.val + 1)
  linarith

theorem cb_eq_of_prod_eq {n : ℕ} {a b : ℕ → ℝ}
    (ha : ∀ i, 1 ≤ i → i + 1 ≤ n → a (i + 1) < a i) (hb : ∀ i, 1 ≤ i → i + 1 ≤ n → b (i + 1) < b i)
    (h : ∀ Y : ℂ, ∏ i ∈ Icc 1 n, (Y + (a i : ℂ)) = ∏ i ∈ Icc 1 n, (Y + (b i : ℂ))) :
    ∀ i ∈ Icc 1 n, a i = b i := by
  have hr : Set.range (fun j : Fin n => -a (j.1 + 1)) = Set.range (fun j : Fin n => -b (j.1 + 1)) :=
    Set.Subset.antisymm (cb_range_sub_of_mem (cb_mem_of_prod_eq h))
      (cb_range_sub_of_mem (cb_mem_of_prod_eq (fun Y => (h Y).symm)))
  have hf := ((cb_strictMono_of_anti ha).range_inj (cb_strictMono_of_anti hb)).mp hr
  intro i hi
  have h1 := (Finset.mem_Icc.mp hi).1
  have h1' := (Finset.mem_Icc.mp hi).2
  have h2 : -a (i - 1 + 1) = -b (i - 1 + 1) := congrFun hf ⟨i - 1, by omega⟩
  rw [Nat.sub_add_cancel h1] at h2
  linarith

theorem cb_rho_eq' (Q : M.Par) (π : M.Ty Q) (j : Fin (Q.k - 1)) :
    M.rho Q π (j.1 + 1) = Q.lo (j.1 + 1) + (((π j : Fin _) : ℕ) : ℝ) := by
  unfold M.rho
  rw [dif_pos ⟨by omega, by have := j.isLt; omega⟩]
  first
    | rfl
    | simp

theorem cb_ofIcc {n i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n) : ∃ j : Fin n, i = j.1 + 1 := by
  exact ⟨⟨i - 1, by omega⟩, by show i = i - 1 + 1; omega⟩

theorem cb_rho_bounds (Q : M.Par) (hg : ∀ i ∈ Icc 1 (Q.k - 1), Q.lo i ≤ Q.hi i) (π : M.Ty Q)
    (j : Fin (Q.k - 1)) : Q.lo (j.1 + 1) ≤ M.rho Q π (j.1 + 1) ∧ M.rho Q π (j.1 + 1) ≤ Q.hi (j.1 + 1) := by
  rw [cb_rho_eq' Q π j]
  have hj := j.2
  have hw : ((π j : Fin _) : ℕ) ≤ Q.wid (j.1 + 1) := by have := (π j).2; omega
  have hg' := hg (j.1 + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hf : ((Q.wid (j.1 + 1) : ℕ) : ℝ) ≤ Q.hi (j.1 + 1) - Q.lo (j.1 + 1) :=
    Nat.floor_le (sub_nonneg.mpr hg')
  have hw' : (((π j : Fin _) : ℕ) : ℝ) ≤ (Q.wid (j.1 + 1) : ℝ) := by exact_mod_cast hw
  have h0 : (0 : ℝ) ≤ (((π j : Fin _) : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

theorem cb_rho_anti (Q : M.Par) (hg : ∀ i ∈ Icc 1 (Q.k - 1), Q.lo i ≤ Q.hi i) (π : M.Ty Q) :
    ∀ i, 1 ≤ i → i + 1 ≤ Q.k - 1 → M.rho Q π (i + 1) < M.rho Q π i := by
  intro i h1 h2
  obtain ⟨j, rfl⟩ := cb_ofIcc (n := Q.k - 1) h1 (by omega)
  have b1 := (cb_rho_bounds Q hg π ⟨j.1 + 1, by omega⟩).2
  have b0 := (cb_rho_bounds Q hg π j).1
  have hm := min_le_max (a := Q.u (j.1 + 1 + 1)) (b := Q.u' (j.1 + 1 + 1))
  have e1 : Q.hi (j.1 + 1 + 1) = min (Q.u (j.1 + 1 + 1)) (Q.u' (j.1 + 1 + 1)) - 1 / 2 := rfl
  have e2 : Q.lo (j.1 + 1) = max (Q.u (j.1 + 1 + 1)) (Q.u' (j.1 + 1 + 1)) + 1 / 2 := rfl
  simp only at b1
  linarith

theorem cb_ty_ext (Q : M.Par) {π π' : M.Ty Q}
    (h : ∀ j : Fin (Q.k - 1), M.rho Q π (j.1 + 1) = M.rho Q π' (j.1 + 1)) : π = π' := by
  funext j
  apply Fin.ext
  have e := h j
  rw [cb_rho_eq' Q π j, cb_rho_eq' Q π' j] at e
  exact_mod_cast add_left_cancel e

theorem cb_exists_ty (Q : M.Par) (v : ℕ → ℝ)
    (hv : ∀ j : Fin (Q.k - 1), Q.lo (j.1 + 1) ≤ v (j.1 + 1) ∧ v (j.1 + 1) ≤ Q.hi (j.1 + 1) ∧
      ∃ n : ℤ, v (j.1 + 1) - Q.lo (j.1 + 1) = n) :
    ∃ τ : M.Ty Q, ∀ j : Fin (Q.k - 1), M.rho Q τ (j.1 + 1) = v (j.1 + 1) := by
  refine ⟨fun j => ⟨⌊v (j.1 + 1) - Q.lo (j.1 + 1)⌋₊, ?_⟩, ?_⟩
  · obtain ⟨h1, h2, -⟩ := hv j
    have : ⌊v (j.1 + 1) - Q.lo (j.1 + 1)⌋₊ ≤ Q.wid (j.1 + 1) := by
      unfold M.Par.wid
      exact Nat.floor_le_floor (by linarith)
    omega
  · intro j
    rw [cb_rho_eq' Q _ j]
    obtain ⟨h1, -, n, hn⟩ := hv j
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := hn ▸ sub_nonneg.mpr h1
    have hn0' : (0 : ℤ) ≤ n := by exact_mod_cast hn0
    lift n to ℕ using hn0'
    rw [Int.cast_natCast] at hn
    show Q.lo (j.1 + 1) + ((⌊v (j.1 + 1) - Q.lo (j.1 + 1)⌋₊ : ℕ) : ℝ) = v (j.1 + 1)
    rw [hn, Nat.floor_natCast]
    linarith

theorem cb_lo_int (Q : M.Par) (c : ℝ) (i : ℕ) (hu : ∃ n : ℤ, Q.u (i + 1) - c = n)
    (hu' : ∃ n : ℤ, Q.u' (i + 1) - c = n) : ∃ n : ℤ, Q.lo i - (c + 1 / 2) = n := by
  unfold M.Par.lo
  rcases max_choice (Q.u (i + 1)) (Q.u' (i + 1)) with h | h <;> rw [h]
  · obtain ⟨n, hn⟩ := hu
    exact ⟨n, by linarith⟩
  · obtain ⟨n, hn⟩ := hu'
    exact ⟨n, by linarith⟩

theorem cb_rho_int (Q : M.Par) (c : ℝ) (τ : M.Ty Q) (j : Fin (Q.k - 1))
    (h : ∃ n : ℤ, Q.lo (j.1 + 1) - c = n) : ∃ n : ℤ, M.rho Q τ (j.1 + 1) - c = n := by
  rw [cb_rho_eq' Q τ j]
  obtain ⟨n, hn⟩ := h
  exact ⟨n + ((τ j : Fin _) : ℕ), by push_cast; linarith⟩

theorem cb_int_sub {x y c : ℝ} (hx : ∃ n : ℤ, x - c = n) (hy : ∃ n : ℤ, y - c = n) :
    ∃ n : ℤ, x - y = n := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨l, hl⟩ := hy
  exact ⟨m - l, by push_cast; linarith⟩

theorem Pp_OK {P : M.Par} (hP : P.OK) : (Pp P).OK := by
  have h1 : (1 : ℕ) ∈ Icc 1 P.k := Finset.mem_Icc.mpr ⟨le_rfl, hP.k_pos⟩
  obtain ⟨b, hb⟩ := hP.int_u' 1 h1
  refine ⟨hP.k_pos, hP.T_pos, hP.T'_pos, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, ha⟩ := hP.int_u' i hi
    exact ⟨a - b, by show P.u' i - P.u' 1 = _; push_cast; linarith⟩
  · intro i hi
    obtain ⟨a, ha⟩ := hP.int_u' i hi
    exact ⟨a - b, by show P.u' i - P.u' 1 = _; push_cast; linarith⟩
  · intro i hi
    have g := hP.gap i hi
    show max (P.u' (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ min (P.u' i) (P.u' i) - 1 / 2
    have e1 : P.lo i = max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2 := rfl
    have e2 : P.hi i = min (P.u i) (P.u' i) - 1 / 2 := rfl
    rw [max_self, min_self]
    have := le_max_right (P.u (i + 1)) (P.u' (i + 1))
    have := min_le_right (P.u i) (P.u' i)
    linarith

theorem Pq_OK {P : M.Par} (hP : P.OK) : (Pq P).OK := by
  refine ⟨hP.k_pos, hP.T_pos, hP.T'_pos, ?_, ?_, ?_⟩
  · exact hP.int_u
  · exact hP.int_u
  · intro i hi
    have g := hP.gap i hi
    show max (P.u (i + 1)) (P.u (i + 1)) + 1 / 2 ≤ min (P.u i) (P.u i) - 1 / 2
    have e1 : P.lo i = max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2 := rfl
    have e2 : P.hi i = min (P.u i) (P.u' i) - 1 / 2 := rfl
    rw [max_self, min_self]
    have := le_max_left (P.u (i + 1)) (P.u' (i + 1))
    have := min_le_left (P.u i) (P.u' i)
    linarith

theorem cb_lo_le_of (P : M.Par) (i : ℕ) (x : ℝ) (h1 : (Pp P).lo i ≤ x) (h2 : (Pq P).lo i ≤ x) :
    P.lo i ≤ x := by
  change max (P.u' (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ x at h1
  change max (P.u (i + 1)) (P.u (i + 1)) + 1 / 2 ≤ x at h2
  rw [max_self] at h1 h2
  show max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ x
  have := max_le (show P.u (i + 1) ≤ x - 1 / 2 by linarith) (show P.u' (i + 1) ≤ x - 1 / 2 by linarith)
  linarith

theorem cb_le_hi_of (P : M.Par) (i : ℕ) (x : ℝ) (h1 : x ≤ (Pp P).hi i) (h2 : x ≤ (Pq P).hi i) :
    x ≤ P.hi i := by
  change x ≤ min (P.u' i) (P.u' i) - 1 / 2 at h1
  change x ≤ min (P.u i) (P.u i) - 1 / 2 at h2
  rw [min_self] at h1 h2
  show x ≤ min (P.u i) (P.u' i) - 1 / 2
  have := le_min (show x + 1 / 2 ≤ P.u i by linarith) (show x + 1 / 2 ≤ P.u' i by linarith)
  linarith

theorem cb_lo_Pp_le (P : M.Par) (i : ℕ) : (Pp P).lo i ≤ P.lo i := by
  show max (P.u' (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2
  rw [max_self]
  linarith [le_max_right (P.u (i + 1)) (P.u' (i + 1))]

theorem cb_hi_le_Pp (P : M.Par) (i : ℕ) : P.hi i ≤ (Pp P).hi i := by
  show min (P.u i) (P.u' i) - 1 / 2 ≤ min (P.u' i) (P.u' i) - 1 / 2
  rw [min_self]
  linarith [min_le_right (P.u i) (P.u' i)]

theorem comb_match {P : M.Par} (hP : P.OK) :
    ∃ f : M.Ty P → M.Ty (Pp P), Function.Injective f ∧ (∀ (ρ : M.Ty P) (Y : ℂ), M.xC (Pp P) (f ρ) Y = M.xC P ρ Y) ∧
      ∀ (σ : M.Ty (Pp P)) (ρ : M.Ty (Pq P)), (∀ Y : ℂ, M.xC (Pp P) σ Y = M.xC (Pq P) ρ Y) → σ ∈ Set.range f := by
  have gP : ∀ i ∈ Icc 1 (P.k - 1), P.lo i ≤ P.hi i := hP.gap
  have gPp : ∀ i ∈ Icc 1 ((Pp P).k - 1), (Pp P).lo i ≤ (Pp P).hi i := (Pp_OK hP).gap
  have gPq : ∀ i ∈ Icc 1 ((Pq P).k - 1), (Pq P).lo i ≤ (Pq P).hi i := (Pq_OK hP).gap
  have hu : ∀ j : Fin (P.k - 1), ∃ n : ℤ, P.u (j.1 + 1 + 1) - P.u 1 = n := fun j =>
    hP.int_u _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)
  have hu' : ∀ j : Fin (P.k - 1), ∃ n : ℤ, P.u' (j.1 + 1 + 1) - P.u 1 = n := fun j =>
    hP.int_u' _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)
  have zP : ∀ j : Fin (P.k - 1), ∃ n : ℤ, P.lo (j.1 + 1) - (P.u 1 + 1 / 2) = n := fun j =>
    cb_lo_int P _ _ (hu j) (hu' j)
  have zPp : ∀ j : Fin (P.k - 1), ∃ n : ℤ, (Pp P).lo (j.1 + 1) - (P.u 1 + 1 / 2) = n := fun j =>
    cb_lo_int (Pp P) _ _ (hu' j) (hu' j)
  have hf : ∀ ρ : M.Ty P, ∃ σ : M.Ty (Pp P),
      ∀ j : Fin (P.k - 1), M.rho (Pp P) σ (j.1 + 1) = M.rho P ρ (j.1 + 1) := by
    intro ρ
    refine cb_exists_ty (Pp P) (fun i => M.rho P ρ i) (fun j => ⟨?_, ?_, ?_⟩)
    · exact (cb_lo_Pp_le P _).trans (cb_rho_bounds P gP ρ j).1
    · exact (cb_rho_bounds P gP ρ j).2.trans (cb_hi_le_Pp P _)
    · exact cb_int_sub (cb_rho_int P _ ρ j (zP j)) (zPp j)
  choose f hf using hf
  refine ⟨f, ?_, ?_, ?_⟩
  · intro ρ ρ' h
    apply cb_ty_ext P
    intro j
    rw [← hf ρ j, ← hf ρ' j, h]
  · intro ρ Y
    unfold M.xC
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨j, rfl⟩ := cb_ofIcc (n := P.k - 1) hi.1 hi.2
    rw [hf ρ j]
  · intro σ τ hx
    have hst : ∀ i ∈ Icc 1 (P.k - 1), M.rho (Pp P) σ i = M.rho (Pq P) τ i :=
      cb_eq_of_prod_eq (n := P.k - 1) (cb_rho_anti (Pp P) gPp σ) (cb_rho_anti (Pq P) gPq τ) (fun Y => hx Y)
    obtain ⟨ρ, hρ⟩ := cb_exists_ty P (fun i => M.rho (Pp P) σ i) (fun j => by
      have e := hst (j.1 + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)
      have bσ := cb_rho_bounds (Pp P) gPp σ j
      have bτ := cb_rho_bounds (Pq P) gPq τ j
      rw [← e] at bτ
      refine ⟨cb_lo_le_of P _ _ bσ.1 bτ.1, cb_le_hi_of P _ _ bσ.2 bτ.2, ?_⟩
      exact cb_int_sub (cb_rho_int (Pp P) _ σ j (zPp j)) (zP j))
    refine ⟨ρ, cb_ty_ext (Pp P) (fun j => ?_)⟩
    rw [hf ρ j, hρ j]

def cb_xPoly (Q : M.Par) (σ : M.Ty Q) : Polynomial ℂ :=
  ∏ i ∈ Icc 1 (Q.k - 1), (Polynomial.X + Polynomial.C ((M.rho Q σ i : ℝ) : ℂ))

theorem cb_eval_xPoly (Q : M.Par) (σ : M.Ty Q) (Y : ℂ) : (cb_xPoly Q σ).eval Y = M.xC Q σ Y := by
  unfold cb_xPoly M.xC
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

theorem exists_sep {P : M.Par} (hP : P.OK) :
    ∃ Y₀ : ℂ, Function.Injective (fun σ : M.Ty (Pp P) => M.xC (Pp P) σ Y₀) := by
  classical
  have gPp : ∀ i ∈ Icc 1 ((Pp P).k - 1), (Pp P).lo i ≤ (Pp P).hi i := (Pp_OK hP).gap
  have hne : ∀ σ σ' : M.Ty (Pp P), σ ≠ σ' → cb_xPoly (Pp P) σ - cb_xPoly (Pp P) σ' ≠ 0 := by
    intro σ σ' hss h0
    apply hss
    have hx : ∀ Y, M.xC (Pp P) σ Y = M.xC (Pp P) σ' Y := by
      intro Y
      rw [← cb_eval_xPoly, ← cb_eval_xPoly, sub_eq_zero.mp h0]
    have e := cb_eq_of_prod_eq (n := (Pp P).k - 1) (cb_rho_anti _ gPp σ) (cb_rho_anti _ gPp σ') hx
    exact cb_ty_ext _ (fun j => e _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩))
  obtain ⟨Y₀, hY⟩ := Infinite.exists_notMem_finset
    ((Finset.univ : Finset (M.Ty (Pp P) × M.Ty (Pp P))).biUnion
      (fun p => if p.1 = p.2 then ∅ else (cb_xPoly (Pp P) p.1 - cb_xPoly (Pp P) p.2).roots.toFinset))
  refine ⟨Y₀, fun σ σ' h => ?_⟩
  by_contra hss
  apply hY
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨(σ, σ'), ?_⟩
  rw [if_neg hss, Multiset.mem_toFinset, Polynomial.mem_roots (hne σ σ' hss), Polynomial.IsRoot.def,
    Polynomial.eval_sub, cb_eval_xPoly, cb_eval_xPoly, sub_eq_zero]
  exact h

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
