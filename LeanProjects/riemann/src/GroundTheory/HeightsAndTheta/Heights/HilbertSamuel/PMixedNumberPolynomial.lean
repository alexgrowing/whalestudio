import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

namespace MixedNumberPolynomial

section Differences

variable {K : Type*}

def gStep {G : Type*} [AddCommGroup G] (b : K → ℤ) (h : (K → ℤ) → G) : (K → ℤ) → G :=
  fun m => h m - h (m - b)

theorem gStep_comm {G : Type*} [AddCommGroup G] (a b : K → ℤ) (h : (K → ℤ) → G) :
    gStep a (gStep b h) = gStep b (gStep a h) := by
  funext m
  simp only [gStep]
  rw [sub_right_comm m a b]
  abel

instance {G : Type*} [AddCommGroup G] : LeftCommutative (gStep (K := K) (G := G)) :=
  ⟨gStep_comm⟩

variable [DecidableEq K]

omit [DecidableEq K] in
theorem mixedDiff_eq {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff bs h = (List.ofFn bs).foldr gStep h := rfl

omit [DecidableEq K] in
theorem mixedDiff_cons {n : ℕ} (v : K → ℤ) (t : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff (Fin.cons v t : Fin (n + 1) → K → ℤ) h = gStep v (mixedDiff t h) := by
  simp only [mixedDiff_eq, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.foldr_cons]

theorem intNum_perm (F : Type*) [Field F] {ι : K → Type*} (q : Ideal (MRing ι F)) {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (bs : Fin d → K → ℤ) : intNum F q (bs ∘ σ) = intNum F q bs := by
  unfold intNum
  rw [mixedDiff_eq, mixedDiff_eq, (σ.ofFn_comp_perm bs).foldr_eq]

omit [DecidableEq K] in
theorem eventualValue_of_eventually {f : (K → ℤ) → ℤ} {c : ℤ} (h : ∀ᶠ m in atTop, f m = c) :
    eventualValue f = c := by
  have hex : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨c, h⟩
  unfold eventualValue
  rw [dif_pos hex]
  obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
  exact hm1.symm.trans hm2

omit [DecidableEq K] in
theorem eventually_sub {P : (K → ℤ) → Prop} (h : ∀ᶠ m in atTop, P m) (x : K → ℤ) :
    ∀ᶠ m in atTop, P (m - x) := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 h
  exact Filter.eventually_atTop.2 ⟨a + x, fun m hm => ha _ (le_sub_iff_add_le.2 hm)⟩

omit [DecidableEq K] in
theorem eventualValue_step_add (G : (K → ℤ) → ℤ) (x y : K → ℤ)
    (hx : ∃ c, ∀ᶠ m in atTop, gStep x G m = c) (hy : ∃ c, ∀ᶠ m in atTop, gStep y G m = c) :
    eventualValue (gStep (x + y) G) = eventualValue (gStep x G) + eventualValue (gStep y G) := by
  obtain ⟨cx, hcx⟩ := hx
  obtain ⟨cy, hcy⟩ := hy
  rw [eventualValue_of_eventually hcx, eventualValue_of_eventually hcy]
  apply eventualValue_of_eventually
  filter_upwards [hcx, eventually_sub hcy x] with m h1 h2
  rw [← h1, ← h2]
  simp only [gStep]
  rw [show m - x - y = m - (x + y) from sub_sub m x y]
  abel

theorem intNum_update_add (F : Type*) [Field F] {ι : K → Type*} (q : Ideal (MRing ι F)) {d : ℕ}
    (hex : ∀ bs : Fin d → K → ℤ, ∃ c, ∀ᶠ m in atTop, mixedDiff bs (hilbFn q) m = c)
    (bs : Fin d → K → ℤ) (j : Fin d) (x y : K → ℤ) :
    intNum F q (Function.update bs j (x + y)) =
      intNum F q (Function.update bs j x) + intNum F q (Function.update bs j y) := by
  cases d with
  | zero => exact j.elim0
  | succ n =>
    set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j with hσ
    set t : Fin n → K → ℤ := fun i => bs (σ i.succ) with ht
    have key : ∀ v, intNum F q (Function.update bs j v) =
        eventualValue (gStep v (mixedDiff t (hilbFn q))) := by
      intro v
      rw [← intNum_perm F q σ]
      have hc : Function.update bs j v ∘ σ = Fin.cons v t := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [hσ]
        · have hne : σ i.succ ≠ j := by
            intro hij
            have h0 : σ 0 = j := by simp [hσ]
            exact Fin.succ_ne_zero i (σ.injective (hij.trans h0.symm))
          simp only [Function.comp_apply, Fin.cons_succ, ht]
          rw [Function.update_of_ne hne]
      rw [hc]
      unfold intNum
      rw [mixedDiff_cons]
    rw [key, key, key]
    apply eventualValue_step_add
    · simpa only [mixedDiff_cons] using hex (Fin.cons x t)
    · simpa only [mixedDiff_cons] using hex (Fin.cons y t)

end Differences

section Polynomials

variable {K : Type*}

def dPoly (b : K → ℤ) (p : MvPolynomial K ℚ) : MvPolynomial K ℚ :=
  p - bind₁ (fun k => X k - C (b k : ℚ)) p

theorem eval_dPoly (b : K → ℤ) (p : MvPolynomial K ℚ) (m : K → ℤ) :
    eval (fun k => (m k : ℚ)) (dPoly b p) =
      eval (fun k => (m k : ℚ)) p - eval (fun k => ((m - b) k : ℚ)) p := by
  show aeval (fun k => (m k : ℚ)) (dPoly b p) =
    aeval (fun k => (m k : ℚ)) p - aeval (fun k => ((m - b) k : ℚ)) p
  have hx : (fun i => aeval (fun k => (m k : ℚ)) (X i - C (b i : ℚ))) =
      fun k => ((m - b) k : ℚ) := by
    funext k
    simp
  rw [dPoly, map_sub, aeval_bind₁, hx]

def Low (A : MvPolynomial K ℚ) (N : ℕ) : Prop := A = 0 ∨ A.totalDegree < N

theorem low_add {A B : MvPolynomial K ℚ} {N : ℕ} (hA : Low A N) (hB : Low B N) :
    Low (A + B) N := by
  rcases hA with hA | hA
  · simpa [hA] using hB
  rcases hB with hB | hB
  · rw [hB, add_zero]
    exact Or.inr hA
  exact Or.inr ((totalDegree_add A B).trans_lt (max_lt hA hB))

theorem low_mono {A : MvPolynomial K ℚ} {N N' : ℕ} (hA : Low A N) (h : N ≤ N') : Low A N' :=
  hA.imp id (fun h' => h'.trans_le h)

theorem low_mul_right {A B : MvPolynomial K ℚ} {N M : ℕ} (hA : Low A N) (hB : B.totalDegree ≤ M) :
    Low (A * B) (N + M) := by
  rcases hA with hA | hA
  · exact Or.inl (by simp [hA])
  exact Or.inr ((totalDegree_mul A B).trans_lt (by omega))

theorem low_mul_left {A B : MvPolynomial K ℚ} {N M : ℕ} (hB : Low B N) (hA : A.totalDegree ≤ M) :
    Low (A * B) (M + N) := by
  rw [mul_comm, add_comm]
  exact low_mul_right hB hA

theorem dPoly_mul (b : K → ℤ) (A B : MvPolynomial K ℚ) :
    dPoly b (A * B) = dPoly b A * B + (A - dPoly b A) * dPoly b B := by
  simp only [dPoly, map_mul]
  ring

theorem totalDegree_sub_dPoly_le {b : K → ℤ} {A : MvPolynomial K ℚ} {N : ℕ}
    (hd : A.totalDegree ≤ N) (hl : Low (dPoly b A) N) : (A - dPoly b A).totalDegree ≤ N := by
  refine (totalDegree_sub _ _).trans (max_le hd ?_)
  rcases hl with hl | hl
  · simp [hl]
  · exact hl.le

theorem low_dPoly_mul {b : K → ℤ} {A B : MvPolynomial K ℚ} {α β : ℕ}
    (hA : Low (dPoly b A) α) (hB : Low (dPoly b B) β) (hdA : A.totalDegree ≤ α)
    (hdB : B.totalDegree ≤ β) : Low (dPoly b (A * B)) (α + β) := by
  rw [dPoly_mul]
  exact low_add (low_mul_right hA hdB) (low_mul_left hB (totalDegree_sub_dPoly_le hdA hA))

theorem low_dPoly_monomial (b : K → ℤ) (s : K →₀ ℕ) (a : ℚ) :
    Low (dPoly b (monomial s a)) (monomial s a).totalDegree := by
  refine MvPolynomial.induction_on_monomial
    (motive := fun p => Low (dPoly b p) p.totalDegree) (fun a => ?_) (fun p n ih => ?_) s a
  · exact Or.inl (by simp [dPoly])
  · by_cases hp : p = 0
    · exact Or.inl (by simp [hp, dPoly])
    show Low (dPoly b (p * X n)) (p * X n).totalDegree
    rw [totalDegree_mul_of_isDomain hp (X_ne_zero n), totalDegree_X]
    refine low_dPoly_mul ih (Or.inr ?_) le_rfl (totalDegree_X n).le
    have hXn : dPoly b (X n) = C (b n : ℚ) := by simp [dPoly]
    rw [hXn, totalDegree_C]
    exact Nat.zero_lt_one

theorem low_dPoly (b : K → ℤ) (p : MvPolynomial K ℚ) : Low (dPoly b p) p.totalDegree := by
  have hsum : dPoly b p = ∑ s ∈ p.support, dPoly b (monomial s (coeff s p)) := by
    simp only [dPoly]
    conv_lhs => rw [p.as_sum]
    rw [map_sum, ← Finset.sum_sub_distrib]
  rw [hsum]
  refine Finset.sum_induction _ (fun A => Low A p.totalDegree) (fun _ _ => low_add)
    (Or.inl rfl) (fun s hs => low_mono (low_dPoly_monomial b s _) ?_)
  exact (totalDegree_monomial_le s _).trans (le_totalDegree hs)

theorem totalDegree_dPoly_le (b : K → ℤ) (p : MvPolynomial K ℚ) :
    (dPoly b p).totalDegree ≤ p.totalDegree - 1 := by
  rcases low_dPoly b p with h | h
  · simp [h]
  · omega

theorem totalDegree_foldr_dPoly_le (l : List (K → ℤ)) (p : MvPolynomial K ℚ) :
    (l.foldr dPoly p).totalDegree ≤ p.totalDegree - l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, List.length_cons]
    have := totalDegree_dPoly_le b (l.foldr dPoly p)
    omega

theorem foldr_gStep_eval (l : List (K → ℤ)) (p : MvPolynomial K ℚ) (m : K → ℤ) :
    l.foldr gStep (fun m : K → ℤ => eval (fun k => (m k : ℚ)) p) m =
      eval (fun k => (m k : ℚ)) (l.foldr dPoly p) := by
  induction l generalizing m with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldr_cons, gStep, ih, eval_dPoly]

theorem foldr_gStep_cast (l : List (K → ℤ)) (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    ((l.foldr gStep h m : ℤ) : ℚ) = l.foldr gStep (fun m => (h m : ℚ)) m := by
  induction l generalizing m with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldr_cons, gStep]
    push_cast
    rw [ih, ih]

theorem foldr_gStep_congr {G : Type*} [AddCommGroup G] (l : List (K → ℤ)) {h h' : (K → ℤ) → G}
    (hh : ∀ᶠ m in atTop, h m = h' m) :
    ∀ᶠ m in atTop, l.foldr gStep h m = l.foldr gStep h' m := by
  induction l with
  | nil => simpa using hh
  | cons b l ih =>
    filter_upwards [ih, eventually_sub ih b] with m h1 h2
    simp only [List.foldr_cons, gStep, h1, h2]

end Polynomials

theorem exists_eventually_const (h : MultigradedHilbertPolynomial.Statement.{u}) (F : Type u)
    [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (q : Ideal (MRing ι F)) (d : ℕ) (hq : IsMultiProjPrime q)
    (hdim : ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞))
    (bs : Fin d → K → ℤ) : ∃ c, ∀ᶠ m in atTop, mixedDiff bs (hilbFn q) m = c := by
  obtain ⟨p, a₀, hdeg, hp⟩ := h F K ι q d hq hdim
  have hev : ∀ᶠ m in atTop, ((hilbFn q m : ℤ) : ℚ) = eval (fun k => (m k : ℚ)) p := by
    filter_upwards [eventually_ge_atTop (fun _ : K => (a₀ : ℤ))] with m hm
    have hm' : ∀ k, (a₀ : ℤ) ≤ m k := fun k => hm k
    have e1 : (fun k => (((m k).toNat : ℕ) : ℤ)) = m :=
      funext fun k => Int.toNat_of_nonneg (by have := hm' k; omega)
    have e2 : (fun k => (((m k).toNat : ℕ) : ℚ)) = fun k => (m k : ℚ) := by
      funext k
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by have := hm' k; omega)]
    have := hp (fun k => (m k).toNat) (fun k => by have := hm' k; omega)
    rw [e1, e2] at this
    exact this
  set P := (List.ofFn bs).foldr dPoly p with hP
  have hP0 : P.totalDegree = 0 := by
    have := totalDegree_foldr_dPoly_le (List.ofFn bs) p
    rw [List.length_ofFn, ← hP] at this
    exact Nat.eq_zero_of_le_zero (this.trans (Nat.sub_eq_zero_of_le hdeg).le)
  obtain ⟨c, hc⟩ : ∃ c, P = C c := ⟨_, totalDegree_eq_zero_iff_eq_C.1 hP0⟩
  have hconst : ∀ᶠ m in atTop, ((mixedDiff bs (hilbFn q) m : ℤ) : ℚ) = c := by
    filter_upwards [foldr_gStep_congr (List.ofFn bs) hev] with m hm
    rw [mixedDiff_eq, foldr_gStep_cast, hm, foldr_gStep_eval, ← hP, hc, eval_C]
  obtain ⟨m₀, hm₀⟩ := hconst.exists
  refine ⟨mixedDiff bs (hilbFn q) m₀, ?_⟩
  filter_upwards [hconst] with m hm
  exact_mod_cast hm.trans hm₀.symm

end MixedNumberPolynomial

theorem MixedNumberPolynomial.proof (h : MultigradedHilbertPolynomial.Statement.{u}) :
    MixedNumberPolynomial.Statement.{u} := by
  intro F _ K _ _ ι _ q d hq hdim
  exact ⟨fun σ bs => MixedNumberPolynomial.intNum_perm F q σ bs,
    fun bs j x y => MixedNumberPolynomial.intNum_update_add F q
      (MixedNumberPolynomial.exists_eventually_const h F K ι q d hq hdim) bs j x y⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
