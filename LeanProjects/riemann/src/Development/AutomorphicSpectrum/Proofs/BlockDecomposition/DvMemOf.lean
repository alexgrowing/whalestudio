import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCech

universe w

variable {R : Type} [CommRing R]

structure DFil (K : DCx.{w} R) where
  L : ℤ → ∀ p q, Submodule R (K.X p q)
  mem_h : ∀ r p q x, x ∈ L r p q → K.dh p q x ∈ L r (p + 1) q
  mem_v : ∀ r p q x, x ∈ L r p q → K.dv p q x ∈ L r p (q + 1)
  anti : ∀ {r r' : ℤ}, r ≤ r' → ∀ p q, L r' p q ≤ L r p q

def DFil.Ex {K : DCx.{w} R} (F : DFil K) (r : ℤ) (p : ℕ) : ℕ → Prop
  | 0 => ∀ x ∈ F.L r p 0, K.dv p 0 x ∈ F.L (r + 1) p 1 → x ∈ F.L (r + 1) p 0
  | q + 1 => ∀ x ∈ F.L r p (q + 1), K.dv p (q + 1) x ∈ F.L (r + 1) p (q + 2) →
      ∃ v ∈ F.L r p q, x - K.dv p q v ∈ F.L (r + 1) p (q + 1)

variable {K : DCx.{w} R} (F : DFil K)

theorem sgl_mem {r : ℤ} {p q : ℕ} {x : K.X p q} (hx : x ∈ F.L r p q) (a b : ℕ) : K.sgl p q x a b ∈ F.L r a b := by
  by_cases h : a = p ∧ b = q
  · obtain ⟨rfl, rfl⟩ := h
    rwa [K.sgl_self]
  · rw [K.sgl_ne x (by omega)]
    exact zero_mem _

theorem dv_mem_of {r : ℤ} {e q : ℕ} (y : ∀ p q, K.X p q) (h1 : K.D y e (q + 1) ∈ F.L r e (q + 1))
    (h2 : ∀ e', e = e' + 1 → y e' (q + 1) ∈ F.L r e' (q + 1)) : K.dv e q (y e q) ∈ F.L r e (q + 1) := by
  have h3 : K.Dh y e (q + 1) ∈ F.L r e (q + 1) := by
    cases e with
    | zero => exact zero_mem _
    | succ e => exact F.mem_h _ _ _ _ (h2 e rfl)
  rw [K.D_apply] at h1
  have h4 : (-1 : ℤ) ^ e • K.dv e q (y e q) ∈ F.L r e (q + 1) := (Submodule.add_mem_iff_right _ h3).1 h1
  rcases neg_one_pow_eq_or ℤ e with h | h <;> rw [h] at h4 <;> simpa using h4

theorem kill (r : ℤ) (m : ℕ) (y : ∀ p q, K.X p q) (hy : y ∈ K.T (m + 1)) (hyL : ∀ p q, y p q ∈ F.L r p q) :
    ∀ e : ℕ, (∀ p q, p < e → K.D y p q ∈ F.L (r + 1) p q) → (∀ p q, p < e → p + q = m + 1 → F.Ex r p q) →
      ∃ w ∈ K.T m, (∀ p q, e ≤ p → w p q = 0) ∧ (∀ p q, (y - K.D w) p q ∈ F.L r p q) ∧
        ∀ p q, p < e → (y - K.D w) p q ∈ F.L (r + 1) p q := by
  intro e
  induction e with
  | zero =>
    intro _ _
    refine ⟨0, zero_mem _, fun _ _ _ => rfl, fun p q => ?_, fun p q h => absurd h (by omega)⟩
    simpa using hyL p q
  | succ e ih =>
    intro hD hE
    obtain ⟨w, hwT, hw0, hwL, hwL'⟩ := ih (fun p q hp => hD p q (by omega)) (fun p q hp => hE p q (by omega))
    have hyT : y - K.D w ∈ K.T (m + 1) := sub_mem hy (K.D_mem m w hwT)
    have hDy : K.D (y - K.D w) = K.D y := by rw [map_sub, K.DD, sub_zero]
    generalize hy' : y - K.D w = y' at hyT hDy hwL hwL'
    by_cases he : e ≤ m + 1
    · obtain ⟨q, hq⟩ : ∃ q, e + q = m + 1 := ⟨m + 1 - e, by omega⟩
      have hx : K.dv e q (y' e q) ∈ F.L (r + 1) e (q + 1) :=
        dv_mem_of F y' (by rw [hDy]; exact hD e (q + 1) (by omega)) (fun e' h => hwL' e' (q + 1) (by omega))
      have hEx := hE e q (by omega) hq
      cases q with
      | zero =>
        have hx0 : y' e 0 ∈ F.L (r + 1) e 0 := hEx _ (hwL e 0) hx
        refine ⟨w, hwT, fun p q h => hw0 p q (by omega), by rw [hy']; exact hwL, fun p q hp => ?_⟩
        rw [hy']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
        · exact hwL' p q hp
        · by_cases hq0 : q = 0
          · subst hq0; exact hx0
          · rw [hyT p q (by omega)]; exact zero_mem _
      | succ q =>
        obtain ⟨v, hv, hxv⟩ := hEx _ (hwL e (q + 1)) hx
        have hDu : K.D ((-1 : ℤ) ^ e • K.sgl e q v) =
            (-1 : ℤ) ^ e • K.sgl (e + 1) q (K.dh e q v) + K.sgl e (q + 1) (K.dv e q v) := by
          rw [map_zsmul, K.D_sgl, smul_add, smul_smul, ← pow_add, ← two_mul, pow_mul]
          simp
        have hval : ∀ p q', (y - K.D (w + (-1 : ℤ) ^ e • K.sgl e q v)) p q' =
            y' p q' - (-1 : ℤ) ^ e • K.sgl (e + 1) q (K.dh e q v) p q' - K.sgl e (q + 1) (K.dv e q v) p q' := by
          intro p q'
          rw [map_add, hDu, ← sub_sub, hy']
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
          abel
        refine ⟨w + (-1 : ℤ) ^ e • K.sgl e q v, add_mem hwT (?_), fun p q' h => ?_, fun p q' => ?_, fun p q' hp => ?_⟩
        · refine (K.T m).smul_of_tower_mem _ ?_
          intro a b hab
          exact K.sgl_ne v (by omega)
        · simp only [Pi.add_apply, Pi.smul_apply]
          rw [hw0 p q' (by omega), K.sgl_ne v (Or.inl (by omega))]
          simp
        · rw [hval]
          exact sub_mem (sub_mem (hwL p q') ((F.L r p q').smul_of_tower_mem _ (sgl_mem F (F.mem_h _ _ _ _ hv) p q')))
            (sgl_mem F (F.mem_v _ _ _ _ hv) p q')
        · rw [hval]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
          · rw [K.sgl_ne _ (Or.inl (by omega)), K.sgl_ne _ (Or.inl (by omega))]
            simpa using hwL' p q' hp
          · rw [K.sgl_ne _ (Or.inl (by omega))]
            by_cases hq0 : q' = q + 1
            · subst hq0
              rw [K.sgl_self]
              simpa using hxv
            · rw [K.sgl_ne _ (Or.inr hq0), hyT p q' (by omega)]
              simp
    · refine ⟨w, hwT, fun p q h => hw0 p q (by omega), by rw [hy']; exact hwL, fun p q hp => ?_⟩
      rw [hy']
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
      · exact hwL' p q hp
      · rw [hyT p q (by omega)]; exact zero_mem _

theorem stair_up (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤) (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q))
    (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q) (P : K.X (n + 1) (n + 1)) (hP : P ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (y0 : ∀ p q, K.X p q) (hy0 : y0 ∈ K.T (2 * n + 1)) (hD : K.D y0 = K.sgl (n + 1) (n + 1) P) (r : ℕ) (hr : r ≤ n) :
    ∃ y ∈ K.T (2 * n + 1), K.D y = K.sgl (n + 1) (n + 1) P ∧ ∀ p q, y p q ∈ F.L (r : ℤ) p q := by
  induction r with
  | zero =>
    refine ⟨y0, hy0, hD, fun p q => ?_⟩
    rw [Nat.cast_zero, hTop]
    trivial
  | succ r ih =>
    obtain ⟨y, hyT, hDy, hyL⟩ := ih (by omega)
    have hPr : P ∈ F.L ((r : ℤ) + 1) (n + 1) (n + 1) := F.anti (by omega) _ _ hP
    obtain ⟨w, hwT, -, hwL, hwL'⟩ := kill F (r : ℤ) (2 * n) y hyT hyL (n + 2)
      (fun p q _ => by rw [hDy]; exact sgl_mem F hPr p q)
      (fun p q hp hq => hE r p q (by omega))
    refine ⟨y - K.D w, sub_mem hyT (K.D_mem _ w hwT), by rw [map_sub, K.DD, sub_zero, hDy], fun p q => ?_⟩
    rw [Nat.cast_succ]
    by_cases hp : p < n + 2
    · exact hwL' p q hp
    · have := hV p q (by omega)
      rw [Subsingleton.elim ((y - K.D w) p q) 0]
      exact zero_mem _

theorem stair (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤) (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q))
    (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q) (P : K.X (n + 1) (n + 1)) (hP : P ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (y0 : ∀ p q, K.X p q) (hy0 : y0 ∈ K.T (2 * n + 1)) (hD : K.D y0 = K.sgl (n + 1) (n + 1) P) :
    ∃ (ω : K.X n (n + 1)) (f : K.X (n + 1) n), ω ∈ F.L ((n : ℤ) + 1) n (n + 1) ∧
      K.dv n (n + 1) ω ∈ F.L ((n : ℤ) + 1 + 1) n (n + 2) ∧ f ∈ F.L (n : ℤ) (n + 1) n ∧
      P = K.dh n (n + 1) ω + (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n f := by
  obtain ⟨y, hyT, hDy, hyL⟩ := stair_up F n hTop hV hE P hP y0 hy0 hD n le_rfl

  obtain ⟨w, hwT, -, hwL, hwL'⟩ := kill F (n : ℤ) (2 * n) y hyT hyL (n + 1)
    (fun p q _ => by rw [hDy]; exact sgl_mem F hP p q) (fun p q hp hq => hE n p q (by omega))
  have hy1T : y - K.D w ∈ K.T (2 * n + 1) := sub_mem hyT (K.D_mem _ w hwT)
  have hDy1 : K.D (y - K.D w) = K.sgl (n + 1) (n + 1) P := by rw [map_sub, K.DD, sub_zero, hDy]
  generalize y - K.D w = y1 at hy1T hDy1 hwL hwL'

  have htT : y1 - K.sgl (n + 1) n (y1 (n + 1) n) ∈ K.T (2 * n + 1) :=
    sub_mem hy1T fun a b hab => K.sgl_ne _ (by omega)
  have hDt : K.D (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) =
      K.sgl (n + 1) (n + 1) (P - (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n (y1 (n + 1) n)) := by
    have := hV (n + 2) n (by omega)
    rw [map_sub, K.D_sgl, hDy1, Subsingleton.elim (K.dh (n + 1) n (y1 (n + 1) n)) 0, map_zero, zero_add, map_sub, map_zsmul]
  have htL : ∀ p q, (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) p q ∈ F.L ((n : ℤ) + 1) p q := by
    intro p q
    rw [Pi.sub_apply, Pi.sub_apply]
    by_cases hp : p < n + 1
    · rw [K.sgl_ne _ (Or.inl (by omega)), sub_zero]
      exact hwL' p q hp
    · by_cases hp' : p = n + 1
      · subst hp'
        by_cases hq : q = n
        · subst hq
          rw [K.sgl_self, sub_self]
          exact zero_mem _
        · rw [K.sgl_ne _ (Or.inr hq), hy1T _ _ (by omega), sub_zero]
          exact zero_mem _
      · have := hV p q (by omega)
        rw [Subsingleton.elim (y1 p q - K.sgl (n + 1) n (y1 (n + 1) n) p q) 0]
        exact zero_mem _
  have ecast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; rfl
  obtain ⟨w2, hw2T, hw20, hw2L, hw2L'⟩ := kill F ((n : ℤ) + 1) (2 * n) _ htT htL n
    (fun p q hp => by
      rw [hDt, K.sgl_ne _ (Or.inl (by omega))]
      exact zero_mem _)
    (fun p q hp hq => by
      have := hE (n + 1) p q (by omega)
      rwa [ecast] at this)
  have hDt' : K.D ((y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2) =
      K.sgl (n + 1) (n + 1) (P - (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n (y1 (n + 1) n)) := by
    rw [map_sub, K.DD, sub_zero, hDt]
  have ht0 : ((y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2) (n + 1) n = 0 := by
    have h1 : K.D w2 (n + 1) n = 0 := by
      rw [K.D_apply]
      have h2 : K.Dv w2 (n + 1) n = 0 := by
        cases n with
        | zero => rfl
        | succ n =>
          show K.dv (n + 1 + 1) n (w2 (n + 1 + 1) n) = 0
          rw [hw20 _ _ (by omega), map_zero]
      have h3 : K.Dh w2 (n + 1) n = 0 := by
        show K.dh n n (w2 n n) = 0
        rw [hw20 _ _ le_rfl, map_zero]
      rw [h2, h3]; simp
    show (y1 (n + 1) n - K.sgl (n + 1) n (y1 (n + 1) n) (n + 1) n) - K.D w2 (n + 1) n = 0
    rw [h1, K.sgl_self]
    simp
  generalize (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2 = t at hDt' ht0 hw2L hw2L'
  refine ⟨t n (n + 1), y1 (n + 1) n, hw2L _ _, ?_, hwL _ _, ?_⟩
  · refine dv_mem_of F t ?_ (fun e' h => hw2L' e' _ (by omega))
    rw [hDt', K.sgl_ne _ (Or.inl (by omega))]
    exact zero_mem _
  · have h := congrFun (congrFun hDt' (n + 1)) (n + 1)
    rw [K.sgl_self, K.D_apply] at h
    have h2 : K.Dv t (n + 1) (n + 1) = 0 := by
      show K.dv (n + 1) n (t (n + 1) n) = 0
      rw [ht0, map_zero]
    rw [h2, smul_zero, add_zero] at h
    have h3 : K.Dh t (n + 1) (n + 1) = K.dh n (n + 1) (t n (n + 1)) := rfl
    rw [← h3, h]
    abel

end GlobalTheory.CompanionTheory.ConeCech
