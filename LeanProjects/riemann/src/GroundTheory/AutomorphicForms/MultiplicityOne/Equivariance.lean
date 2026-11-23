import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.NormOne

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open AutomorphicForm FourierWhittaker

section Columns

variable {n : ℕ} {R : Type*} [CommRing R]

def colShift {k j : ℕ} (hkj : k < j) (x : Fin k → R) (y : Fin j → R) : Fin j → R :=
  fun i => if h : i.val < k then y ⟨k, hkj⟩ * x ⟨i.val, h⟩ else 0

theorem uN_colX_mul_uN_colX_of_lt {k j : ℕ} (hkj : k < j) (x : Fin k → R) (y : Fin j → R) :
    uN (colX (n := n) k x) * uN (colX j y) = uN (colX j (colShift hkj x y)) := by
  ext a b
  rw [Matrix.mul_apply]
  by_cases hb : b.val = j
  · by_cases ha : a.val < k
    · have hk : k < n := by have := b.2; omega
      rw [Finset.sum_eq_single ⟨k, hk⟩]
      · have hab : a < b := by rw [Fin.lt_def]; omega
        have hak : a < (⟨k, hk⟩ : Fin n) := by rw [Fin.lt_def]; exact ha
        have hkb : (⟨k, hk⟩ : Fin n) < b := by rw [Fin.lt_def]; simp only; omega
        rw [uN_apply, uN_apply, uN_apply, dif_pos hak, dif_pos hkb, dif_pos hab, colX_apply,
          colX_apply, colX_apply, dif_pos rfl, dif_pos hb, dif_pos hb]
        simp only [colShift, dif_pos ha]
        ring
      · intro c _ hc
        rw [uN_apply, uN_apply]
        by_cases hac : a < c
        · rw [dif_pos hac, colX_apply, dif_neg (fun h => hc (Fin.ext h)), zero_mul]
        · rw [dif_neg hac, zero_mul]
      · simp
    · rw [uN_apply]
      have h0 : ∀ c : Fin n, uN (colX (n := n) k x) a c * uN (colX j y) c b = 0 := by
        intro c
        rw [uN_apply]
        by_cases hac : a < c
        · rw [dif_pos hac, colX_apply]
          by_cases hck : c.val = k
          · rw [Fin.lt_def] at hac; omega
          · rw [dif_neg hck, zero_mul]
        · rw [dif_neg hac, zero_mul]
      rw [Finset.sum_eq_zero fun c _ => h0 c]
      split_ifs with hab
      · rw [colX_apply, dif_pos hb]
        simp only [colShift]
        rw [dif_neg (by simpa using ha)]
      · rfl
  · have h0 : ∀ c : Fin n, uN (colX (n := n) k x) a c * uN (colX j y) c b = 0 := by
      intro c
      rw [uN_apply (colX j y)]
      by_cases hcb : c < b
      · rw [dif_pos hcb, colX_apply, dif_neg hb, mul_zero]
      · rw [dif_neg hcb, mul_zero]
    rw [Finset.sum_eq_zero fun c _ => h0 c, uN_apply]
    split_ifs with hab
    · rw [colX_apply, dif_neg hb]
    · rfl

theorem colGL_mul_colGL_of_lt {k j : ℕ} (hkj : k < j) (x : Fin k → R) (y : Fin j → R) :
    (colGL k x : GL (Fin n) R) * colGL j y = colGL j (y + colShift hkj x y) * colGL k x := by
  refine Units.ext ?_
  have hz : ∀ w : Fin j → R, uN (colX (n := n) j w) * uN (colX k x) = 0 := by
    intro w
    refine uN_mul_uN_colX (fun p hp => colX_le j w p (Or.inl (by omega))) x
  simp only [colGL, Units.val_mul, coe_uGL, uMat, colX_add, uN_add, mul_add, add_mul, one_mul,
    mul_one, hz, uN_colX_mul_uN_colX_of_lt hkj, add_zero]
  abel

theorem pair_lastVec_colShift {K : Type*} [Field K] [NumberField K] {k j : ℕ} (hkj : k < j)
    (x : Fin k → 𝔸[K]) (y : Fin j → 𝔸[K]) :
    pair (lastVec (K := K) j) (colShift hkj x y) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val + 1 = j
  · rw [colShift, dif_neg (by omega), mul_zero]
  · rw [lastVec, if_neg hi, map_zero, zero_mul]

end Columns

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem partialCoeff_colGL_mul {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hl : IsLeftInvariant ϕ) :
    ∀ (m k : ℕ), n - k = m → ∀ j, k ≤ j → j < n → ∀ (y : Fin j → 𝔸[K]) (g : AdelicGLn.AdelicGL K n),
      partialCoeff ϕ k (colGL j y * g) =
        (GroundTheory.Global.adelicChar K (pair (lastVec j) y) : ℂ) * partialCoeff ϕ k g := by
  intro m
  induction m with
  | zero => intro k hk j hkj hj; omega
  | succ m ih =>
    intro k hkm j hkj hj y g
    have hk : k < n := by omega
    rw [partialCoeff_of_lt ϕ hk, stepCoeff, stepCoeff]
    have hper : ∀ g', ∀ ξ ∈ vecLattice K (Fin k), ∀ x,
        partialCoeff ϕ (k + 1) (colGL k (ξ + x) * g') = partialCoeff ϕ (k + 1) (colGL k x * g') := by
      intro g' ξ hξ x
      obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
      rw [colGL_add, mul_assoc, ← diagonal_colGL, partialCoeff_succ_diagonal_colGL hl hk]
    rcases eq_or_lt_of_le hkj with rfl | hlt
    · have e : (fun x : Fin k → 𝔸[K] => partialCoeff ϕ (k + 1) (colGL k x * (colGL k y * g))) =
          fun x => partialCoeff ϕ (k + 1) (colGL k (x + y) * g) := by
        funext x
        rw [colGL_add, mul_assoc]
      rw [e]
      exact vecCoeff_translate (f := fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) (hper g) y
        (lastVec k)
    · have e : (fun x : Fin k → 𝔸[K] => partialCoeff ϕ (k + 1) (colGL k x * (colGL j y * g))) =
          fun x => (GroundTheory.Global.adelicChar K (pair (lastVec j) y) : ℂ) *
            partialCoeff ϕ (k + 1) (colGL k x * g) := by
        funext x
        rw [← mul_assoc, colGL_mul_colGL_of_lt hlt, mul_assoc,
          ih (k + 1) (by omega) j hlt hj, FourierWhittaker.pair_add, pair_lastVec_colShift, add_zero]
      rw [e]
      unfold vecCoeff
      simp_rw [mul_assoc]
      rw [integral_const_mul]

theorem whittaker_colGL_mul {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hc : Continuous ϕ)
    (hl : IsLeftInvariant ϕ) {j : ℕ} (hj : j < n) (y : Fin j → 𝔸[K]) (g : AdelicGLn.AdelicGL K n) :
    whittaker ϕ (colGL j y * g) =
      (GroundTheory.Global.adelicChar K (pair (lastVec j) y) : ℂ) * whittaker ϕ g := by
  rw [whittaker_eq_partialCoeff_zero hc, whittaker_eq_partialCoeff_zero hc]
  exact partialCoeff_colGL_mul hl _ 0 rfl j (Nat.zero_le j) hj y g

theorem supSum_zero_eq_of_vanish {m : ℕ} {X : Pos n → 𝔸[K]}
    (hX : ∀ p : Pos n, p.1.2.val < m → X p = 0) : supSum 0 X = supSum m X := by
  classical
  unfold supSum
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun p : Pos n => p.1.2.val = p.1.1.val + 1 ∧ 0 ≤ p.1.2.val))
    (fun p : Pos n => m ≤ p.1.2.val)]
  rw [Finset.sum_eq_zero (s := Finset.filter (fun p : Pos n => ¬ m ≤ p.1.2.val) _)
    fun p hp => hX p (by simp only [Finset.mem_filter] at hp; omega), add_zero]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem whittaker_uGL_mul {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hc : Continuous ϕ)
    (hl : IsLeftInvariant ϕ) (X : Pos n → 𝔸[K]) (g : AdelicGLn.AdelicGL K n) :
    whittaker ϕ (uGL X * g) = (GroundTheory.Global.adelicChar K (supSum 0 X) : ℂ) * whittaker ϕ g := by
  classical
  suffices H : ∀ (d m : ℕ), n - m = d → ∀ X : Pos n → 𝔸[K], (∀ p : Pos n, p.1.2.val < m → X p = 0) →
      ∀ g, whittaker ϕ (uGL X * g) = (GroundTheory.Global.adelicChar K (supSum 0 X) : ℂ) * whittaker ϕ g from
    H n 0 (Nat.sub_zero n) X (fun p hp => absurd hp (Nat.not_lt_zero _)) g
  intro d
  induction d with
  | zero =>
    intro m hm X hX g
    have hX0 : X = 0 := funext fun p => hX p (by have := p.1.2.2; omega)
    rw [hX0, uGL_zero, one_mul, supSum_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
  | succ d ih =>
    intro m hm X hX g
    have hmn : m < n := by omega
    set c : Fin m → 𝔸[K] := fun i => X ⟨(⟨i.val, by omega⟩, ⟨m, hmn⟩), by
      rw [Fin.lt_def]; exact i.2⟩
    set X' : Pos n → 𝔸[K] := fun p => if p.1.2.val = m then 0 else X p
    have hcol : colX m c = fun p : Pos n => if p.1.2.val = m then X p else 0 := by
      funext p
      rw [colX_apply]
      by_cases h : p.1.2.val = m
      · rw [dif_pos h, if_pos h]
        show X _ = X p
        congr 1
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> simp [h]
      · rw [dif_neg h, if_neg h]
    have hsplit : X = X' + colX m c := by
      funext p
      rw [hcol, Pi.add_apply]
      by_cases h : p.1.2.val = m
      · simp [X', h]
      · simp [X', h]
    have hX' : ∀ p : Pos n, p.1.2.val < m + 1 → X' p = 0 := by
      intro p hp
      by_cases h : p.1.2.val = m
      · simp [X', h]
      · simp only [X', if_neg h]; exact hX p (by omega)
    have hu : uGL X = uGL X' * colGL m c := by
      refine Units.ext ?_
      rw [Units.val_mul, colGL, coe_uGL, coe_uGL, coe_uGL,
        uMat_mul_uMat_colX (fun p hp => hX' p (by omega)) c, ← hsplit]
    have hs : supSum 0 X = supSum 0 X' + pair (lastVec m) c := by
      rw [hsplit, supSum_add, ← supSum_colX m hmn c,
        ← supSum_zero_eq_of_vanish (m := m) (X := colX m c) fun p hp => colX_le m c p (Or.inl (by omega))]
    rw [hu, mul_assoc, ih (m + 1) (by omega) X' hX', whittaker_colGL_mul hc hl hmn, hs,
      AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]

end MultiplicityOne

end

end GroundTheory.Automorphic
