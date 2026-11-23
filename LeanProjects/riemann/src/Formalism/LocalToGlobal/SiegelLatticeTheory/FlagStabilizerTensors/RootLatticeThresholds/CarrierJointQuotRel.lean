import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

section Alg

variable {r : ℕ}

theorem relAlg (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (π : Fin (r + 1) → Fin (r + 1)) (hπ : ∀ a, π (π a) = a)
    (hP1 : ∀ c b, Z c b ≠ 0 ↔ c = π b)
    (hP2 : ∀ k : Fin r, ((π k.succ).val + 1 = (π k.castSucc).val ∧
        Z (π k.succ) k.succ = - Z (π k.castSucc) k.castSucc) ∨ (π k.castSucc).val < (π k.succ).val)
    (m U : Fin r → Fin (r + 1) → ℂ)
    (hA : ∀ a b, (∑ c : Fin r, if c.castSucc < a then conj (m c a) * Z c.castSucc b else 0) =
      ∑ c : Fin r, if c.castSucc < b then U c b * Z a c.castSucc else 0) :
    ∑ k : Fin r, (U k k.succ).re = - ∑ k : Fin r, (m k k.succ).re := by
  have hπinj : Function.Injective π := Function.Involutive.injective hπ
  have hZ0 : ∀ c b, c ≠ π b → Z c b = 0 := fun c b h => by
    by_contra h'
    exact h ((hP1 c b).1 h')
  have hzne : ∀ b, Z (π b) b ≠ 0 := fun b => (hP1 _ b).2 rfl
  have hcond : ∀ k : Fin r, (π k.succ).val + 1 = (π k.castSucc).val → (π k.succ).val < r :=
    fun k h => by have := (π k.castSucc).isLt; omega
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : Fin r → Fin r, ∀ k, ψ k =
      if h : (π k.succ).val + 1 = (π k.castSucc).val then ⟨(π k.succ).val, hcond k h⟩ else k :=
    ⟨_, fun k => rfl⟩

  have hR1 : ∀ k : Fin r, (∑ c : Fin r, if c.castSucc < π k.castSucc then
        conj (m c (π k.castSucc)) * Z c.castSucc k.succ else 0) =
      U k k.succ * Z (π k.castSucc) k.castSucc := by
    intro k
    rw [hA, Finset.sum_eq_single k]
    · rw [if_pos (Fin.castSucc_lt_succ : k.castSucc < k.succ)]
    · intro c _ hck
      split_ifs
      · rw [hZ0 _ _ (fun e => hck (Fin.castSucc_injective r (hπinj e).symm)), mul_zero]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ k) h

  have hR2 : ∀ j : Fin r, (∑ c : Fin r, if c.castSucc < π j.castSucc then
        U c (π j.castSucc) * Z j.succ c.castSucc else 0) =
      conj (m j j.succ) * Z j.castSucc (π j.castSucc) := by
    intro j
    rw [← hA, Finset.sum_eq_single j]
    · rw [if_pos (Fin.castSucc_lt_succ : j.castSucc < j.succ)]
    · intro c _ hcj
      split_ifs
      · rw [hZ0 _ _ (by rw [hπ]; exact fun e => hcj (Fin.castSucc_injective r e)), mul_zero]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hψ : Function.Involutive ψ := by
    intro k
    by_cases h : (π k.succ).val + 1 = (π k.castSucc).val
    · obtain ⟨j, hjv⟩ : ∃ j : Fin r, j.val = (π k.succ).val := ⟨⟨_, hcond k h⟩, rfl⟩
      have hψk : ψ k = j := by
        rw [hψdef, dif_pos h]
        exact Fin.ext hjv.symm
      have hjc : j.castSucc = π k.succ := Fin.ext (by rw [Fin.coe_castSucc, hjv])
      have hjs : j.succ = π k.castSucc := Fin.ext (by rw [Fin.val_succ, hjv]; exact h)
      have h' : (π j.succ).val + 1 = (π j.castSucc).val := by
        rw [hjs, hjc, hπ, hπ, Fin.coe_castSucc, Fin.val_succ]
      rw [hψk, hψdef, dif_pos h']
      apply Fin.ext
      show (π j.succ).val = k.val
      rw [hjs, hπ, Fin.coe_castSucc]
    · have hψk : ψ k = k := by rw [hψdef, dif_neg h]
      rw [hψk, hψk]
  have hterm : ∀ k : Fin r, (U k k.succ).re = -(m (ψ k) (ψ k).succ).re := by
    intro k
    by_cases h : (π k.succ).val + 1 = (π k.castSucc).val
    · obtain ⟨j, hjv⟩ : ∃ j : Fin r, j.val = (π k.succ).val := ⟨⟨_, hcond k h⟩, rfl⟩
      have hψk : ψ k = j := by
        rw [hψdef, dif_pos h]
        exact Fin.ext hjv.symm
      have hjc : j.castSucc = π k.succ := Fin.ext (by rw [Fin.coe_castSucc, hjv])
      have hjs : j.succ = π k.castSucc := Fin.ext (by rw [Fin.val_succ, hjv]; exact h)
      have hz : Z (π k.succ) k.succ = - Z (π k.castSucc) k.castSucc := by
        rcases hP2 k with ⟨_, hz⟩ | hlt
        · exact hz
        · omega
      have hlt1 : π k.succ < π k.castSucc := Fin.lt_iff_val_lt_val.2 (by omega)
      have eL : (∑ c : Fin r, if c.castSucc < π k.castSucc then
          conj (m c (π k.castSucc)) * Z c.castSucc k.succ else 0) =
          conj (m j j.succ) * Z (π k.succ) k.succ := by
        rw [Finset.sum_eq_single j]
        · rw [hjs, hjc, if_pos hlt1]
        · intro c _ hcj
          split_ifs
          · rw [hZ0 _ _ (fun e => hcj (Fin.castSucc_injective r (e.trans hjc.symm))), mul_zero]
          · rfl
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      have key := eL.symm.trans (hR1 k)
      rw [hz] at key
      have hU : U k k.succ = -conj (m j j.succ) := by
        apply mul_right_cancel₀ (hzne k.castSucc)
        rw [← key]
        ring
      rw [hψk, hU, Complex.neg_re, Complex.conj_re]
    · have hlt : (π k.castSucc).val < (π k.succ).val := by
        rcases hP2 k with ⟨h', _⟩ | hlt
        · exact absurd h' h
        · exact hlt
      have hψk : ψ k = k := by rw [hψdef, dif_neg h]
      have eL : (∑ c : Fin r, if c.castSucc < π k.castSucc then
          conj (m c (π k.castSucc)) * Z c.castSucc k.succ else 0) = 0 :=
        Finset.sum_eq_zero fun c _ => by
          split_ifs with hc
          · rw [hZ0 _ _ (fun e => by rw [e, Fin.lt_iff_val_lt_val] at hc; omega), mul_zero]
          · rfl
      have hU : U k k.succ = 0 := by
        have key := eL.symm.trans (hR1 k)
        exact (mul_eq_zero.1 key.symm).resolve_right (hzne _)
      have eR2 : (∑ c : Fin r, if c.castSucc < π k.castSucc then
          U c (π k.castSucc) * Z k.succ c.castSucc else 0) = 0 :=
        Finset.sum_eq_zero fun c _ => by
          split_ifs with hc
          · rw [hZ0 _ _ (fun e => by
                have e2 := congrArg π e
                rw [hπ] at e2
                rw [← e2, Fin.lt_iff_val_lt_val] at hc
                omega), mul_zero]
          · rfl
      have hm : conj (m k k.succ) = 0 := by
        have key := eR2.symm.trans (hR2 k)
        exact (mul_eq_zero.1 key.symm).resolve_right ((hP1 _ _).2 (hπ _).symm)
      have hre : (m k k.succ).re = 0 := by rw [← Complex.conj_re, hm, Complex.zero_re]
      rw [hψk, hU, Complex.zero_re, hre, neg_zero]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_neg_distrib]
  congr 1
  exact Equiv.sum_comp (Function.Involutive.toPerm ψ hψ) (fun j => (m j j.succ).re)

end Alg

section Pt

variable {K : Type*} [Zero K]

def ptPar : List (K × ℕ) → ℕ → ℕ
  | [], a => a
  | (_, s) :: bs, a => if a < s then s - 1 - a else s + ptPar bs (a - s)

def ptSc : List (K × ℕ) → ℕ → K
  | [], _ => 0
  | (t, s) :: bs, a => if a < s then t else ptSc bs (a - s)

theorem ptPar_cons (t : K) (s : ℕ) (bs : List (K × ℕ)) (a : ℕ) :
    ptPar ((t, s) :: bs) a = if a < s then s - 1 - a else s + ptPar bs (a - s) := rfl

theorem ptSc_cons (t : K) (s : ℕ) (bs : List (K × ℕ)) (a : ℕ) :
    ptSc ((t, s) :: bs) a = if a < s then t else ptSc bs (a - s) := rfl

theorem ptEntry_cons (t : K) (s : ℕ) (bs : List (K × ℕ)) (i j : ℕ) :
    ptEntry ((t, s) :: bs) i j = if i < s ∧ j < s then (if i + j + 1 = s then t else 0)
      else if s ≤ i ∧ s ≤ j then ptEntry bs (i - s) (j - s) else 0 := rfl

theorem ptEntry_eq : ∀ (bs : List (K × ℕ)) (c b : ℕ), b < (bs.map Prod.snd).sum →
    ptEntry bs c b = if c = ptPar bs b then ptSc bs b else 0
  | [], _, b, hb => by simp at hb
  | (t, s) :: bs, c, b, hb => by
    simp only [List.map_cons, List.sum_cons] at hb
    rw [ptEntry_cons]
    by_cases hbs : b < s
    · have hp : ptPar ((t, s) :: bs) b = s - 1 - b := by rw [ptPar_cons, if_pos hbs]
      have hq : ptSc ((t, s) :: bs) b = t := by rw [ptSc_cons, if_pos hbs]
      rw [hp, hq]
      by_cases hcs : c < s
      · rw [if_pos ⟨hcs, hbs⟩]
        by_cases h : c + b + 1 = s
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      · rw [if_neg (fun h => hcs h.1), if_neg (fun h => by omega), if_neg (by omega)]
    · have hp : ptPar ((t, s) :: bs) b = s + ptPar bs (b - s) := by rw [ptPar_cons, if_neg hbs]
      have hq : ptSc ((t, s) :: bs) b = ptSc bs (b - s) := by rw [ptSc_cons, if_neg hbs]
      rw [hp, hq, if_neg (fun h => hbs h.2)]
      by_cases hcs : s ≤ c
      · rw [if_pos ⟨hcs, by omega⟩, ptEntry_eq bs (c - s) (b - s) (by omega)]
        by_cases h : c - s = ptPar bs (b - s)
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      · rw [if_neg (fun h => hcs h.1), if_neg (by omega)]

theorem ptPar_lt : ∀ (bs : List (K × ℕ)) (b : ℕ), b < (bs.map Prod.snd).sum →
    ptPar bs b < (bs.map Prod.snd).sum
  | [], b, hb => by simp at hb
  | (t, s) :: bs, b, hb => by
    simp only [List.map_cons, List.sum_cons] at hb ⊢
    rw [ptPar_cons]
    by_cases hbs : b < s
    · rw [if_pos hbs]; omega
    · rw [if_neg hbs]; have := ptPar_lt bs (b - s) (by omega); omega

theorem ptPar_invol : ∀ (bs : List (K × ℕ)) (b : ℕ), b < (bs.map Prod.snd).sum →
    ptPar bs (ptPar bs b) = b
  | [], b, hb => by simp at hb
  | (t, s) :: bs, b, hb => by
    simp only [List.map_cons, List.sum_cons] at hb
    by_cases hbs : b < s
    · have hp : ptPar ((t, s) :: bs) b = s - 1 - b := by rw [ptPar_cons, if_pos hbs]
      rw [hp, ptPar_cons, if_pos (by omega)]; omega
    · have hp : ptPar ((t, s) :: bs) b = s + ptPar bs (b - s) := by rw [ptPar_cons, if_neg hbs]
      rw [hp, ptPar_cons, if_neg (by omega)]
      have : s + ptPar bs (b - s) - s = ptPar bs (b - s) := by omega
      rw [this, ptPar_invol bs (b - s) (by omega)]; omega

theorem ptSc_ne : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ b : ℕ,
    b < (bs.map Prod.snd).sum → ptSc bs b ≠ 0
  | [], _, b, hb => by simp at hb
  | (t, s) :: bs, h, b, hb => by
    simp only [List.map_cons, List.sum_cons] at hb
    rw [ptSc_cons]
    by_cases hbs : b < s
    · rw [if_pos hbs]; exact (h (t, s) (by simp)).1
    · rw [if_neg hbs]; exact ptSc_ne bs (fun b hb => h b (by simp [hb])) (b - s) (by omega)

theorem ptPar_consec : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, 1 ≤ b.2) → ∀ k : ℕ,
    k + 1 < (bs.map Prod.snd).sum →
    (ptPar bs (k + 1) + 1 = ptPar bs k ∧ ptSc bs (k + 1) = ptSc bs k) ∨ ptPar bs k < ptPar bs (k + 1)
  | [], _, k, hk => by simp at hk
  | (t, s) :: bs, h, k, hk => by
    simp only [List.map_cons, List.sum_cons] at hk
    have hs1 : 1 ≤ s := h (t, s) (by simp)
    rw [ptPar_cons, ptPar_cons, ptSc_cons, ptSc_cons]
    by_cases h1 : k + 1 < s
    · left
      rw [if_pos h1, if_pos (by omega), if_pos h1, if_pos (by omega)]
      exact ⟨by omega, rfl⟩
    · by_cases h2 : k < s
      · right
        rw [if_neg h1, if_pos h2]; omega
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        have e : k + 1 - s = k - s + 1 := by omega
        rw [e]
        rcases ptPar_consec bs (fun b hb => h b (by simp [hb])) (k - s) (by omega) with h3 | h3
        · left; exact ⟨by omega, h3.2⟩
        · right; omega

end Pt

section Frame

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_add_r' (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp only [hJ, Matrix.mulVec_add, dotProduct_add]

theorem hJ_sum_r' {ι : Type*} [Fintype ι] (x : Fin n → ℂ) (a : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ c, a c • y c) = ∑ c, a c * hJ ε x (y c) := by
  simp only [hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem hJ_cj' (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) := by
  simp only [hJ, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, RCLike.star_def, map_sum,
    map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp <;> ring

theorem hJ_sum_l' {ι : Type*} [Fintype ι] (x : Fin n → ℂ) (a : ι → ℂ) (y : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    hJ ε (x + ∑ c, a c • y c) w = hJ ε x w + ∑ c, conj (a c) * hJ ε (y c) w := by
  rw [hJ_cj' ε (x + ∑ c, a c • y c) w, hJ_add_r', hJ_sum_r', map_add, map_sum, ← hJ_cj' ε x w]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, ← hJ_cj' ε (y c) w]

theorem span_expand (e f : Fin r → Fin n → ℂ) (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0)
    (k : ℕ) (y : Fin n → ℂ) (hy : y ∈ spanLt e k) :
    y = ∑ c : Fin r, (if c.val < k then hJ ε (f c) y else 0) • e c := by
  have hsm : ∀ (x : Fin n → ℂ) (t : ℂ) (v : Fin n → ℂ), hJ ε x (t • v) = t * hJ ε x v := by
    intro x t v
    simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  unfold spanLt at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : b.val < k := hb
    simp only [hfe]
    rw [Finset.sum_eq_single b]
    · simp [hb']
    · intro c _ hcb
      simp [Ne.symm hcb]
    · intro h
      exact absurd (Finset.mem_univ b) h
  | zero => simp [hJ]
  | add x y' _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hJ_add_r']
    split_ifs <;> simp [add_smul]
  | smul t x _ hx =>
    conv_lhs => rw [hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hsm]
    split_ifs <;> simp [mul_smul]

theorem fam_castSucc (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (c : Fin r) : fam e z c.castSucc = e c := by
  simp [fam]

theorem fam_last (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : fam e z (Fin.last r) = z := by
  simp [fam]

theorem nxt_eq_fam (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (k : Fin r) : nxt e z k = fam e z k.succ := by
  unfold nxt
  have hk := k.isLt
  split_ifs with h
  · have e1 : k.succ = (⟨k.val + 1, h⟩ : Fin r).castSucc := Fin.ext (by simp)
    rw [e1, fam_castSucc]
  · have e1 : k.succ = Fin.last r := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
    rw [e1, fam_last]

theorem flag_expand (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : InS e z g) (a : Fin (r + 1)) :
    g *ᵥ fam e z a = fam e z a +
      ∑ c : Fin r, (if c.castSucc < a then hJ ε (f c) (g *ᵥ fam e z a) else 0) • e c := by
  have hmem : (g - 1) *ᵥ fam e z a ∈ spanLt e a.val := by
    induction a using Fin.lastCases with
    | last =>
      rw [fam_last]
      simpa using hg.2
    | cast b =>
      rw [fam_castSucc]
      simpa using hg.1 b
  have hzero : ∀ c : Fin r, c.castSucc < a → hJ ε (f c) (fam e z a) = 0 := by
    intro c hc
    induction a using Fin.lastCases with
    | last =>
      rw [fam_last]
      exact hfz c
    | cast b =>
      rw [fam_castSucc, hfe, if_neg]
      intro hbc
      subst hbc
      exact lt_irrefl _ hc
  have hsubJ : ∀ x y y' : Fin n → ℂ, hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
    intro x y y'
    simp only [hJ, Matrix.mulVec_sub, dotProduct_sub]
  have hexp := span_expand ε e f hfe a.val _ hmem
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hexp
  have hS : (∑ c : Fin r, (if c.val < a.val then hJ ε (f c) (g *ᵥ fam e z a - fam e z a) else 0) • e c) =
      ∑ c : Fin r, (if c.castSucc < a then hJ ε (f c) (g *ᵥ fam e z a) else 0) • e c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : c.castSucc < a
    · have hc' : c.val < a.val := by
        rw [Fin.lt_iff_val_lt_val, Fin.coe_castSucc] at hc
        exact hc
      rw [if_pos hc', if_pos hc, hsubJ, hzero c hc, sub_zero]
    · have hc' : ¬ c.val < a.val := by
        rw [Fin.lt_iff_val_lt_val, Fin.coe_castSucc] at hc
        exact hc
      rw [if_neg hc', if_neg hc]
  rw [← hS, ← hexp]
  abel

end Frame

end Formalism.L2.SG.Pf.Carrier.JointQuot
