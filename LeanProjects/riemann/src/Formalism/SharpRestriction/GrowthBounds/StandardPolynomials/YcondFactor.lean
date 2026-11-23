import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCoreDef
import Formalism.SharpRestriction.GrowthBounds.PolBridge

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def mdHom (X : Loc) (l : X.TT × Bool) : MonH X →+ ℕ where
  toFun := fun m => multideg m l
  map_zero' := by simp [multideg]
  map_add' := fun a b => multideg_add a b l

def ndHom (X : Loc) : MonH X →+ ℕ where
  toFun := ndM X
  map_zero' := Formalism.MainNotions.LemmaBAlt.degUS_zero _ _
  map_add' := ndM_add X

section Hom

variable {X : Loc} {O : Type} [CommRing O] [IsDomain O]

def HomW (φ : MonH X →+ ℕ) (d : ℕ) (P : RHH O X) : Prop := ∀ m ∈ P.support, φ m = d

theorem HomW.mul {φ : MonH X →+ ℕ} {d d' : ℕ} {P Q : RHH O X} (hP : HomW φ d P) (hQ : HomW φ d' Q) :
    HomW φ (d + d') (P * Q) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul P Q hm)
  rw [map_add, hP a ha, hQ b hb]

theorem HomW.one (φ : MonH X →+ ℕ) : HomW φ 0 (1 : RHH O X) := by
  classical
  intro m hm
  rw [mem_support_iff, coeff_one] at hm
  by_cases h : 0 = m
  · rw [← h, map_zero]
  · rw [if_neg h] at hm; exact absurd rfl hm

theorem HomW.pow {φ : MonH X →+ ℕ} {d : ℕ} {P : RHH O X} (hP : HomW φ d P) (u : ℕ) : HomW φ (u * d) (P ^ u) := by
  induction u with
  | zero => simpa using HomW.one (O := O) φ
  | succ u ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hP

theorem HomW.prod {φ : MonH X →+ ℕ} {κ : Type} (s : Finset κ) (d : κ → ℕ) (P : κ → RHH O X)
    (h : ∀ a ∈ s, HomW φ (d a) (P a)) : HomW φ (∑ a ∈ s, d a) (∏ a ∈ s, P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HomW.one (O := O) φ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem HomW.monomial (φ : MonH X →+ ℕ) (M : MonH X) (c : KK O) : HomW φ (φ M) (monomial M c : RHH O X) := by
  classical
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]

theorem mem_Pol_iffW {d : X.TT × Bool → ℕ} {P : RHH O X} :
    P ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) d ↔ ∀ l, HomW (mdHom X l) (d l) P := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  constructor
  · intro h l m hm
    exact h (Finset.mem_coe.2 hm) l
  · intro h m hm l
    exact h l m (Finset.mem_coe.1 hm)

theorem mono_sum {ι : Type} (s : Finset ι) (n : ι → ℕ) (a : ι → MonH X) :
    (monomial (∑ i ∈ s, n i • a i) (1 : KK O) : RHH O X) = ∏ i ∈ s, (monomial (a i) (1 : KK O) : RHH O X) ^ n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, ← ih, monomial_pow, one_pow, monomial_mul, one_mul]

theorem hom_total (φ : MonH X →+ ℕ) {κ : Type} [Fintype κ] (sg : κ → RHH O X) (d : κ → ℕ) (h : ∀ a, HomW φ (d a) (sg a))
    {sgR : RHH O X} {dR : ℕ} (hR : HomW φ dR sgR) (mult u : κ → ℕ) (M : MonH X) :
    HomW φ (dR + ∑ a, (mult a - u a) * d a + φ M) (sgR * (∏ a, sg a ^ (mult a - u a)) * monomial M 1) :=
  (hR.mul (HomW.prod _ _ _ fun a _ => (h a).pow _)).mul (HomW.monomial φ M 1)

end Hom

open Formalism.MainNotions.G.PolBridge Formalism.MainNotions.G.GLWeightTheory in

theorem ycond_factor (D : Formalism.BasicNotions.D7) {K : Type} [Field K] [CharZero K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) (jj : ℕ)
    (M : WithTop ℤ) (Gu Gr : MvPolynomial (Fin N × Fin r) K) (dr : Fin N → ℕ) (hr : Gr ∈ Pol K r dr) (hne : Gr ≠ 0)
    (h : Gu * Gr ∈ YCond K (r := r) LL jj M) (cov : ℕ) (hcov : ∑ i, (if LL.vec i then 0 else dr i) ≤ cov) :
    Gu ∈ YCond K (r := r) LL jj (M + ((cov : ℤ) : WithTop ℤ)) := by
  classical
  cases M with
  | top => rw [WithTop.top_add, ycond_top]; exact Submodule.mem_top
  | coe Mz =>
    rw [← WithTop.coe_add, mem_ycond_iff D]
    rw [mem_ycond_iff D, (valuationsAdditive_D7 D K (Fin N) (⟨LL.vec⟩ : Letters (Fin N)) r {i : Fin N | (i : ℕ) < jj}).2.2.1] at h
    have hlow : ¬ lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < jj} Gr ≤ ((-(cov : ℤ) - 1 : ℤ) : WithBot ℤ) := by
      intro hle
      have h1 := ycond_le (K := K) (r := r) LL jj ((-(cov : ℤ) - 1 : ℤ) : WithTop ℤ) ((mem_ycond_iff D LL jj _ Gr).2 hle)
      rw [MvPolynomial.mem_restrictSupport_iff] at h1
      obtain ⟨m, hm⟩ : Gr.support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro h0; exact hne (MvPolynomial.support_eq_empty.1 h0)
      have h2 : ((chWt LL jj 0 m : ℤ) : WithTop ℤ) ≤ ((-(cov : ℤ) - 1 : ℤ) : WithTop ℤ) := h1 (Finset.mem_coe.2 hm)
      have h3 : chWt LL jj 0 m ≤ -(cov : ℤ) - 1 := by exact_mod_cast h2
      have hdeg : ∀ i, multideg m i = dr i := by
        unfold Pol at hr
        rw [MvPolynomial.mem_restrictSupport_iff] at hr
        exact hr (Finset.mem_coe.2 hm)
      have h4 : -((∑ i, (if LL.vec i then 0 else dr i) : ℕ) : ℤ) ≤ chWt LL jj 0 m := by
        unfold chWt
        rw [Nat.cast_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        have hm0 : m (i, 0) ≤ dr i := by
          rw [← hdeg i]
          exact Finset.single_le_sum (f := fun c => m (i, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
        have hm0' : (m (i, 0) : ℤ) ≤ (dr i : ℤ) := by exact_mod_cast hm0
        by_cases hv : LL.vec i = true
        · simp only [hv, if_true]
          split_ifs <;> simp
        · simp only [hv]
          split_ifs <;> simp <;> omega
      have h5 : ((∑ i, (if LL.vec i then 0 else dr i) : ℕ) : ℤ) ≤ (cov : ℤ) := by exact_mod_cast hcov
      omega
    induction hGr : lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < jj} Gr using WithBot.recBotCoe with
    | bot => rw [hGr] at hlow; exact absurd bot_le hlow
    | coe v =>
      rw [hGr] at hlow h
      have hv : -(cov : ℤ) - 1 < v := by
        by_contra hc
        exact hlow (by exact_mod_cast (not_lt.1 hc))
      induction hGu : lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < jj} Gu using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe a =>
        rw [hGu] at h
        have h6 : a + v ≤ Mz := by exact_mod_cast h
        have : a ≤ Mz + (cov : ℤ) := by omega
        exact_mod_cast this

end Formalism.MainNotions.ColumnSystems.Pf
