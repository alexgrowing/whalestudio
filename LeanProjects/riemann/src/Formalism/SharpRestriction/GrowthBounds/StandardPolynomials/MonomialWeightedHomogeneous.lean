import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.NdHomSingle
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.PreDef

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Small

variable {X : Loc} {O : Type} [CommRing O] [IsDomain O]

theorem top_letter_power_ne_zero (x : X.TT) (P : ℕ) (hP : P ≠ 0) : EhatT O X x P ≠ 0 := by
  intro h
  have key := congrArg (MvPolynomial.eval (fun v : (X.TT × Bool) × Fin (X.m + 1) => if v.2 = 0 then (1 : KK O) else 0)) h
  simp [EhatT, hP, Fin.succ_ne_zero] at key

theorem top_letter_ne_zero (x : X.TT) : hTop O X x ≠ 0 := by
  intro h
  have key := congrArg (MvPolynomial.eval (fun v : (X.TT × Bool) × Fin (X.m + 1) => if v.2 = 0 then (1 : KK O) else 0)) h
  simp [hTop, hKey, Fin.sum_univ_succ, Fin.succ_ne_zero] at key

theorem monomial_in_algebra (M : MonH X) : InA (monomial M (1 : KK O) : RHH O X) := by
  classical
  intro m
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem algebra_mul_mem {P Q : RHH O X} (hP : InA P) (hQ : InA Q) : InA (P * Q) := by
  rw [Formalism.MainNotions.G.WittFrameLocaliserOrders.inA_iff_inWj0 (w := (1 : O))] at hP hQ ⊢
  exact Formalism.MainNotions.G.WittFrameLocaliserOrders.inWPow_zero_mul hP hQ

theorem algebra_prod_pow_mem {κ : Type} (s : Finset κ) (P : κ → RHH O X) (n : κ → ℕ) (h : ∀ a ∈ s, InA (P a)) :
    InA (∏ a ∈ s, P a ^ n a) := by
  rw [Formalism.MainNotions.G.WittFrameLocaliserOrders.inA_iff_inWj0 (w := (1 : O))]
  refine Formalism.MainNotions.G.WittFrameLocaliserOrders.inWj_prod0 s _ (fun a ha => Formalism.MainNotions.G.WittFrameLocaliserOrders.inWPow_zero_pow ?_ _)
  exact (Formalism.MainNotions.G.WittFrameLocaliserOrders.inA_iff_inWj0 _).1 (h a ha)

theorem chain_embedding_injective (N r t : ℕ) : Function.Injective (chainEmb N r t) := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

end Small

section Ord

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O] {w : O}
  {g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')}
  {J : Type} [Fintype J] {A : J → Type} [∀ j, Fintype (A j)] {B : J → Type} [∀ j, Fintype (B j)] {M : Type} [Fintype M]

theorem order_total_bound {sR : RHH O X} {dR : ℕ} (hR : InWjRg X.p X.n' O w 1 (hhLetters X.TT) g sR dR)
    {sC : ∀ j, A j → RHH O X} {dC : ∀ j, A j → ℕ} (hC : ∀ j a, InWjRg X.p X.n' O w 1 (hhLetters X.TT) g (sC j a) (dC j a))
    {sH : ∀ j, B j → RHH O X} {dH : ∀ j, B j → ℕ} (hH : ∀ j i, InWjRg X.p X.n' O w 1 (hhLetters X.TT) g (sH j i) (dH j i))
    {sM : M → RHH O X} {dM : M → ℕ} (hM : ∀ a, InWjRg X.p X.n' O w 1 (hhLetters X.TT) g (sM a) (dM a))
    (lv : ∀ j, B j → ℕ) (mult : M → ℕ) :
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g
      (sR * ((∏ j, ∏ a, sC j a) * ((∏ j, ∏ i, sH j i ^ lv j i) * ∏ a, sM a ^ mult a)))
      (dR + ((∑ j, ∑ a, dC j a) + ((∑ j, ∑ i, lv j i * dH j i) + ∑ a, mult a * dM a))) := by
  refine inWjRg_mul hR (inWjRg_mul ?_ (inWjRg_mul ?_ ?_))
  · exact inWjRg_prod Finset.univ (fun j => ∏ a, sC j a) (fun j => ∑ a, dC j a)
      (fun j _ => inWjRg_prod Finset.univ (sC j) (dC j) (fun a _ => hC j a))
  · exact inWjRg_prod Finset.univ (fun j => ∏ i, sH j i ^ lv j i) (fun j => ∑ i, lv j i * dH j i)
      (fun j _ => inWjRg_prod Finset.univ (fun i => sH j i ^ lv j i) (fun i => lv j i * dH j i)
        (fun i _ => inWjRg_pow (hH j i) (lv j i)))
  · exact inWjRg_prod Finset.univ (fun a => sM a ^ mult a) (fun a => mult a * dM a)
      (fun a _ => inWjRg_pow (hM a) (mult a))

end Ord

def multMk0 (X : Loc) (β : GlobalTheory X) : IM X → ℕ
  | Sum.inr (Sum.inr (Sum.inr _)) => 0
  | a => multMk X β a

theorem product_split_constant {O : Type} [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) :
    ∏ a, fMk O C0 CE1 CE2 X a ^ multMk X β a =
      (∏ a, fMk O C0 CE1 CE2 X a ^ multMk0 X β a) * ∏ c : Fin X.m, locC O X c.succ ^ X.c := by
  simp only [Fintype.prod_sum_type, multMk0, multMk, fMk, pow_zero, Finset.prod_const_one, mul_one]
  simp only [mul_assoc]

theorem sum_split_constant (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) :
    ∑ a, multMk0 X β a * oMk C0 CE1 CE2 X a = ∑ a, multMk X β a * oMk C0 CE1 CE2 X a := by
  simp [Fintype.sum_sum_type, multMk0, multMk, oMk]

end Formalism.MainNotions.ColumnSystems.Pf
