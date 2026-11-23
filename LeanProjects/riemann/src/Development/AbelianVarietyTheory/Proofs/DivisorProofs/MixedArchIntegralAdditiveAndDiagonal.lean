import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalArchIntegralChernPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableOfProjArithAmbientStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixAdd

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem archInt_congr {A B : HermLB q} (h : A.Isometric B) (M : HermLB q) (e : ℕ) {r : M.B.ι → Y.functionFieldˣ}
    (hr : IsRatSec M.B r) : A.archInt M e hr = B.archInt M e hr := by
  simp only [HermLB.archInt, h.chernInt_eq]

theorem lin_comb {ι κ : Type} [Fintype ι] [Fintype κ] (m : κ → ι → ℤ) (n : κ → ℤ) :
    (lin fun i => ((∑ j, n j * m j i : ℤ) : ℝ)) = ∑ j, (n j : ℝ) • lin fun i => (m j i : ℝ) := by
  simp only [lin, Int.cast_sum, Int.cast_mul, map_sum, map_mul, Finset.sum_mul, smul_eq_C_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem lin_add {ι : Type} [Fintype ι] (m n : ι → ℤ) :
    (lin fun i => (((m + n) i : ℤ) : ℝ)) = (lin fun i => (m i : ℝ)) + lin fun i => (n i : ℝ) := by
  simp only [lin, Pi.add_apply, Int.cast_add, map_add, add_mul, Finset.sum_add_distrib]

theorem mixArch_eq {ι : Type} [Fintype ι] {e : ℕ} (F : ι → HermLB q) (M : HermLB q) {r : M.B.ι → Y.functionFieldˣ}
    (hr : IsRatSec M.B r) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hΨ : ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ e) = (comb F n).archInt M e hr)
    (L : Fin e → HermLB q) (m : Fin e → ι → ℤ) (h : ∀ a, (comb F (m a)).Isometric (L a)) :
    mixArch L M hr = Ψ (∏ a, lin fun i => (m a i : ℝ)) := by
  have h₁ : (fun n => (comb L n).archInt M e hr) =
      fun n : Fin e → ℤ => Ψ ((∑ a, (n a : ℝ) • lin fun i => (m a i : ℝ)) ^ e) := by
    funext n
    rw [← lin_comb, hΨ]
    exact (archInt_congr ((isometric_comb_comb F m n).trans (isometric_comb_congr h n)) M e hr).symm
  rw [mixArch, h₁, FibreProj.pol_pow _ Ψ (Fintype.card_fin e), mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.2 e.factorial_ne_zero

theorem mixArch_add_diag : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k),
    IsAmb q → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r),
    (∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ (A B : HermLB q) (L : Fin e → HermLB q),
      mixArch (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr =
        mixArch (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + mixArch (Fin.cons B L : Fin (e + 1) → HermLB q) M hr) ∧
    ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ N : HermLB q,
      mixArch (fun _ : Fin e => N) M hr = N.archInt M e hr := by
  intro hI k _ Y _ q hq M r hr
  classical
  refine ⟨fun e he A B L => ?_, fun e he N => ?_⟩
  · let F : Bool ⊕ Fin e → HermLB q := Sum.elim (fun b => cond b A B) L
    obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_linear_functional_arch_integral_chern_power k Y q hq (e + 1) _ F M r hr
      fun n => GlobalTheory.T.archIntegrable_of_projArithAmbient hI k Y q hq (e + 1) he M _ r hr
    let u : Bool ⊕ Fin e → Bool ⊕ Fin e → ℤ := fun j => Pi.single j 1
    have key (C : HermLB q) (c : Bool ⊕ Fin e → ℤ) (hc : (comb F c).Isometric C) :
        mixArch (Fin.cons C L : Fin (e + 1) → HermLB q) M hr =
          Ψ ((lin fun i => (c i : ℝ)) * ∏ a : Fin e, lin fun i => (u (Sum.inr a) i : ℝ)) := by
      rw [mixArch_eq F M hr Ψ hΨ (Fin.cons C L) (Fin.cons c fun a => u (Sum.inr a)) (fun a => by
        cases a using Fin.cases with
        | zero => exact hc
        | succ a => exact isometric_comb_single F (Sum.inr a)), Fin.prod_univ_succ]
      rfl
    have hA : (comb F (u (Sum.inl true))).Isometric A := isometric_comb_single F (Sum.inl true)
    have hB : (comb F (u (Sum.inl false))).Isometric B := isometric_comb_single F (Sum.inl false)
    rw [key A _ hA, key B _ hB, key _ _ ((isometric_comb_add F _ _).trans (hA.tens hB)), lin_add, add_mul, map_add]
  · let F : Unit → HermLB q := fun _ => N
    obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_linear_functional_arch_integral_chern_power k Y q hq e _ F M r hr fun n => GlobalTheory.T.archIntegrable_of_projArithAmbient hI k Y q hq e he M _ r hr
    have hN : (comb F (Pi.single () 1)).Isometric N := isometric_comb_single F ()
    rw [mixArch_eq F M hr Ψ hΨ _ (fun _ => Pi.single () 1) fun _ => hN, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hΨ]
    exact archInt_congr hN M e hr

end GlobalTheory.MixAdd
