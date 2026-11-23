import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

namespace GlobalTheory.Div.TwistConst

theorem step3 {P : Type*} [AddCommGroup P] {ψ : P → ℤ} (h : DiffVanish (2 + 1) ψ) (c y : P) :
    (ψ (y + c + c + c) : ℚ) - 3 * ψ (y + c + c) + 3 * ψ (y + c) - ψ y = 0 := by
  have e := congrFun (h.multiDiff_eq_zero (g := fun _ : Fin 3 => c) (by simp)) (y + c + c + c)
  rw [multiDiff_const] at e
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, bwdDiff_apply,
    Pi.zero_apply, add_sub_cancel_right] at e
  have e' : ((ψ (y + c + c + c) - ψ (y + c + c) - (ψ (y + c + c) - ψ (y + c)) -
      (ψ (y + c + c) - ψ (y + c) - (ψ (y + c) - ψ y)) : ℤ) : ℚ) = 0 := by exact_mod_cast e
  push_cast at e'
  linarith

theorem const_of_step3 {a : ℕ → ℚ} (h : ∀ n, a (n + 3) - 3 * a (n + 2) + 3 * a (n + 1) - a n = 0)
    {c : ℚ} (hc : ∀ᶠ n in atTop, a n = c) : a 0 = c := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc
  have key : ∀ j n, N ≤ n + j → a n = c ∧ a (n + 1) = c ∧ a (n + 2) = c := by
    intro j
    induction j with
    | zero => intro n hn; exact ⟨hN n (by omega), hN _ (by omega), hN _ (by omega)⟩
    | succ j ih =>
      intro n hn
      obtain ⟨h1, h2, h3⟩ := ih (n + 1) (by omega)
      have := h n
      refine ⟨?_, h1, h2⟩
      rw [show n + 1 + 1 = n + 2 by omega, show n + 1 + 2 = n + 3 by omega] at *
      linarith
  exact (key N 0 (by omega)).1

end GlobalTheory.Div.TwistConst

open GlobalTheory.Div.TwistConst in

theorem GlobalTheory.Div.degCh2_eq_of_eventually_twist :
    ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T →
      ∀ (G D : T.Modules) (r : ℕ), IsVB G r → Nonempty (D ≅ dual G) → ∀ (L : LB T), L.IsLB →
        ∀ c : ℚ, (∀ᶠ n in atTop, ((chi k (twist G (lbPow L n)) : ℚ) +
          (chi k (twist D (lbPow L n)) : ℚ)) / 2 - (r : ℚ) *
            (chi k (twist (structureModule T) (lbPow L n)) : ℚ) = c) → degCh2 k G = c := by
  intro k _ T _ _ hT G D r hG ⟨e⟩ L hL c hc
  have := hG.isFiniteQC
  have := hG.dual.isFiniteQC
  have := (isVB_structureModule T).isFiniteQC
  have hd : ∀ F : T.Modules, QCoh.suppDim F ≤ ((2 : ℕ) : WithBot ℕ∞) := fun F =>
    (QCoh.suppDim_le F).trans (by rw [hT.dim_eq]; rfl)
  have vG : DiffVanish (2 + 1) (chiPic k G) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k T) G hT.isProjOver (hd G)
  have vD : DiffVanish (2 + 1) (chiPic k D) := by
    rw [chiPic_congr k e]
    exact diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k T) _ hT.isProjOver (hd _)
  have vO : DiffVanish (2 + 1) (chiPic k (structureModule T)) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k T) _ hT.isProjOver (hd _)
  set c₀ := CechPic.cls L hL
  have ev : ∀ (F : T.Modules) (n : ℕ), chi k (twist F (lbPow L n)) = chiPic k F (n • c₀) := by
    intro F n
    have h := Twist.isLB_lbZPow hL (n : ℤ)
    have e₁ : chi k (twist F (lbPow L n)) = chiPic k F (CechPic.cls (lbZPow L (n : ℤ)) h) :=
      (chiPic_cls k F h).symm
    rw [e₁, cls_lbZPow hL (n : ℤ) h, natCast_zsmul]
  let a : ℕ → ℚ := fun n => ((chiPic k G (n • c₀) : ℚ) + (chiPic k D (n • c₀) : ℚ)) / 2 -
    (r : ℚ) * (chiPic k (structureModule T) (n • c₀) : ℚ)
  have ha : ∀ n, a (n + 3) - 3 * a (n + 2) + 3 * a (n + 1) - a n = 0 := by
    intro n
    have s : ∀ j, (n + j) • c₀ = n • c₀ + j • c₀ := fun j => add_nsmul _ _ _
    have s3 : (n + 3) • c₀ = n • c₀ + c₀ + c₀ + c₀ := by rw [s]; simp only [succ_nsmul, zero_nsmul, zero_add, add_assoc]
    have s2 : (n + 2) • c₀ = n • c₀ + c₀ + c₀ := by rw [s]; simp only [succ_nsmul, zero_nsmul, zero_add, add_assoc]
    have s1 : (n + 1) • c₀ = n • c₀ + c₀ := succ_nsmul _ _
    have hG' := step3 vG c₀ (n • c₀)
    have hD' := step3 vD c₀ (n • c₀)
    have hO' := step3 vO c₀ (n • c₀)
    simp only [a, s1, s2, s3]
    linear_combination (1 / 2 : ℚ) * hG' + (1 / 2 : ℚ) * hD' - (r : ℚ) * hO'
  have hc' : ∀ᶠ n in atTop, a n = c := hc.mono fun n hn => by
    simp only [a, ← ev]; exact hn
  have h0 := const_of_step3 ha hc'
  simp only [a, zero_nsmul, chiPic_zero] at h0
  rw [degCh2_eq hG, ← chi_congr k e]
  exact h0
