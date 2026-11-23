import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

private theorem B_update_mul_eq_mul {X : ℕ → Type} (B : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ)) (j : ℕ)
    (a : (∀ i, X i) → X j → ℂ) (R : (∀ i, X i) → ℂ)
    (ha : ∀ u x, a (Function.update u j x) = a u) (hR : ∀ u x, R (Function.update u j x) = R u)
    (u : ∀ i, X i) :
    B j (fun x => a (Function.update u j x) (Function.update u j x j) * R (Function.update u j x)) (u j) =
      B j (a u) (u j) * R u := by
  have hfun : (fun x => a (Function.update u j x) (Function.update u j x j) * R (Function.update u j x)) =
      R u • a u := by
    funext x
    rw [ha, hR, Function.update_self, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hfun, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem exists_prod_op {X : ℕ → Type} (A : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ)) (n : ℕ) :
    ∃ Tc : ((∀ j, X j) → ℂ) →ₗ[ℂ] ((∀ j, X j) → ℂ), ∀ (C : ∀ j, X j → X (j + 1) → ℂ) (g : (∀ j, X j) → ℂ),
      (∀ u u' : ∀ j, X j, (∀ j, 2 * n ≤ j → u j = u' j) → g u = g u') →
      (fun u : ∀ j, X j => (∏ k ∈ Finset.range n,
          A (2 * k) (fun x => A (2 * k + 1) (C (2 * k) x) (u (2 * k + 1))) (u (2 * k))) * g u) =
        Tc (fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) := by
  classical

  let op : ∀ j, ((∀ i, X i) → ℂ) →ₗ[ℂ] ((∀ i, X i) → ℂ) := fun j =>
    { toFun := fun F u => A j (fun x => F (Function.update u j x)) (u j)
      map_add' := fun F G => by
        funext u
        have e : (fun x => (F + G) (Function.update u j x)) =
            (fun x => F (Function.update u j x)) + (fun x => G (Function.update u j x)) := rfl
        rw [e, map_add]
        rfl
      map_smul' := fun c F => by
        funext u
        have e : (fun x => (c • F) (Function.update u j x)) = c • (fun x => F (Function.update u j x)) := rfl
        rw [e, map_smul]
        rfl }
  induction n with
  | zero => exact ⟨LinearMap.id, fun C g _ => by simp⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨T ∘ₗ op (2 * n) ∘ₗ op (2 * n + 1), fun C g hg => ?_⟩

    obtain ⟨R, hRR⟩ : ∃ R : (∀ j, X j) → ℂ,
        R = fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u := ⟨_, rfl⟩
    have hR : ∀ j, 2 * n ≤ j → j < 2 * n + 2 → ∀ (u : ∀ i, X i) x, R (Function.update u j x) = R u := by
      intro j hj1 hj2 u x
      subst hRR
      dsimp only
      congr 1
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.mp hk
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · exact hg _ _ fun i hi => Function.update_of_ne (by omega) _ _

    obtain ⟨g', hgG⟩ : ∃ g' : (∀ j, X j) → ℂ,
        g' = fun u => A (2 * n) (fun x => A (2 * n + 1) (C (2 * n) x) (u (2 * n + 1))) (u (2 * n)) * g u :=
      ⟨_, rfl⟩
    have hg' : ∀ u u' : ∀ j, X j, (∀ j, 2 * n ≤ j → u j = u' j) → g' u = g' u' := by
      intro u u' h
      subst hgG
      dsimp only
      rw [h (2 * n) le_rfl, h (2 * n + 1) (by omega), hg u u' fun j hj => h j (by omega)]

    have h1 : op (2 * n + 1) (fun u => (∏ k ∈ Finset.range (n + 1), C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) =
        fun u => A (2 * n + 1) (C (2 * n) (u (2 * n))) (u (2 * n + 1)) * R u := by
      have hF : (fun u => (∏ k ∈ Finset.range (n + 1), C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) =
          fun u => (fun w : ∀ j, X j => C (2 * n) (w (2 * n))) u (u (2 * n + 1)) * R u := by
        funext u
        subst hRR
        simp only [Finset.prod_range_succ]
        ring
      rw [hF]
      funext v
      refine B_update_mul_eq_mul A (2 * n + 1) (fun w => C (2 * n) (w (2 * n))) R ?_ (hR _ (by omega) (by omega)) v
      intro w x
      show C (2 * n) (Function.update w (2 * n + 1) x (2 * n)) = C (2 * n) (w (2 * n))
      rw [Function.update_of_ne (by omega)]

    have h2 : op (2 * n) (fun u => A (2 * n + 1) (C (2 * n) (u (2 * n))) (u (2 * n + 1)) * R u) =
        fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g' u := by
      funext v
      have e := B_update_mul_eq_mul A (2 * n) (fun w x => A (2 * n + 1) (C (2 * n) x) (w (2 * n + 1))) R
        (fun w y => by
          funext x
          show A (2 * n + 1) (C (2 * n) x) (Function.update w (2 * n) y (2 * n + 1)) = A (2 * n + 1) (C (2 * n) x) (w (2 * n + 1))
          rw [Function.update_of_ne (by omega)])
        (hR _ le_rfl (by omega)) v
      refine e.trans ?_
      subst hRR hgG
      dsimp only
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, h2, ← hT C g' hg']
    funext u
    subst hgG
    simp only [Finset.prod_range_succ]
    ring

noncomputable def combLin {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  map_smul' a f := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem exists_comb_op : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ c : Combs ch.G, ∃ Tc : (ColPt ch.G → ℂ) →ₗ[ℂ] (ColPt ch.G → ℂ), ∀ C : BiFam ch.G, (fun u => evT (combC ch.W c C) 1 u 0) = Tc (fun u => evT C 1 u 0) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ => ?_⟩⟩
  intro c
  obtain ⟨Tc, hTc⟩ := exists_prod_op (X := fun j => WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))))
    (fun j => combLin ch.W.ψ _ _ (c.1 j)) (D.R.m / 2)
  refine ⟨Tc, fun C => ?_⟩
  exact hTc C (fun _ => ∏ i, (1 : SchRow ch.G) i ((0 : RowPt ch.G) i)) fun _ _ _ => rfl

end GlobalTheory.LocAsm
