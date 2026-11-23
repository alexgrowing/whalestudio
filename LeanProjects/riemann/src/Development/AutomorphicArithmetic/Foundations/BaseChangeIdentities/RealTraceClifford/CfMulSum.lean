import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnAdj
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TraceRestrictSupDisjoint
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private def tenPiS {J V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : J → Submodule ℂ V) : Submodule ℂ (Ten J V) where
  carrier := {x | ∀ j, x j ∈ T j}
  add_mem' {x y} hx hy j := by simpa using (T j).add_mem (hx j) (hy j)
  zero_mem' j := by simp
  smul_mem' c x hx j := by simpa using (T j).smul_mem c (hx j)

private def tenPiE {J V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : J → Submodule ℂ V) : tenPiS T ≃ₗ[ℂ] Π j, T j where
  toFun x j := ⟨x.1 j, x.2 j⟩
  invFun y := ⟨WithLp.toLp 2 fun j => (y j).1, fun j => (y j).2⟩
  map_add' x y := by ext j; simp
  map_smul' c x := by ext j; simp
  left_inv x := by ext j; simp
  right_inv y := by ext j; simp

private theorem cf_mul_sum {n : ℕ} {J : Type} (c₀ : FR n) (η : J → Wt n) (s : Finset J) (μ : Wt n) :
    cf (c₀ * ∑ j ∈ s, ex (η j)) μ = ∑ j ∈ s, cf c₀ (μ - η j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cf]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, mul_add, ((cfBasic n).2.2.2.1 _ _ 1 μ).1, ih,
      mul_comm c₀ (ex (η j)), (cfBasic n).2.2.2.2.1]

theorem UpperTheory.RealTr.tenCh :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ (J : Type) [Fintype J] [DecidableEq J] (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), ClifMod c η → ∀ c₀, IsCh F S 1 c₀ → ∃ S' : Submodule ℂ (Ten J V), FiniteDimensional ℂ S' ∧ Stb (dg F c) S' ∧ IsCh (dg F c) S' 1 (c₀ * ∑ j, ex (η j)) := by
  intro n V _ _ F hF S hS hSt J _ _ c η hc c₀ hch
  refine ⟨tenPiS (fun _ => S), ?_, ?_, ?_⟩
  · exact Module.Finite.equiv (tenPiE (fun _ : J => S)).symm
  · intro a b x hx j
    have h : (dg F c a b x) j = F a b (x j) + ∑ k, spn c a b j k • x k := rfl
    rw [h]
    exact S.add_mem (hSt a b _ (hx j)) (S.sum_mem fun k _ => S.smul_mem _ (hx k))
  · intro μ
    have hdiag : ∀ (x : Ten J V) a j, (dg F c a a x) j = F a a (x j) + (η j a : ℂ) • x j := by
      intro x a j
      have h : (dg F c a a x) j = F a a (x j) + ∑ k, spn c a a j k • x k := rfl
      rw [h, hc.diag a]
      simp [Matrix.diagonal_apply]
    have hset : wsp (dg F c) μ ⊓ tenPiS (fun _ => S) = tenPiS (fun j => wsp F (μ - η j) ⊓ S) := by
      ext x
      constructor
      · rintro ⟨hw, hx⟩ j
        refine ⟨fun a => ?_, hx j⟩
        have h1 : (dg F c a a x) j = (μ a : ℂ) • x j := by
          have := congrArg (fun y : Ten J V => y j) (hw a)
          simpa using this
        rw [hdiag] at h1
        have h2 : F a a (x j) = (μ a : ℂ) • x j - (η j a : ℂ) • x j := eq_sub_of_add_eq h1
        rw [h2, ← sub_smul]
        simp
      · intro hx
        refine ⟨fun a => ?_, fun j => (hx j).2⟩
        ext j
        have h1 : F a a (x j) = (((μ - η j) a : ℝ) : ℂ) • x j := (hx j).1 a
        rw [hdiag, h1, ← add_smul]
        simp
    have hfin : ∀ j, FiniteDimensional ℂ ↥(wsp F (μ - η j) ⊓ S) :=
      fun j => Submodule.finiteDimensional_inf_right _ _
    have hfin' : FiniteDimensional ℂ ↥(tenPiS fun j => wsp F (μ - η j) ⊓ S) :=
      Module.Finite.equiv (tenPiE _).symm
    rw [hset, (trAdd (Ten J V) 1).2.2.2 _ hfin', LinearEquiv.finrank_eq (tenPiE _),
      Module.finrank_pi_fintype, cf_mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hch, (trAdd V 1).2.2.2 _ (hfin j)]
