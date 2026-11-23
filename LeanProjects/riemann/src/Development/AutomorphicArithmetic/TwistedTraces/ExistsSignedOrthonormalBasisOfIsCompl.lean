import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_signed_orthonormal_basis_of_isCompl :
    ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) (k p : Submodule ℝ V), IsCompl k p → (∀ X Y, B X Y = B Y X) → (∀ X ∈ k, X ≠ 0 → B X X < 0) → (∀ X ∈ p, X ≠ 0 → 0 < B X X) → (∀ X ∈ k, ∀ Y ∈ p, B X Y = 0) → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ V) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∀ i j, B (b i) (b j) = if i = j then ε i else 0) ∧ ∀ i, ε i = -1 → b i ∈ k := by
  intro V _ _ _ B k p hc hsymm hneg hpos hzero
  classical
  obtain ⟨bk, hbk⟩ := exists_signed_basis (B.restrict k)
    (fun x y => hsymm (x : V) y) (s := -1)
    (by norm_num) (fun v hv => by
      have h0 : (v : V) ≠ 0 := fun e => hv (Subtype.ext e)
      have := hneg v v.2 h0
      change 0 < _ * B (v : V) v
      linarith)
  obtain ⟨bp, hbp⟩ := exists_signed_basis (B.restrict p)
    (fun x y => hsymm (x : V) y) (s := 1)
    (by norm_num) (fun v hv => by
      have h0 : (v : V) ≠ 0 := fun e => hv (Subtype.ext e)
      have := hpos v v.2 h0
      change 0 < _ * B (v : V) v
      linarith)
  set e := Submodule.prodEquivOfIsCompl k p hc
  set b0 := (bk.prod bp).map e
  set f : Fin (Module.finrank ℝ k) ⊕ Fin (Module.finrank ℝ p) → V :=
    Sum.elim (fun i => (bk i : V)) (fun j => (bp j : V))
  have hb0 : ∀ x, b0 x = f x := by
    rintro (i | j)
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
  set ε0 : Fin (Module.finrank ℝ k) ⊕ Fin (Module.finrank ℝ p) → ℝ :=
    Sum.elim (fun _ => -1) (fun _ => 1)
  have horth : ∀ x y, B (b0 x) (b0 y) = if x = y then ε0 x else 0 := by
    intro x y
    rw [hb0, hb0]
    rcases x with i | i <;> rcases y with j | j
    · have := hbk i j
      change B _ _ = _ at this
      simp only [f, ε0, Sum.elim_inl, Sum.inl.injEq]
      exact this
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact hzero _ (bk i).2 _ (bp j).2
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      rw [hsymm]
      exact hzero _ (bk j).2 _ (bp i).2
    · have := hbp i j
      change B _ _ = _ at this
      simp only [f, ε0, Sum.elim_inr, Sum.inr.injEq]
      exact this
  set σ := finSumFinEquiv (m := Module.finrank ℝ k) (n := Module.finrank ℝ p)
  refine ⟨_, b0.reindex σ, ε0 ∘ σ.symm, fun i => ?_, fun i j => ?_, fun i hi => ?_⟩
  · rcases hx : σ.symm i with a | a <;> simp [ε0, hx]
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, horth]
    simp only [Function.comp_apply, σ.symm.injective.eq_iff]
  · rw [Module.Basis.reindex_apply, hb0]
    simp only [Function.comp_apply] at hi
    rcases hx : σ.symm i with a | a
    · simp only [f, Sum.elim_inl]
      exact (bk a).2
    · rw [hx] at hi
      simp [ε0] at hi
      norm_num at hi
