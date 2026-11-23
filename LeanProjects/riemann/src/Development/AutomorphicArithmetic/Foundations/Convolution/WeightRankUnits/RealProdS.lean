import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.RealProd

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def emptyW : DomWeight 0 := ⟨fun i => i.elim0, fun i => i.elim0⟩

private theorem chAt_rank_zero (l : DomWeight 0) : chAt l (1 : ℂ[X]) = 1 := by
  have h := GlobalTheory.LaplaceChar.chAt_prod_eq_gtChar l (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  have hw : l.w = (0 : Fin 0 → ℤ) := Subsingleton.elim _ _
  rw [hw, ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar_zero] at h
  simpa using h

private theorem chW_rank_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    (l : InfinitePlace E → DomWeight 0) : chW l (1 : E[X]) = 1 := by
  unfold chW
  simp [chAt_rank_zero]

private theorem infOfWeight_rank_zero (l : DomWeight 0) : infOfWeight l = 0 := by
  simp [infOfWeight]

private theorem eq_one_of_ell_zero {E : Type} [Field E] {P : E[X]} (h : P ∈ Ell E 0) : P = 1 :=
  (Polynomial.Monic.natDegree_eq_zero (show P.Monic from h.1)).mp h.2.1

private theorem phase_one {E : Type} [Field E] [NumberField E] [IsCMField E] (e : InfinitePlace E → ℤ) (v : InfinitePlace E) :
    UpperTheory.ConvolutionTheory.G2.phase e (1 : E) v = 1 := by
  simp [UpperTheory.ConvolutionTheory.G2.phase]

theorem UpperTheory.ConvolutionTheory.G2.realProdS :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ), a + b = n → ∀ e : InfinitePlace E → ℤ, (∀ v, Odd (e v)) →
    ∀ lam : InfinitePlace E → DomWeight n, ∃ (ι : Type) (_ : Fintype ι) (l₁ : ι → InfinitePlace E → DomWeight a)
      (l₂ : ι → InfinitePlace E → DomWeight b) (sg : ι → ℤˣ), ((a = 0 ∨ b = 0) → (∃ i₀ : ι, ∀ i, i = i₀) ∧ ∀ i, sg i = 1) ∧
      (∀ i v, (infOfWeight (l₁ i v)).map (· + (b : ℂ) * (e v : ℂ) / 2) + (infOfWeight (l₂ i v)).map (· + (a : ℂ) * (e v : ℂ) / 2) =
        infOfWeight (lam v)) ∧
      ∀ P₁ P₂ : E[X], P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCoprime P₁ P₂ →
        (∏ v, UpperTheory.ConvolutionTheory.G2.phase e (resultant P₁ P₂) v) * chW lam (P₁ * P₂) = ∑ i, ((sg i : ℤ) : ℂ) * chW (l₁ i) P₁ * chW (l₂ i) P₂ := by
  intro E _ _ _ n a b hab e he lam
  by_cases hz : a = 0 ∨ b = 0
  · rcases hz with rfl | rfl
    · obtain rfl : b = n := by omega
      refine ⟨Unit, inferInstance, fun _ _ => emptyW, fun _ => lam, fun _ => 1,
        fun _ => ⟨⟨(), fun _ => rfl⟩, fun _ => rfl⟩, ?_, ?_⟩
      · intro _ v
        simp [infOfWeight_rank_zero]
      · intro P₁ P₂ h₁ _ _
        obtain rfl := eq_one_of_ell_zero h₁
        simp [phase_one, chW_rank_zero]
    · obtain rfl : a = n := by omega
      refine ⟨Unit, inferInstance, fun _ => lam, fun _ _ => emptyW, fun _ => 1,
        fun _ => ⟨⟨(), fun _ => rfl⟩, fun _ => rfl⟩, ?_, ?_⟩
      · intro _ v
        simp [infOfWeight_rank_zero]
      · intro P₁ P₂ _ h₂ _
        obtain rfl := eq_one_of_ell_zero h₂
        simp [phase_one, chW_rank_zero]
  · obtain ⟨ι, hι, l₁, l₂, sg, hinf, hid⟩ := UpperTheory.ConvolutionTheory.G2.realProd E n a b hab e he lam
    exact ⟨ι, hι, l₁, l₂, sg, fun h => absurd h hz, hinf, hid⟩
