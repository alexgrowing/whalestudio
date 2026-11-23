import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishTransferOfVanishOverAlgebraicClosureStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem exists_elim_form_of_field : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F)) (g : MvPolynomial (Fin N) F), 1 ≤ D → I.IsPrime → (∀ a ∈ I, ∀ n : ℕ, homogeneousComponent n a ∈ I) → ringKrullDim (MvPolynomial (Fin N) F ⧸ I) = (D + 1 : ℕ) → g.IsHomogeneous d → g ∉ I → ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ ∀ (K : Type) [Field K] [Algebra F K] (s : Fin D → Fin N → K) (y : Fin N → K), y ≠ 0 → (∀ a ∈ I, aeval y a = 0) → aeval y g = 0 → (∀ i, ∑ j, s i j * y j = 0) → aeval (fun p : Fin D × Fin N => s p.1 p.2) Q = 0 := by
  intro F _ _ D N d I g hD hI hhom hdim hg hgI
  obtain ⟨Q, hQ0, -, hQ⟩ := GlobalTheory.HSElim.exists_elim_form F D N d I g hD hI hhom hdim hg hgI
  refine ⟨Q, hQ0, ?_⟩
  intro K _ _ s y hy hyI hyg hlin
  classical
  let ey : Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun j => Sum.inr (Sum.inl j)
  let ez : Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun j => Sum.inr (Sum.inr j)
  let gens : Set (MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F) :=
    ((rename ey) '' (I : Set _) ∪ {rename ey g}) ∪
    (Set.range (fun i : Fin D => ∑ j, X (Sum.inl (i, j)) * X (ey j)) ∪ {∑ j, X (ez j) * X (ey j) - 1})
  let f := rename (Sum.inl : Fin D × Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) Q
  have hclos : ∀ x : (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) → AlgebraicClosure F,
      (∀ p ∈ Ideal.span gens, aeval x p = 0) → aeval x f = 0 := by
    intro x hx
    have h' : ∀ p ∈ gens, aeval x p = 0 := fun p hp => hx p (Ideal.subset_span hp)
    have hz : ∑ j, x (ez j) * x (ey j) = 1 := by
      have := h' _ (Or.inr (Or.inr rfl))
      simpa [sub_eq_zero] using this
    have hy0 : (fun j => x (ey j)) ≠ 0 := by
      intro h0
      have : ∑ j, x (ez j) * x (ey j) = 0 := by
        simp [show ∀ j, x (ey j) = 0 from fun j => congrFun h0 j]
      rw [hz] at this
      exact one_ne_zero this
    simp only [f, aeval_rename]
    exact hQ (AlgebraicClosure F) (fun i j => x (Sum.inl (i, j))) (fun j => x (ey j)) hy0
      (fun a ha => by
        have := h' _ (Or.inl (Or.inl ⟨a, ha, rfl⟩))
        simpa [aeval_rename, Function.comp_def] using this)
      (by
        have := h' _ (Or.inl (Or.inr rfl))
        simpa [aeval_rename, Function.comp_def] using this)
      (fun i => by
        have := h' _ (Or.inr (Or.inl ⟨i, rfl⟩))
        simpa using this)
  obtain ⟨j0, hj0⟩ : ∃ j0, y j0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hy (funext hcon)
  let z : Fin N → K := fun j => if j = j0 then (y j0)⁻¹ else 0
  let x0 : (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) → K := Sum.elim (fun p => s p.1 p.2) (Sum.elim y z)
  have hx0 : ∀ p ∈ Ideal.span gens, aeval x0 p = 0 := by
    intro p hp
    have hle : Ideal.span gens ≤ RingHom.ker (aeval x0 : MvPolynomial _ F →ₐ[F] K) := by
      rw [Ideal.span_le]
      rintro q ((⟨a, ha, rfl⟩ | rfl) | (⟨i, rfl⟩ | rfl))
      · simpa [aeval_rename, Function.comp_def, x0, ey] using hyI a ha
      · simpa [aeval_rename, Function.comp_def, x0, ey] using hyg
      · simpa [x0, ey] using hlin i
      · simp [x0, ey, ez, z, hj0]
    exact hle hp
  have := GlobalTheory.T.vanish_transfer_of_vanish_over_algebraicClosure F ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) (Ideal.span gens) f hclos K x0 hx0
  simpa [f, aeval_rename, Function.comp_def, x0] using this

end GlobalTheory.HSShort
