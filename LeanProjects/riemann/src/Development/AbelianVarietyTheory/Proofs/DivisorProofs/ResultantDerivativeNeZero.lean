import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PencilLinePolynomialNatDegreeLeAndCoeffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreePencilLineDiscriminantLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSquareLinearFactorOfPencilLineDiscriminantNeZStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreduciblePencilLinePolynomialGenericLineStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.PencilDisc

theorem resultant_derivative_ne_zero : ∀ (σ F : Type) [Fintype σ] [Field F] [CharZero F] (p : Polynomial (MvPolynomial σ F)) (δ : ℕ), 1 ≤ δ → p.natDegree = δ → Irreducible p → Polynomial.resultant p (Polynomial.derivative p) δ (δ - 1) ≠ 0 := by
  intro σ F _ _ _ p δ hδ hp hirr
  let K := FractionRing (MvPolynomial σ F)
  have hinj : Function.Injective (algebraMap (MvPolynomial σ F) K) := IsFractionRing.injective _ _
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  have hprim : p.IsPrimitive := hirr.isPrimitive (by omega)
  have h1 : Irreducible (p.map (algebraMap _ K)) := hprim.irreducible_iff_irreducible_map_fraction_map.1 hirr
  have h2 := Polynomial.resultant_ne_zero _ _ h1.separable
  rw [Polynomial.natDegree_derivative, Polynomial.natDegree_map_eq_of_injective hinj, hp, Polynomial.derivative_map,
    Polynomial.resultant_map_map] at h2
  intro h
  exact h2 (by rw [h, map_zero])

theorem exists_specialise_ne_zero : ∀ (F S T : Type) [Field F] [Infinite F] (R : MvPolynomial (S ⊕ T) F), R ≠ 0 → ∃ v : T → F, MvPolynomial.aeval (Sum.elim (fun i => (MvPolynomial.X i : MvPolynomial S F)) fun k => MvPolynomial.C (v k)) R ≠ 0 := by
  intro F S T _ _ R hR
  have h1 : sumAlgEquiv F S T R ≠ 0 := (map_ne_zero_iff _ (sumAlgEquiv F S T).injective).2 hR
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 h1
  obtain ⟨v, hv⟩ : ∃ v : T → F, eval v (coeff m (sumAlgEquiv F S T R)) ≠ 0 := by
    by_contra! H
    exact hm (MvPolynomial.funext fun x => by simpa using H x)
  refine ⟨v, fun h => hv ?_⟩
  have key : ∀ P : MvPolynomial (S ⊕ T) F,
      aeval (Sum.elim (fun i => (X i : MvPolynomial S F)) fun k => C (v k)) P = MvPolynomial.map (eval v) (sumAlgEquiv F S T P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      cases i <;> simp
  rw [← coeff_map, ← key, h, coeff_zero]

theorem irreducible_of_map {F L : Type} [Field F] [Field L] [Algebra F L] {σ : Type} (f : MvPolynomial σ F)
    (h : Irreducible (MvPolynomial.map (algebraMap F L) f)) : Irreducible f := by
  have hinj := (algebraMap F L).injective
  haveI : IsLocalHom (MvPolynomial.map (σ := σ) (algebraMap F L)) := ⟨fun g hg => by
    obtain ⟨c, hc, e⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hg
    have hc0 : algebraMap F L (coeff 0 g) = c := by
      rw [← coeff_map, e, coeff_zero_C]
    refine MvPolynomial.isUnit_iff_eq_C_of_isReduced.2 ⟨coeff 0 g, ?_, ?_⟩
    · refine isUnit_iff_ne_zero.2 fun h0 => hc.ne_zero ?_
      rw [← hc0, h0, map_zero]
    · apply MvPolynomial.map_injective _ hinj
      rw [e, map_C, hc0]⟩
  exact Irreducible.of_map h

theorem exists_poly_noSquare : ∀ (F : Type) [Field F] [CharZero F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), 1 ≤ δ → IsMultiHomogeneous (fun _ => δ) f → Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f) → ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ Q.totalDegree ≤ 2 * D * δ ^ 2 ∧ ∀ (K : Type) [Field K] [Algebra F K] (s : Fin D → Fin N → K), aeval (fun p : Fin D × Fin N => s p.1 p.2) Q ≠ 0 → NoSquare (spec s f) := by
  intro F _ _ D N δ f hδ hf hirr
  have hF : Irreducible f := irreducible_of_map f hirr
  let u : Fin D → Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun i j => X (Sum.inl (i, j))
  let a : Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun j => X (Sum.inr (Sum.inl j))
  let b : Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun j => X (Sum.inr (Sum.inr j))
  have hc := GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff F _ D N δ f hf u a b
  let g : Fin (D + 1) × Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun p =>
    Fin.lastCases (motive := fun _ => (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) (Sum.inr (Sum.inr p.2)) (fun i => Sum.inl (i, p.2)) p.1
  have hg : Function.Injective g := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    induction i using Fin.lastCases <;> induction i' using Fin.lastCases <;> simp_all [g]
  have hjoin : join u b = fun p => X (g p) := by
    funext ⟨i, j⟩
    induction i using Fin.lastCases <;> simp [join, g, u, b]
  have hlead : (line u a b f).coeff δ ≠ 0 := by
    rw [hc.2, hjoin, show (aeval fun p => (X (g p) : MvPolynomial _ F)) f = rename g f from congrArg (fun φ : MvPolynomial _ F →ₐ[F] MvPolynomial _ F => φ f) (MvPolynomial.algHom_ext fun p => by simp)]
    exact (rename_injective g hg).ne_iff' (map_zero _) |>.mpr hF.ne_zero
  have hnat : (line u a b f).natDegree = δ := le_antisymm hc.1 (Polynomial.le_natDegree_of_ne_zero hlead)
  have hR : disc δ u a b f ≠ 0 := resultant_derivative_ne_zero _ F (line u a b f) δ hδ hnat (GlobalTheory.T.irreducible_pencilLinePolynomial_generic_line F D N f hF)
  obtain ⟨v, hv⟩ := exists_specialise_ne_zero F (Fin D × Fin N) (Fin N ⊕ Fin N) _ hR
  refine ⟨disc δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F)) (fun j => C (v (Sum.inl j))) (fun j => C (v (Sum.inr j))) f,
    ?_, GlobalTheory.T.totalDegree_pencilLineDiscriminant_le F D N δ f hf _ _, ?_⟩
  · have e := map_disc (aeval (Sum.elim (fun i => (X i : MvPolynomial (Fin D × Fin N) F)) fun k => C (v k))) δ u a b f
    rw [e] at hv
    simpa [u, a, b] using hv
  · intro K _ _ s hs
    have e := map_disc (aeval (fun p : Fin D × Fin N => s p.1 p.2)) δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (v (Sum.inl j))) (fun j => C (v (Sum.inr j))) f
    rw [e] at hs
    simp only [aeval_X, aeval_C] at hs
    have hc' := GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff F K D N δ f hf s (fun j => algebraMap F K (v (Sum.inl j))) (fun j => algebraMap F K (v (Sum.inr j)))
    exact GlobalTheory.T.not_square_linear_factor_of_pencilLineDiscriminant_ne_zero F K D N δ f s _ _ hδ hc'.1 hc'.2 hs

end GlobalTheory.PencilDisc
