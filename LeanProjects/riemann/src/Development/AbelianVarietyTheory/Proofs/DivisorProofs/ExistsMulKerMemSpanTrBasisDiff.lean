import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace GlobalTheory.FieldPair

section Graph

variable {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (ρ : κ →ₐ[ℂ] κ')

private def graphDiff (a : κ) : κ ⊗[ℂ] κ' := a ⊗ₜ[ℂ] (1 : κ') - (1 : κ) ⊗ₜ[ℂ] ρ a

private theorem tmul_one_mul (a b : κ) :
    (a * b) ⊗ₜ[ℂ] (1 : κ') = (a ⊗ₜ[ℂ] (1 : κ')) * (b ⊗ₜ[ℂ] (1 : κ')) := by
  simp [Algebra.TensorProduct.tmul_mul_tmul]

private theorem one_tmul_mul (a b : κ') :
    (1 : κ) ⊗ₜ[ℂ] (a * b) = ((1 : κ) ⊗ₜ[ℂ] a) * ((1 : κ) ⊗ₜ[ℂ] b) := by
  simp [Algebra.TensorProduct.tmul_mul_tmul]

private theorem graphDiff_mul (a b : κ) :
    graphDiff ρ (a * b) = (a ⊗ₜ[ℂ] (1 : κ')) * graphDiff ρ b + ((1 : κ) ⊗ₜ[ℂ] ρ b) * graphDiff ρ a := by
  simp only [graphDiff, map_mul, tmul_one_mul, one_tmul_mul]
  ring

private theorem graphDiff_mul' (a b : κ) :
    graphDiff ρ (a * b) - ((a ⊗ₜ[ℂ] (1 : κ')) * graphDiff ρ b + (b ⊗ₜ[ℂ] (1 : κ')) * graphDiff ρ a) =
      -(graphDiff ρ a * graphDiff ρ b) := by
  simp only [graphDiff, map_mul, tmul_one_mul, one_tmul_mul]
  ring

private theorem graphDiff_add (a b : κ) : graphDiff ρ (a + b) = graphDiff ρ a + graphDiff ρ b := by
  simp only [graphDiff, map_add, TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

private theorem graphDiff_algebraMap (r : ℂ) : graphDiff ρ (algebraMap ℂ κ r) = 0 := by
  simp only [graphDiff, AlgHom.commutes]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, sub_self]

private theorem graphDiff_inv (a : κ) (ha : a ≠ 0) :
    graphDiff ρ a⁻¹ = -((a⁻¹ ⊗ₜ[ℂ] ρ a⁻¹) * graphDiff ρ a) := by
  have h1 : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  simp only [graphDiff, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ ha, mul_one,
    one_mul, h1]
  abel

private def closureField (L : Ideal (κ ⊗[ℂ] κ')) : IntermediateField ℂ κ where
  carrier := {a | graphDiff ρ a ∈ L}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, graphDiff_mul] at *
    exact L.add_mem (L.mul_mem_left _ hb) (L.mul_mem_left _ ha)
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, graphDiff_add] at *
    exact L.add_mem ha hb
  algebraMap_mem' r := by
    simp only [Set.mem_setOf_eq, graphDiff_algebraMap]
    exact L.zero_mem
  inv_mem' a ha := by
    by_cases h : a = 0
    · subst h; simpa using ha
    · simp only [Set.mem_setOf_eq, graphDiff_inv ρ a h] at *
      exact L.neg_mem (L.mul_mem_left _ ha)

private theorem sub_mem_span (x : κ ⊗[ℂ] κ') :
    x - (1 : κ) ⊗ₜ[ℂ] (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x) ∈
      Ideal.span (Set.range (graphDiff ρ)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    have e : a ⊗ₜ[ℂ] b - (1 : κ) ⊗ₜ[ℂ] (ρ a * (AlgHom.id ℂ κ') b) = graphDiff ρ a * ((1 : κ) ⊗ₜ[ℂ] b) := by
      simp [graphDiff, sub_mul, Algebra.TensorProduct.tmul_mul_tmul]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, rfl⟩)
  | add x y hx hy =>
    rw [map_add, TensorProduct.tmul_add]
    convert Ideal.add_mem _ hx hy using 1
    abel

private theorem graphDiff_mem_ker (a : κ) :
    graphDiff ρ a ∈ RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) := by
  simp [graphDiff, RingHom.mem_ker, Algebra.TensorProduct.productMap_apply_tmul]

private theorem ker_le_span :
    RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) ≤
      Ideal.span (Set.range (graphDiff ρ)) := by
  intro x hx
  have h := sub_mem_span ρ x
  rw [RingHom.mem_ker] at hx
  rwa [hx, TensorProduct.tmul_zero, sub_zero] at h

private theorem graphDiff_mem_of_isAlgebraic (L : Ideal (κ ⊗[ℂ] κ'))
    (hL : RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) *
      RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) ≤ L)
    (K : IntermediateField ℂ κ) (hK : K ≤ closureField ρ L) [Algebra.IsAlgebraic K κ] (x : κ) :
    graphDiff ρ x ∈ L := by
  let D0 : κ →ₗ[ℂ] (κ ⊗[ℂ] κ') ⧸ L := (Ideal.Quotient.mkₐ ℂ L).toLinearMap ∘ₗ
    ((TensorProduct.mk ℂ κ κ').flip 1 - (TensorProduct.mk ℂ κ κ' 1) ∘ₗ ρ.toLinearMap)
  have hD0 : ∀ a, D0 a = Ideal.Quotient.mk L (graphDiff ρ a) := fun a => rfl
  have hsmul : ∀ (a : κ) (y : κ ⊗[ℂ] κ'),
      a • Ideal.Quotient.mk L y = Ideal.Quotient.mk L ((a ⊗ₜ[ℂ] (1 : κ')) * y) := by
    intro a y
    rw [← Ideal.Quotient.mkₐ_eq_mk κ, ← map_smul, Algebra.smul_def,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  let D : Derivation ℂ κ ((κ ⊗[ℂ] κ') ⧸ L) := Derivation.mk' D0 (fun a b => by
    rw [hD0, hD0, hD0, hsmul, hsmul, ← map_add, Ideal.Quotient.eq, graphDiff_mul']
    exact L.neg_mem (hL (Ideal.mul_mem_mul (graphDiff_mem_ker ρ a) (graphDiff_mem_ker ρ b))))
  have hD : ∀ a, D a = Ideal.Quotient.mk L (graphDiff ρ a) := fun a => rfl
  letI : Module K ((κ ⊗[ℂ] κ') ⧸ L) := Module.compHom _ (algebraMap K κ)
  have key := Derivation.apply_aeval_eq' (0 : Derivation ℂ K ((κ ⊗[ℂ] κ') ⧸ L)) D 0
    (fun c => by
      rw [LinearMap.zero_apply, hD, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
      exact hK c.2) x (minpoly K x)
  simp only [minpoly.aeval, map_zero, LinearMap.zero_apply, zero_add] at key
  have hne := Polynomial.Separable.aeval_derivative_ne_zero (Algebra.IsSeparable.isSeparable K x)
    (minpoly.aeval K x)
  have h0 : D x = 0 := by
    have hz : ∀ q, PolynomialModule.map κ (0 : ((κ ⊗[ℂ] κ') ⧸ L) →ₗ[K] ((κ ⊗[ℂ] κ') ⧸ L)) q = 0 := by
      intro q
      ext i
      simp [PolynomialModule.map]
    have key' := key.symm
    rw [hz, map_zero, zero_add] at key'
    have h2 := congrArg (fun v => ((Polynomial.aeval x) (Polynomial.derivative (minpoly K x)))⁻¹ • v) key'
    simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] using h2
  rwa [hD, Ideal.Quotient.eq_zero_iff_mem] at h0

end Graph

theorem exists_mul_ker_mem_span_trBasis_diff :
    ∀ {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (k : ℕ) (z : Fin k → κ) (ρ : κ →ₐ[ℂ] κ') (O : Subring κ), TrBasis (algebraMap ℂ κ) z → IsLocModel (algebraMap ℂ κ) O → ∃ e : TensorProduct ℂ κ κ', Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') e = 1 ∧ ∀ a ∈ RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')), e * a ∈ Ideal.span (Set.range fun i => (TensorProduct.tmul ℂ (z i) (1 : κ') - TensorProduct.tmul ℂ (1 : κ) (ρ (z i)))) := by
  intro κ κ' _ _ _ _ k z ρ O hz hO
  set J := RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) with hJ
  set I := Ideal.span (Set.range fun i =>
    (TensorProduct.tmul ℂ (z i) (1 : κ') - TensorProduct.tmul ℂ (1 : κ) (ρ (z i)))) with hI

  have hfg : J.FG := by
    letI := ((algebraMap ℂ κ).codRestrict O hO.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ O := hO.essFiniteType
    obtain ⟨s, hs⟩ := Algebra.EssFiniteType.cond (R := ℂ) (S := O)
    set L₀ : Ideal (κ ⊗[ℂ] κ') := Ideal.span (graphDiff ρ '' ((↑) '' (s : Set O))) with hL₀
    have hadj : ∀ w : O, w ∈ Algebra.adjoin ℂ (s : Set O) → (w : κ) ∈ closureField ρ L₀ := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => exact Ideal.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      | algebraMap r => exact (closureField ρ L₀).algebraMap_mem r
      | add x y _ _ hx hy => exact (closureField ρ L₀).add_mem hx hy
      | mul x y _ _ hx hy => exact (closureField ρ L₀).mul_mem hx hy
    have hO' : ∀ y : O, (y : κ) ∈ closureField ρ L₀ := by
      intro y
      obtain ⟨⟨a, u⟩, e⟩ := @IsLocalization.surj _ _ _ _ _ _ hs y
      have hu : IsUnit ((u : Algebra.adjoin ℂ (s : Set O)) : O) := u.2
      have hu0 : (((u : Algebra.adjoin ℂ (s : Set O)) : O) : κ) ≠ 0 := by
        intro h0
        exact hu.ne_zero (Subtype.ext h0)
      have e' : (y : κ) * (((u : Algebra.adjoin ℂ (s : Set O)) : O) : κ) =
          ((a : O) : κ) := congrArg Subtype.val e
      rw [← eq_div_iff hu0] at e'
      rw [e', div_eq_mul_inv]
      exact (closureField ρ L₀).mul_mem (hadj _ a.2) ((closureField ρ L₀).inv_mem (hadj _ (u : Algebra.adjoin ℂ (s : Set O)).2))
    have hall : ∀ x : κ, x ∈ closureField ρ L₀ := by
      intro x
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hO.frac x
      rw [← eq_div_iff hb0] at e
      rw [e, div_eq_mul_inv]
      exact (closureField ρ L₀).mul_mem (hO' ⟨a, ha⟩) ((closureField ρ L₀).inv_mem (hO' ⟨b, hb⟩))
    have hJL : J = L₀ := le_antisymm
      ((ker_le_span ρ).trans (Ideal.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hall a)))
      (Ideal.span_le.2 (by rintro _ ⟨a, -, rfl⟩; exact graphDiff_mem_ker ρ a))
    rw [hJL, hL₀]
    exact Submodule.fg_span ((s.finite_toSet.image _).image _)

  have hle : J ≤ I ⊔ J * J := by
    have hz' : IsTranscendenceBasis ℂ z := by
      have e : (algebraMap ℂ κ).toAlgebra = ‹Algebra ℂ κ› := Algebra.algebra_ext _ _ fun _ => rfl
      unfold TrBasis at hz
      rwa [e] at hz
    haveI := hz'.isAlgebraic_field
    have hK : IntermediateField.adjoin ℂ (Set.range z) ≤ closureField ρ (I ⊔ J * J) := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
    refine (ker_le_span ρ).trans (Ideal.span_le.2 ?_)
    rintro _ ⟨a, rfl⟩
    exact graphDiff_mem_of_isAlgebraic ρ _ le_sup_right _ hK a
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl hle
  refine ⟨r, ?_, fun a ha => ?_⟩
  · rw [hJ, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hr1
    exact hr1
  · have := hr (Submodule.smul_mem_pointwise_smul a r J ha)
    rwa [smul_eq_mul] at this

end GlobalTheory.FieldPair
