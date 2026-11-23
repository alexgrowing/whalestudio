import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocQuot
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsNoetherIntegralClosure
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem exists_mul_isIntegral_of_eq_mul_inv {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (R A : Subalgebra F Ω) (hRA : R ≤ A)
    (hloc : ∀ a ∈ A, ∃ r ∈ R, ∃ d ∈ R, d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹)
    {x : Ω} (hx : IsIntegral A x) : ∃ d ∈ R, d ≠ 0 ∧ d⁻¹ ∈ A ∧ IsIntegral R (d * x) := by
  let M : Submonoid R :=
    { carrier := {d | (d : Ω) ≠ 0 ∧ (d : Ω)⁻¹ ∈ A}
      mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, by
        rw [Subalgebra.coe_mul, mul_inv]; exact A.mul_mem ha.2 hb.2⟩
      one_mem' := ⟨one_ne_zero, by rw [Subalgebra.coe_one, inv_one]; exact A.one_mem⟩ }
  let _ : Algebra R A := (Subalgebra.inclusion hRA).toAlgebra
  have : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization M A := by
    refine (isLocalization_iff M A).mpr ⟨fun d => ?_, fun a => ?_, fun {a b} h => ⟨1, ?_⟩⟩
    · exact ⟨⟨_, ⟨_, d.2.2⟩, Subtype.ext (mul_inv_cancel₀ d.2.1), Subtype.ext (inv_mul_cancel₀ d.2.1)⟩, rfl⟩
    · obtain ⟨r, hr, d, hd, hd0, hdA, he⟩ := hloc a a.2
      refine ⟨(⟨r, hr⟩, ⟨⟨d, hd⟩, hd0, hdA⟩), Subtype.ext ?_⟩
      change (a : Ω) * d = r
      rw [he, mul_assoc, inv_mul_cancel₀ hd0, mul_one]
    · have e : ((algebraMap R A a : A) : Ω) = (algebraMap R A b : A) := congrArg Subtype.val h
      have e' : (a : Ω) = b := e
      rw [Subtype.ext e']
  obtain ⟨⟨d, hd0, hdA⟩, hint⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (M := M) (Rₘ := A) x hx
  exact ⟨d, d.2, hd0, hdA, hint⟩

open IntermediateField.algebraAdjoinAdjoin in

theorem exists_finset_integral_span (hN : NoetherIntegralClosureFinite.Statement.{u})
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] {S : Set Ω} (hS : S.Finite)
    (A : Subalgebra F Ω) (L : IntermediateField F Ω) (hRA : Algebra.adjoin F S ≤ A)
    (hloc : ∀ a ∈ A, ∃ r ∈ Algebra.adjoin F S, ∃ d ∈ Algebra.adjoin F S,
      d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹)
    (hEL : IntermediateField.adjoin F S ≤ L)
    (hfin : FiniteDimensional (IntermediateField.adjoin F S) (IntermediateField.extendScalars hEL)) :
    ∃ s : Finset Ω, (∀ e ∈ s, e ∈ L ∧ IsIntegral A e) ∧
      ∀ x ∈ L, IsIntegral A x → x ∈ Submodule.span A (s : Set Ω) := by
  classical
  let L' := IntermediateField.extendScalars hEL
  let _ : Algebra (Algebra.adjoin F S) L' :=
    ((algebraMap (IntermediateField.adjoin F S) L').comp
      (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S))).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) (IntermediateField.adjoin F S) L' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType F (Algebra.adjoin F S) := Algebra.FiniteType.adjoin_of_finite hS
  obtain ⟨t, ht⟩ := Module.finite_def.mp
    (hN F (Algebra.adjoin F S) (IntermediateField.adjoin F S) L')
  let ι₀ : L' →ₐ[Algebra.adjoin F S] Ω := { L'.val.toRingHom with commutes' := fun _ => rfl }
  have hι₀ : Function.Injective ι₀ := Subtype.val_injective
  let _ : Algebra (Algebra.adjoin F S) A := (Subalgebra.inclusion hRA).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨t.image fun y => ι₀ y.1, ?_, fun x hx hxA => ?_⟩
  · intro e he
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp he
    exact ⟨(IntermediateField.mem_extendScalars hEL).mp y.1.2,
      ((isIntegral_algHom_iff ι₀ hι₀).mpr y.2).tower_top⟩
  obtain ⟨d, hd, hd0, hdA, hint⟩ := exists_mul_isIntegral_of_eq_mul_inv _ A hRA hloc hxA
  let z : integralClosure (Algebra.adjoin F S) L' :=
    ⟨⟨d * x, (IntermediateField.mem_extendScalars hEL).mpr
      (mul_mem (hEL (IntermediateField.algebra_adjoin_le_adjoin F S hd)) hx)⟩,
      (isIntegral_algHom_iff ι₀ hι₀).mp hint⟩
  have hz : ι₀ z ∈ Submodule.span (Algebra.adjoin F S) ((t.image fun y => ι₀ y.1 : Finset Ω) : Set Ω) := by
    have hzt : z ∈ Submodule.span (Algebra.adjoin F S) (t : Set _) := ht ▸ Submodule.mem_top
    have := Submodule.mem_map_of_mem
      (f := ι₀.toLinearMap.comp (integralClosure (Algebra.adjoin F S) L').val.toLinearMap) hzt
    rw [Submodule.map_span] at this
    rw [Finset.coe_image]
    exact this
  have e : (⟨d⁻¹, hdA⟩ : A) • (d * x) = x := by
    rw [Subalgebra.smul_def, smul_eq_mul, ← mul_assoc]
    change d⁻¹ * d * x = x
    rw [inv_mul_cancel₀ hd0, one_mul]
  rw [← e]
  exact Submodule.smul_mem _ _ (Submodule.span_le_restrictScalars (Algebra.adjoin F S) A _ hz)

section Chart

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem isMultiHomog_chartMonomial (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by
  have hb : (∑ k, b k • blockWeight ι ⟨k, u k⟩) = b := by
    funext k
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  have h := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩)
    fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (b k)
  unfold IsMultiHomog chartMonomial
  convert h using 1
  exact hb.symm

omit [DecidableEq K] in

theorem chartMonomial_not_mem_of_notMem (W : Ideal (MRing ι F)) [W.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) (b : K → ℕ) : chartMonomial u b ∉ W :=
  (Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (hu k) _ : chartMonomial u b ∈ W.primeCompl)

theorem degZeroLoc_map_eq_mul_inv (hQ : DegZeroLocQuot.Statement.{u})
    (hD : MChartDehomog.Statement.{u}) (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) {Ω : Type*} [Field Ω]
    [Algebra F Ω] (φ : FractionRing (MRing ι F ⧸ P) →ₐ[F] Ω) :
    Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))) ≤ (degZeroLoc P {W}).map φ ∧
      ∀ a ∈ (degZeroLoc P {W}).map φ,
        ∃ r ∈ Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))),
        ∃ d ∈ Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))),
          d ≠ 0 ∧ d⁻¹ ∈ (degZeroLoc P {W}).map φ ∧ a = r * d⁻¹ := by
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k h => hu k (hPW h)
  have hW1 : ∀ W' ∈ ({W} : Set (Ideal (MRing ι F))), W'.IsPrime := fun W' h => by
    rw [Set.mem_singleton_iff.mp h]; infer_instance
  have hmem : ∀ p, φ (chartMap P u p) ∈
      Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))) := fun p => by
    rw [← aeval_range]
    refine ⟨p, ?_⟩
    change aeval _ p = (φ.comp (chartMap P u)) p
    rw [chartMap, comp_aeval]
    simp
  have hq : ∀ g : MRing ι F, g ∉ P → algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P g) ≠ 0 := fun g hg => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hg
  refine ⟨Algebra.adjoin_le ?_, fun a ha => ?_⟩
  · rintro _ ⟨v, rfl⟩
    refine Subalgebra.mem_map.mpr ⟨_, div_mem_degZeroLoc P {W} (b := blockWeight ι v)
      (isWeightedHomogeneous_X F _ v) (isWeightedHomogeneous_X F (blockWeight ι) ⟨v.1, u v.1⟩)
      (huP v.1) (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hu v.1), ?_⟩
    simp [chartMap]
  obtain ⟨a, haA, rfl⟩ := Subalgebra.mem_map.mp ha
  obtain ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ := hQ F K ι P {W} hW1 a haA
  have hm := chartMonomial_not_mem_of_notMem (F := F) W u hu b
  have hm0 := hq _ fun h => hm (hPW h)
  have hg0 := hq g hgP
  refine ⟨φ (chartMap P u f), hmem f, φ (chartMap P u g), hmem g, ?_, ?_, ?_⟩
  · rw [hD F K ι P u huP g b hg, map_ne_zero]
    exact div_ne_zero hg0 hm0
  · rw [hD F K ι P u huP g b hg, ← map_inv₀, inv_div]
    exact Subalgebra.mem_map.mpr ⟨_, div_mem_degZeroLoc P {W} (isMultiHomog_chartMonomial u b) hg
      hgP (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hgW W rfl), rfl⟩
  · rw [hD F K ι P u huP f b hf, hD F K ι P u huP g b hg, ← map_inv₀, ← map_mul]
    congr 1
    field_simp

end Chart

end

end GroundTheory.Heights₂.Heights.FieldNumbers
