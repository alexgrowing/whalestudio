import Mathlib
import GroundTheory.AutomorphicForms.SphericalIntegral
import GroundTheory.AutomorphicForms.SatakeSymmetric
import GroundTheory.LocalFields.LocalFourierHaar

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory GLnLocal Iwasawa Parabolic HeckeAlgebra AddMonoidAlgebra
open scoped NNReal

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem prod_zpow_eq_zpow_sum {G₀ : Type*} [CommGroupWithZero G₀] {a : G₀} (ha : a ≠ 0)
    {ι : Type*} (s : Finset ι) (f : ι → ℤ) : ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ ha]

variable (F) in

theorem modulus_uniformizer :
    Measures.modulus (GLnLocal.uniformizer F : F) = ((qF F : ℝ≥0))⁻¹ := by
  borelize F
  have h := Measures.modulus_units (uniformizerUnit F)
  rw [coe_uniformizerUnit] at h
  rw [h, GroundTheory.LocalField.distribHaarChar_eq_modulus, coe_uniformizerUnit,
    GroundTheory.LocalField.modulus_of_ne_zero,
    GroundTheory.LocalField.ord_uniformizer (irreducible_uniformizer F)]
  · simp [qF, GroundTheory.LocalField.residueCard]
  · exact (uniformizerUnit F).ne_zero

def rhoPair (l : Fin n → ℤ) : ℤ := ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * l i

theorem rhoPair_single (i : Fin n) :
    rhoPair (Pi.single i 1 : Fin n → ℤ) = (n : ℤ) - 1 - 2 * (i : ℕ) := by
  rw [rhoPair, Finset.sum_eq_single i (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

variable (F n) in

def torusBorel (l : Fin n → ℤ) : blockUpper F n (id : Fin n → Fin n) :=
  ⟨torusPow F n l, torusPow_mem_borel F n l⟩

variable (F) in

def halfModulus (l : Fin n → ℤ) : ℂ :=
  sqrtModular F n id (torusBorel F n l)

theorem halfModulus_add (l l' : Fin n → ℤ) :
    halfModulus F (l + l') = halfModulus F l * halfModulus F l' := by
  rw [halfModulus, halfModulus, halfModulus, ← map_mul]
  congr 1
  exact Subtype.ext (torusPow_add l l')

theorem halfModulus_zero : halfModulus F (0 : Fin n → ℤ) = 1 := by
  rw [halfModulus, ← map_one (sqrtModular F n id)]
  congr 1
  exact Subtype.ext torusPow_zero

variable (F) in

def sqrtQ : ℂ := ((NNReal.sqrt (qF F : ℝ≥0) : ℝ) : ℂ)

theorem qF_nnreal_ne_zero : ((qF F : ℝ≥0)) ≠ 0 := by
  exact_mod_cast (qF_pos (F := F)).ne'

theorem sqrtQ_ne_zero : sqrtQ F ≠ 0 := by
  rw [sqrtQ, Complex.ofReal_ne_zero, NNReal.coe_ne_zero, Ne, NNReal.sqrt_eq_zero]
  exact qF_nnreal_ne_zero

theorem sqrtQ_sq : sqrtQ F ^ 2 = (qF F : ℂ) := by
  rw [sqrtQ, ← Complex.ofReal_pow, ← NNReal.coe_pow, NNReal.sq_sqrt]
  norm_cast

theorem modularCharacter_torusBorel (l : Fin n → ℤ) :
    Measure.modularCharacter (torusBorel F n l) = ((qF F : ℝ≥0)) ^ (-rhoPair l) := by
  rw [Measures.modularCharacter_borel]
  have hd : ∀ i, (((torusBorel F n l : blockUpper F n (id : Fin n → Fin n)) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) i i = (GLnLocal.uniformizer F : F) ^ l i := fun i => by
    simp [torusBorel, coe_torusPow]
  simp only [hd, map_zpow₀, modulus_uniformizer]
  rw [rhoPair, ← Finset.sum_neg_distrib, ← prod_zpow_eq_zpow_sum qF_nnreal_ne_zero]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [inv_zpow', ← zpow_mul]
  congr 1
  ring

theorem halfModulus_eq (l : Fin n → ℤ) : halfModulus F l = sqrtQ F ^ (-rhoPair l) := by
  have h1 : NNReal.sqrt (Measure.modularCharacter (torusBorel F n l)) =
      NNReal.sqrt (qF F : ℝ≥0) ^ (-rhoPair l) := by
    rw [modularCharacter_torusBorel, NNReal.sqrt_eq_iff_eq_sq, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, NNReal.sq_sqrt]
  change ((NNReal.sqrt (Measure.modularCharacter (torusBorel F n l)) : ℝ) : ℂ) = _
  rw [h1, NNReal.coe_zpow, Complex.ofReal_zpow]
  rfl

theorem halfModulus_ne_zero (l : Fin n → ℤ) : halfModulus F l ≠ 0 := by
  rw [halfModulus_eq]
  exact zpow_ne_zero _ sqrtQ_ne_zero

variable (F n) in

def halfPoint : Fin n → ℂˣ :=
  fun i => Units.mk0 (halfModulus F (Pi.single i 1)) (halfModulus_ne_zero _)

theorem monomialChar_halfPoint (l : Fin n → ℤ) : monomialChar l (halfPoint F n) = halfModulus F l := by
  rw [monomialChar_apply, halfModulus_eq, rhoPair, ← Finset.sum_neg_distrib,
    ← prod_zpow_eq_zpow_sum sqrtQ_ne_zero]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_zpow_eq_zpow_val, halfPoint, Units.val_mk0, halfModulus_eq, rhoPair_single,
    ← zpow_mul]
  congr 1
  ring

variable (F n) in

def normHom : Multiplicative (Fin n → ℤ) →* LaurentRing n where
  toFun l := single (Multiplicative.toAdd l) (halfModulus F (Multiplicative.toAdd l))
  map_one' := by
    rw [toAdd_one, halfModulus_zero]
    rfl
  map_mul' a b := by
    rw [toAdd_mul, halfModulus_add, single_mul_single]

variable (F n) in

def normalize : LaurentRing n →ₐ[ℂ] LaurentRing n :=
  AddMonoidAlgebra.lift ℂ (LaurentRing n) (Fin n → ℤ) (normHom F n)

theorem normalize_single (l : Fin n → ℤ) (c : ℂ) :
    normalize F n (single l c) = single l (c * halfModulus F l) := by
  rw [normalize, AddMonoidAlgebra.lift_single]
  change c • single l (halfModulus F l) = _
  rw [smul_single']

theorem coeff_normalize (p : LaurentRing n) (l : Fin n → ℤ) :
    (normalize F n p).coeff l = halfModulus F l * p.coeff l := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p p' hp hp' => rw [map_add, coeff_add, coeff_add, Finsupp.add_apply, Finsupp.add_apply, hp,
      hp', mul_add]
  | single m c =>
    rw [normalize_single, coeff_single, coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h
      ring
    · simp

theorem normalize_injective : Function.Injective (normalize F n) := by
  intro p p' h
  apply AddMonoidAlgebra.coeff_injective
  ext l
  have := congrArg (fun r : LaurentRing n => r.coeff l) h
  simp only [coeff_normalize] at this
  exact mul_left_cancel₀ (halfModulus_ne_zero l) this

theorem evalAt_normalize (z : Fin n → ℂˣ) (p : LaurentRing n) :
    evalAt z (normalize F n p) = evalAt (z * halfPoint F n) p := by
  have : (evalAt z).comp (normalize F n) = evalAt (z * halfPoint F n) := by
    refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
    rw [AlgHom.comp_apply, normalize_single, evalAt_single, evalAt_single, map_mul,
      monomialChar_halfPoint]
    ring
  exact AlgHom.congr_fun this p

variable (F n) in

def torusLevi (l : Fin n → ℤ) : levi F n (id : Fin n → Fin n) :=
  ⟨torusPow F n l, mem_levi.2 fun i j hij => by
    rw [coe_torusPow, Matrix.diagonal_apply_ne _ (by simpa using hij)]⟩

variable (F) in

def paramChar (z : Fin n → ℂˣ) : levi F n (id : Fin n → Fin n) →* ℂ :=
  unramifiedChar (z * halfPoint F n)

theorem isUnramified_paramChar (z : Fin n → ℂˣ) : IsUnramified (paramChar F z) :=
  isUnramified_unramifiedChar _

theorem paramChar_torusLevi (z : Fin n → ℂˣ) (l : Fin n → ℤ) :
    paramChar F z (torusLevi F n l) = monomialChar l z := by
  change monomialChar (iwasawaExponent F n (torusPow F n l)) (z * halfPoint F n) *
    invSqrtModular F n id (leviIncl (torusLevi F n l)) = _
  have h1 : leviIncl (torusLevi F n l) = torusBorel F n l := Subtype.ext rfl
  rw [iwasawaExponent_torusPow, h1, map_mul, monomialChar_halfPoint]
  have h2 : invSqrtModular F n id (torusBorel F n l) = (halfModulus F l)⁻¹ := rfl
  rw [h2, mul_assoc, mul_inv_cancel₀ (halfModulus_ne_zero l), mul_one]

theorem normalize_yElt (i : Fin n) :
    normalize F n (yElt F i) = sqrtQ F ^ ((n : ℤ) - 1) • monomial (Pi.single i 1) := by
  rw [yElt, normalize_single, smul_single', mul_one, halfModulus_eq, rhoPair_single, ← sqrtQ_sq,
    ← pow_mul, ← zpow_natCast, ← zpow_add₀ sqrtQ_ne_zero]
  congr 2
  have := i.is_lt
  push_cast [Nat.sub_sub, Nat.cast_sub (show 1 + (i : ℕ) ≤ n by omega)]
  ring

theorem normalize_esymm_yElt (k : ℕ) :
    normalize F n ((Finset.univ.val.map (yElt F (n := n))).esymm k) =
      (sqrtQ F ^ ((n : ℤ) - 1)) ^ k • polyEmb n (MvPolynomial.esymm (Fin n) ℂ k) := by
  classical
  rw [Finset.esymm_map_val, map_sum, MvPolynomial.esymm, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [map_prod, map_prod]
  simp only [normalize_yElt, polyEmb_X, smul_single', mul_one]
  rw [AddMonoidAlgebra.prod_single, AddMonoidAlgebra.prod_single, Finset.prod_const,
    Finset.prod_const_one, smul_single', mul_one, (Finset.mem_powersetCard.1 ht).2]

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

variable (μ) in

def satakeTransform : SphericalHecke μ (F := F) (n := n) →ₐ[ℂ] LaurentRing n :=
  (normalize F n).comp (satakeHom μ)

theorem satakeTransform_apply (h : SphericalHecke μ (F := F) (n := n)) :
    satakeTransform μ h = normalize F n (satake μ h) :=
  rfl

theorem satakeTransform_eq_sum (h : SphericalHecke μ (F := F) (n := n)) :
    satakeTransform μ h = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) •
      ∑ x ∈ cosetSupport h, single (iwasawaExponent F n x.out)
        (halfModulus F (iwasawaExponent F n x.out) * (h : HeckeAlgebra μ) x.out) := by
  rw [satakeTransform_apply, satake, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [normalize_single, mul_comm]

theorem coeff_satakeTransform (h : SphericalHecke μ (F := F) (n := n)) (l : Fin n → ℤ) :
    (satakeTransform μ h).coeff l = halfModulus F l * (satake μ h).coeff l :=
  coeff_normalize _ l

theorem satakeTransform_injective : Function.Injective (satakeTransform μ (F := F) (n := n)) :=
  (normalize_injective (F := F)).comp satakeHom_injective

theorem sphericalCharacter_paramChar (z : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    sphericalCharacter μ (isUnramified_paramChar (F := F) z) h = evalAt z (satakeTransform μ h) := by
  rw [satakeTransform_apply, evalAt_normalize, evalAt_satake]
  rfl

theorem symmetricLaurent_le_range :
    symmetricLaurent n ≤ (satakeTransform μ (F := F) (n := n)).range := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  refine symmetricLaurent_le (fun k => ?_) ?_
  · obtain ⟨h, hh⟩ := (AlgHom.mem_range _).1 (esymm_yElt_mem (μ := μ) (F := F) (n := n) k)
    have hc : (sqrtQ F ^ ((n : ℤ) - 1)) ^ k ≠ 0 := pow_ne_zero _ (zpow_ne_zero _ sqrtQ_ne_zero)
    have : polyEmb n (MvPolynomial.esymm (Fin n) ℂ k) =
        ((sqrtQ F ^ ((n : ℤ) - 1)) ^ k)⁻¹ • satakeTransform μ h := by
      rw [satakeTransform_apply, ← satakeHom_apply, hh, normalize_esymm_yElt, smul_smul,
        inv_mul_cancel₀ hc, one_smul]
    rw [this]
    exact Subalgebra.smul_mem _ (AlgHom.mem_range_self _ _) _
  · have : monomial (fun _ => (-1 : ℤ)) = ((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
        halfModulus F (fun _ : Fin n => (-1 : ℤ)))⁻¹ • satakeTransform μ (centralHecke μ) := by
      rw [satakeTransform_apply, satake_centralHecke, map_smul, normalize_single, smul_smul,
        smul_single']
      field_simp [hK, halfModulus_ne_zero (F := F) (fun _ : Fin n => (-1 : ℤ))]
    rw [this]
    exact Subalgebra.smul_mem _ (AlgHom.mem_range_self _ _) _

end Spherical

end GroundTheory.Automorphic
