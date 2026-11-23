import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap nonZeroDivisors Classical
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published NumberField.mixedEmbedding

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

variable (F) in

def gauss : 𝓢(NumberField.mixedEmbedding.mixedSpace F, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean F)
    (gaussianSchwartz (NumberField.mixedEmbedding.euclidean.mixedSpace F))

def gJ (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : Ad F → ℂ := schwartzBruhatTensor (gauss F) (cosetIndicator J 0)

theorem gJ_mem (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : gJ J ∈ schwartzBruhat F :=
  schwartzBruhatTensor_mem _ (cosetIndicator_mem_finiteSchwartzBruhat J 0)

variable (F) in

def invN (N : ℕ) : IdeleGroup F :=
  diagonal F (Units.mk0 ((N : F) + 1)⁻¹ (inv_ne_zero (Nat.cast_add_one_ne_zero N)))

theorem pInf_apply_eq (x : Ad F) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F x v = (homeomorphMixedSpace F x.1).1 ⟨v, IsTotallyReal.isReal v⟩ := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  rfl

theorem continuous_pInf_apply (v : InfinitePlace F) : Continuous fun x : Ad F => UpperTheory.V.TR.pInf F x v := by
  simp_rw [pInf_apply_eq]
  exact (continuous_apply (⟨v, IsTotallyReal.isReal v⟩ : {w : InfinitePlace F // w.IsReal})).comp
    (continuous_fst.comp ((homeomorphMixedSpace F).continuous.comp continuous_fst))

theorem arch_norm_le (x y : UpperTheory.V.TR.Rinf F) :
    ‖arch x y‖ ≤ Real.exp (-(Real.pi - 1) * ∑ v, (x v ^ 2 + y v ^ 2)) := by
  unfold arch
  rw [norm_prod, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_
  have he : -(Real.pi : ℂ) * (((x v : ℝ) : ℂ) ^ 2 + ((y v : ℝ) : ℂ) ^ 2) =
      ((-Real.pi * (x v ^ 2 + y v ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, he, Complex.norm_exp_ofReal]
  have h1 : ‖((x v : ℝ) : ℂ) + Complex.I * ((y v : ℝ) : ℂ)‖ ≤ |x v| + |y v| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
  have h2 : |x v| + |y v| ≤ Real.exp (x v ^ 2 + y v ^ 2) := by
    have := Real.add_one_le_exp (x v ^ 2 + y v ^ 2)
    nlinarith [sq_abs (x v), sq_abs (y v), sq_nonneg (|x v| - 1), sq_nonneg (|y v| - 1)]
  calc ‖((x v : ℝ) : ℂ) + Complex.I * ((y v : ℝ) : ℂ)‖ * Real.exp (-Real.pi * (x v ^ 2 + y v ^ 2))
      ≤ Real.exp (x v ^ 2 + y v ^ 2) * Real.exp (-Real.pi * (x v ^ 2 + y v ^ 2)) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le
    _ = Real.exp (-(Real.pi - 1) * (x v ^ 2 + y v ^ 2)) := by
        rw [← Real.exp_add]; congr 1; ring

theorem gauss_apply (m : NumberField.mixedEmbedding.mixedSpace F) :
    gauss F m = ((Real.exp (-Real.pi * ‖mixedToEuclidean F m‖ ^ 2) : ℝ) : ℂ) := rfl

theorem norm_gauss (m : NumberField.mixedEmbedding.mixedSpace F) :
    ‖gauss F m‖ = Real.exp (-Real.pi * ∑ v : InfinitePlace F, (m.1 ⟨v, IsTotallyReal.isReal v⟩) ^ 2) := by
  rw [gauss_apply, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, norm_mixedToEuclidean_sq]
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => (InfinitePlace.not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2⟩
  rw [Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}), Finset.sum_empty, mul_zero, add_zero]
  congr 2
  exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _ fun w => rfl

theorem invN_smul (N : ℕ) (x : Ad F) : invN F N • x = algebraMap F (Ad F) ((N : F) + 1)⁻¹ * x := by
  rw [Units.smul_def, invN, coe_diagonal, Units.val_mk0]
  rfl

theorem pInf_algebraMap_mul (a : F) (x : Ad F) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F (algebraMap F (Ad F) a * x) v =
      InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) a * UpperTheory.V.TR.pInf F x v := by
  rw [map_mul, Pi.mul_apply, pInf_apply_eq (algebraMap F (Ad F) a)]
  congr 1
  change (homeomorphMixedSpace F (algebraMap F (InfiniteAdeleRing F) a)).1 _ = _
  rw [homeomorphMixedSpace_algebraMap, mixedEmbedding_apply_isReal]

theorem norm_gJ_invN (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (x : Ad F) :
    ‖gJ J (invN F N • x)‖ = Real.exp (-Real.pi * ∑ v, (((N : ℝ) + 1)⁻¹ * UpperTheory.V.TR.pInf F x v) ^ 2) *
      (if algebraMap F (Af F) ((N : F) + 1)⁻¹ * pFin F x ∈ idealFiniteAdeles J then 1 else 0) := by
  rw [invN_smul]
  unfold gJ schwartzBruhatTensor
  rw [norm_mul, norm_gauss, cosetIndicator_apply, sub_zero]
  have hs : ∑ v : InfinitePlace F, ((homeomorphMixedSpace F (algebraMap F (Ad F) ((N : F) + 1)⁻¹ * x).1).1
      ⟨v, IsTotallyReal.isReal v⟩) ^ 2 = ∑ v, (((N : ℝ) + 1)⁻¹ * UpperTheory.V.TR.pInf F x v) ^ 2 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← pInf_apply_eq, pInf_algebraMap_mul]
    congr 2
    simp [map_inv₀]
  rw [hs]
  congr 1
  · have h2 : (algebraMap F (Ad F) ((N : F) + 1)⁻¹ * x).2 = algebraMap F (Af F) ((N : F) + 1)⁻¹ * pFin F x := rfl
    rw [h2]
    split_ifs <;> simp

theorem pInf_vecMul (y : Fin 2 → Ad F) (A : Matrix (Fin 2) (Fin 2) (Ad F)) (i : Fin 2) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F ((y ᵥ* A) i) v =
      UpperTheory.V.TR.pInf F (y 0) v * UpperTheory.V.TR.pInf F (A 0 i) v + UpperTheory.V.TR.pInf F (y 1) v * UpperTheory.V.TR.pInf F (A 1 i) v := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, map_add, map_mul]

theorem pFin_vecMul (y : Fin 2 → Ad F) (A : Matrix (Fin 2) (Fin 2) (Ad F)) (i : Fin 2) :
    pFin F ((y ᵥ* A) i) = pFin F (y 0) * pFin F (A 0 i) + pFin F (y 1) * pFin F (A 1 i) := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, map_add, map_mul]

private theorem sq_lin_le {a b p q H : ℝ} (hp : |p| ≤ H) (hq : |q| ≤ H) :
    (a * p + b * q) ^ 2 ≤ 2 * H ^ 2 * (a ^ 2 + b ^ 2) := by
  have hp2 : p ^ 2 ≤ H ^ 2 := by
    rw [← sq_abs p]; exact pow_le_pow_left₀ (abs_nonneg p) hp 2
  have hq2 : q ^ 2 ≤ H ^ 2 := by
    rw [← sq_abs q]; exact pow_le_pow_left₀ (abs_nonneg q) hq 2
  nlinarith [sq_nonneg (a * p - b * q), mul_le_mul_of_nonneg_left hp2 (sq_nonneg a),
    mul_le_mul_of_nonneg_left hq2 (sq_nonneg b)]

open Classical in

theorem dom_gen {Kc : Set (Matrix (Fin 2) (Fin 2) (Ad F))} (hK : IsCompact Kc) {L : Set (Af F)} (hL : IsCompact L) :
    ∃ (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ), ∀ A ∈ Kc, ∀ y : Fin 2 → Ad F,
      ‖arch (UpperTheory.V.TR.pInf F (y 0)) (UpperTheory.V.TR.pInf F (y 1))‖ *
          (if pFin F (y 0) ∈ L ∧ pFin F (y 1) ∈ L then (1 : ℝ) else 0) ≤
        ‖gJ J (invN F N • (y ᵥ* A) 0)‖ * ‖gJ J (invN F N • (y ᵥ* A) 1)‖ := by

  have hb : ∀ p : Fin 2 × Fin 2 × InfinitePlace F, ∃ C : ℝ, ∀ A ∈ Kc,
      ‖UpperTheory.V.TR.pInf F (A p.1 p.2.1) p.2.2‖ ≤ C := fun p =>
    hK.exists_bound_of_continuousOn
      ((continuous_pInf_apply p.2.2).comp (continuous_id.matrix_elem p.1 p.2.1)).continuousOn
  choose C hC using hb
  set H : ℝ := 1 + ∑ p, |C p| with hH
  have hent : ∀ A ∈ Kc, ∀ i j v, |UpperTheory.V.TR.pInf F (A i j) v| ≤ H := by
    intro A hA i j v
    have h1 := hC (i, j, v) A hA
    rw [Real.norm_eq_abs] at h1
    have h2 : |C (i, j, v)| ≤ ∑ p, |C p| :=
      Finset.single_le_sum (f := fun p => |C p|) (fun p _ => abs_nonneg _) (Finset.mem_univ _)
    linarith [le_abs_self (C (i, j, v))]

  set N : ℕ := ⌈4 * Real.pi * H ^ 2 / (Real.pi - 1)⌉₊ with hNdef
  have hpi1 : 0 < Real.pi - 1 := by linarith [Real.pi_gt_three]
  have hN : 4 * Real.pi * H ^ 2 ≤ (Real.pi - 1) * ((N : ℝ) + 1) ^ 2 := by
    have h1 : 4 * Real.pi * H ^ 2 / (Real.pi - 1) ≤ (N : ℝ) := Nat.le_ceil _
    have h0 : (0 : ℝ) ≤ N := N.cast_nonneg
    have h2 : (N : ℝ) + 1 ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
    rw [div_le_iff₀ hpi1] at h1
    nlinarith
  set c : ℝ := ((N : ℝ) + 1)⁻¹ with hcdef
  have hc2 : Real.pi * c ^ 2 * (4 * H ^ 2) ≤ Real.pi - 1 := by
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hc : c ^ 2 * ((N : ℝ) + 1) ^ 2 = 1 := by
      rw [hcdef, ← mul_pow, inv_mul_cancel₀ hN1.ne', one_pow]
    calc Real.pi * c ^ 2 * (4 * H ^ 2) = c ^ 2 * (4 * Real.pi * H ^ 2) := by ring
      _ ≤ c ^ 2 * ((Real.pi - 1) * ((N : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left hN (sq_nonneg c)
      _ = Real.pi - 1 := by rw [mul_left_comm, hc, mul_one]

  let f : Fin 2 → (Af F × Af F) × Matrix (Fin 2) (Fin 2) (Ad F) → Af F := fun i p =>
    algebraMap F (Af F) ((N : F) + 1)⁻¹ * (p.1.1 * pFin F (p.2 0 i) + p.1.2 * pFin F (p.2 1 i))
  have hfc : ∀ i, Continuous (f i) := by
    intro i
    have hp : ∀ j, Continuous fun p : (Af F × Af F) × Matrix (Fin 2) (Fin 2) (Ad F) => pFin F (p.2 j i) :=
      fun j => continuous_snd.comp (continuous_snd.matrix_elem j i)
    exact continuous_const.mul (((continuous_fst.comp continuous_fst).mul (hp 0)).add
      ((continuous_snd.comp continuous_fst).mul (hp 1)))
  set S : Set (Af F) := f 0 '' ((L ×ˢ L) ×ˢ Kc) ∪ f 1 '' ((L ×ˢ L) ×ˢ Kc) with hSdef
  have hS : IsCompact S :=
    (((hL.prod hL).prod hK).image (hfc 0)).union (((hL.prod hL).prod hK).image (hfc 1))
  obtain ⟨J, hJ⟩ := exists_subset_idealFiniteAdeles hS
  refine ⟨J, N, fun A hA y => ?_⟩
  split_ifs with hy
  swap
  · rw [mul_zero]; positivity
  rw [mul_one]
  have hfin : ∀ i : Fin 2, algebraMap F (Af F) ((N : F) + 1)⁻¹ * pFin F ((y ᵥ* A) i) ∈ idealFiniteAdeles J := by
    intro i
    apply hJ
    rw [pFin_vecMul]
    have hmem : f i ((pFin F (y 0), pFin F (y 1)), A) ∈ S := by
      fin_cases i
      · exact Or.inl ⟨_, ⟨⟨hy.1, hy.2⟩, hA⟩, rfl⟩
      · exact Or.inr ⟨_, ⟨⟨hy.1, hy.2⟩, hA⟩, rfl⟩
    exact hmem
  rw [norm_gJ_invN, norm_gJ_invN, if_pos (hfin 0), if_pos (hfin 1), mul_one, mul_one, ← Real.exp_add]
  refine (arch_norm_le _ _).trans (Real.exp_le_exp.2 ?_)
  simp_rw [pInf_vecMul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  set a := UpperTheory.V.TR.pInf F (y 0) v
  set b := UpperTheory.V.TR.pInf F (y 1) v
  have L1 : (a * UpperTheory.V.TR.pInf F (A 0 0) v + b * UpperTheory.V.TR.pInf F (A 1 0) v) ^ 2 +
      (a * UpperTheory.V.TR.pInf F (A 0 1) v + b * UpperTheory.V.TR.pInf F (A 1 1) v) ^ 2 ≤ 4 * H ^ 2 * (a ^ 2 + b ^ 2) := by
    have e1 := sq_lin_le (a := a) (b := b) (hent A hA 0 0 v) (hent A hA 1 0 v)
    have e2 := sq_lin_le (a := a) (b := b) (hent A hA 0 1 v) (hent A hA 1 1 v)
    linarith
  have hab : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left L1 (by positivity : (0 : ℝ) ≤ Real.pi * c ^ 2)
  have h4 : Real.pi * c ^ 2 * (4 * H ^ 2 * (a ^ 2 + b ^ 2)) ≤ (Real.pi - 1) * (a ^ 2 + b ^ 2) := by
    calc Real.pi * c ^ 2 * (4 * H ^ 2 * (a ^ 2 + b ^ 2)) = (Real.pi * c ^ 2 * (4 * H ^ 2)) * (a ^ 2 + b ^ 2) := by ring
      _ ≤ (Real.pi - 1) * (a ^ 2 + b ^ 2) := mul_le_mul_of_nonneg_right hc2 hab
  nlinarith [h3, h4]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability
