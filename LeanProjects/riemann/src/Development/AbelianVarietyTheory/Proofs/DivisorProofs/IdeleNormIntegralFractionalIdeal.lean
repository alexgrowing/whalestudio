import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
import GroundTheory.GlobalFields.TateThesis.GlobalZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesAtInfiniteFiniteIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleBaseChangeMemIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetIdelesInIdealStatement
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped Classical nonZeroDivisors TensorProduct
open GlobalTheory.Doubling (absE)
open GlobalTheory.LocIdeal (locId)

noncomputable section

namespace GlobalTheory.TateIdelic

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Global.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem parts_iff (l : (AE F E)ˣ) :
    (l ∈ idelesAt E (evI F) ↔ ((GlobalTheory.IdeleLogHom.toE F E l : AdeleRing (𝓞 E) E)).2 = 1) ∧
    (l ∈ idelesAt E (fun x : AF F => x.2) ↔ ((GlobalTheory.IdeleLogHom.toE F E l : AdeleRing (𝓞 E) E)).1 = 1) :=
  GlobalTheory.T.ideles_at_infinite_finite_iff l

theorem mem_idealFiniteAdeles_of_locId (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0) (z : AE F E)
    (hz : ∀ v : Pl F, compFin F E v z ∈ locId v 𝔞) :
    (adeleTensorAlgEquivLeft F E z).2 ∈ idealFiniteAdeles (Units.mk0 𝔞 h𝔞) :=
  GlobalTheory.T.adele_base_change_mem_ideal 𝔞 h𝔞 z hz

theorem measurableSet_locId (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0) :
    MeasurableSet {l : (AE F E)ˣ | ∀ v : Pl F, compFin F E v (l : AE F E) ∈ locId v 𝔞} :=
  GlobalTheory.T.measurableSet_ideles_in_ideal 𝔞 h𝔞

theorem continuous_toE : Continuous (GlobalTheory.IdeleLogHom.toE F E) := by
  have : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have : IsModuleTopology (AF F) (AdeleRing (𝓞 E) E) := isModuleTopology_adeleRing
  have := IsModuleTopology.toContinuousSMul (AF F) (AdeleRing (𝓞 E) E)
  exact Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).toLinearMap)

theorem toE_ofE (x : IdeleGroup E) : GlobalTheory.IdeleLogHom.toE F E (GlobalTheory.IdeleLogHom.ofE F E x) = x := by
  ext
  simp [GlobalTheory.IdeleLogHom.ofE, GlobalTheory.IdeleLogHom.toE]

variable (F E) in

def toEEquiv : (AE F E)ˣ ≃ₜ* IdeleGroup E where
  toFun := GlobalTheory.IdeleLogHom.toE F E
  invFun := GlobalTheory.IdeleLogHom.ofE F E
  left_inv := GlobalTheory.IdeleLogHom.ofE_toE F E
  right_inv := toE_ofE
  map_mul' := map_mul _
  continuous_toFun := continuous_toE
  continuous_invFun := GlobalTheory.IdeleLogHom.continuous_ofE F E

theorem toInfinite_ofFinite (b : (FiniteAdeleRing (𝓞 E) E)ˣ) : toInfinite E (ofFinite b) = 1 := by
  ext : 1
  rfl

theorem toFinite_ofFinite (b : (FiniteAdeleRing (𝓞 E) E)ˣ) : toFinite E (ofFinite b) = b := by
  ext : 1
  rfl

theorem absE_ofFinite (b : (FiniteAdeleRing (𝓞 E) E)ˣ) (σ : ℝ) :
    (absE F E ((toEEquiv F E).symm (ofFinite b)) : ℝ) ^ σ = (ofFinite b).finiteModule ^ σ := by
  rw [GlobalTheory.IdeleLogHom.absE_eq_ideleModule]
  have e1 : GlobalTheory.IdeleLogHom.toE F E ((toEEquiv F E).symm (ofFinite b)) = ofFinite b := toE_ofE _
  rw [e1, ideleModule_rpow_eq, toInfinite_ofFinite, toFinite_ofFinite]
  have h1 : ∀ x : InfinitePlace E, ‖((1 : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E) x‖ = 1 := fun x => by
    rw [Units.val_one]; exact norm_one
  simp only [h1, Real.one_rpow, Finset.prod_const_one, one_mul]

variable (F E) in

def archEquiv : (InfiniteAdeleRing E)ˣ ≃ₜ* idelesAt E (evI F) where
  toFun a := ⟨(toEEquiv F E).symm ((prodEquiv E).symm (a, 1)), by
    refine ((parts_iff _).1).2 ?_
    change ((toEEquiv F E ((toEEquiv F E).symm ((prodEquiv E).symm (a, 1))) : AdeleRing (𝓞 E) E)).2 = 1
    rw [ContinuousMulEquiv.apply_symm_apply]
    rfl⟩
  invFun m := (prodEquiv E (toEEquiv F E m.1)).1
  left_inv a := by simp
  right_inv m := by
    apply Subtype.ext
    have h2 : (prodEquiv E (toEEquiv F E m.1)).2 = 1 :=
      Units.ext (((parts_iff m.1).1).1 m.2)
    change (toEEquiv F E).symm ((prodEquiv E).symm ((prodEquiv E (toEEquiv F E m.1)).1, 1)) = m.1
    rw [← h2, Prod.mk.eta, ContinuousMulEquiv.symm_apply_apply, ContinuousMulEquiv.symm_apply_apply]
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, mul_one]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (toEEquiv F E).symm.continuous.comp ((prodEquiv E).symm.continuous.comp (Continuous.prodMk_left 1))
  continuous_invFun :=
    continuous_fst.comp ((prodEquiv E).continuous.comp ((toEEquiv F E).continuous.comp continuous_subtype_val))

theorem integrable_comp_archEquiv (μi : Measure (idelesAt E (evI F))) (H : idelesAt E (evI F) → ℝ)
    (hH : Integrable H μi) :
    Integrable (H ∘ archEquiv F E) (μi.map (archEquiv F E).symm) := by
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI : BorelSpace (InfiniteAdeleRing E) := ⟨rfl⟩
  haveI : BorelSpace (InfiniteAdeleRing E)ˣ := GroundTheory.Global.borelSpace_units
  let mψ := (archEquiv F E).symm.toHomeomorph.toMeasurableEquiv
  refine (integrable_map_equiv mψ (H ∘ archEquiv F E)).2 ?_
  convert hH using 1
  funext m
  change H (archEquiv F E ((archEquiv F E).symm m)) = H m
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem abs_mul_ind_le (x i A B : ℝ) (hi : |i| ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |x * i * (A * B)| ≤ |x * A| * B := by
  have h0 : 0 ≤ |x| := abs_nonneg x
  have e1 : |x * i * (A * B)| = (|x| * A * B) * |i| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (mul_nonneg hA hB)]; ring
  have e2 : |x * A| * B = (|x| * A * B) * 1 := by
    rw [abs_mul, abs_of_nonneg hA]; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hi (mul_nonneg (mul_nonneg h0 hA) hB)

theorem bound_at (g : (AE F E)ˣ → ℝ) (hinv : ∀ l, ∀ m ∈ idelesAt E (fun x : AF F => x.2), g (l * m) = g l)
    (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0) (s : ℕ) (a : (InfiniteAdeleRing E)ˣ) (b : (FiniteAdeleRing (𝓞 E) E)ˣ) :
    ‖(fun l : (AE F E)ˣ => g l * (if ∀ v : Pl F, compFin F E v (l : AE F E) ∈ locId v 𝔞 then (1 : ℝ) else 0) *
      (absE F E l : ℝ) ^ s) ((toEEquiv F E).symm ((prodEquiv E).symm (a, b)))‖ ≤
    ‖g (archEquiv F E a).1 * (absE F E (archEquiv F E a).1 : ℝ) ^ s‖ * finiteZetaBound (Units.mk0 𝔞 h𝔞) (s : ℝ) b := by
  have hΦ : (toEEquiv F E).symm ((prodEquiv E).symm (a, b)) =
      (archEquiv F E a).1 * (toEEquiv F E).symm (ofFinite b) := by
    change (toEEquiv F E).symm ((prodEquiv E).symm (a, b)) =
      (toEEquiv F E).symm ((prodEquiv E).symm (a, 1)) * (toEEquiv F E).symm ((prodEquiv E).symm (1, b))
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hlbf : (toEEquiv F E).symm (ofFinite b) ∈ idelesAt E (fun x : AF F => x.2) := by
    refine ((parts_iff _).2).2 ?_
    change ((toEEquiv F E ((toEEquiv F E).symm (ofFinite b)) : AdeleRing (𝓞 E) E)).1 = 1
    rw [ContinuousMulEquiv.apply_symm_apply]
    rfl
  have hmod := absE_ofFinite (F := F) b s
  have hb2 : (adeleTensorAlgEquivLeft F E (((toEEquiv F E).symm ((prodEquiv E).symm (a, b)) : (AE F E)ˣ) : AE F E)).2 =
      (b : FiniteAdeleRing (𝓞 E) E) := by
    change ((toEEquiv F E ((toEEquiv F E).symm ((prodEquiv E).symm (a, b))) : AdeleRing (𝓞 E) E)).2 = _
    rw [ContinuousMulEquiv.apply_symm_apply]
    rfl
  rw [hΦ] at hb2 ⊢
  generalize (archEquiv F E a).1 = la at hb2 ⊢
  generalize (toEEquiv F E).symm (ofFinite b) = lb at hb2 hlbf hmod ⊢
  simp only [Real.norm_eq_abs]
  rw [hinv la lb hlbf, map_mul, NNReal.coe_mul, mul_pow]
  have hA : 0 ≤ (absE F E la : ℝ) ^ s := by positivity
  have hB : 0 ≤ (absE F E lb : ℝ) ^ s := by positivity
  by_cases hb : (b : FiniteAdeleRing (𝓞 E) E) ∈ idealFiniteAdeles (Units.mk0 𝔞 h𝔞)
  · rw [finiteZetaBound, if_pos hb, ← hmod, Real.rpow_natCast]
    refine abs_mul_ind_le _ _ _ _ ?_ hA hB
    split_ifs <;> simp
  · have hi : ¬ ∀ v : Pl F, compFin F E v ((la * lb : (AE F E)ˣ) : AE F E) ∈ locId v 𝔞 := by
      intro h
      apply hb
      rw [← hb2]
      exact mem_idealFiniteAdeles_of_locId 𝔞 h𝔞 _ h
    rw [finiteZetaBound, if_neg hb, if_neg hi]
    simp

theorem integrable_tate : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (μ : Measure (AE F E)ˣ), μ.IsHaarMeasure →
    ∀ (μi : Measure (idelesAt E (evI F))), μi.IsHaarMeasure → ∀ (s : ℕ), 2 ≤ s →
    ∀ (g : (AE F E)ˣ → ℝ), Measurable g → (∀ l, ∀ m ∈ idelesAt E (fun x : AF F => x.2), g (l * m) = g l) →
    Integrable (fun m : idelesAt E (evI F) => g m.1 * (absE F E m.1 : ℝ) ^ s) μi →
    ∀ (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 →
    Integrable (fun l : (AE F E)ˣ => g l * (if ∀ v : Pl F, compFin F E v (l : AE F E) ∈ locId v 𝔞 then (1 : ℝ) else 0) *
      (absE F E l : ℝ) ^ s) μ := by
  intro F E _ _ _ _ _ μ hμ μi hμi s hs g hg hinv hint 𝔞 h𝔞
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI : BorelSpace (InfiniteAdeleRing E) := ⟨rfl⟩
  haveI : BorelSpace (InfiniteAdeleRing E)ˣ := GroundTheory.Global.borelSpace_units
  set L : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 𝔞 h𝔞
  set f : (AE F E)ˣ → ℝ := fun l => g l * (if ∀ v : Pl F, compFin F E v (l : AE F E) ∈ locId v 𝔞 then (1 : ℝ) else 0) *
      (absE F E l : ℝ) ^ s with hf
  have hfm : Measurable f := by
    refine (hg.mul (Measurable.ite (measurableSet_locId 𝔞 h𝔞) measurable_const measurable_const)).mul ?_
    exact ((NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).pow s).measurable

  let Φ : ((InfiniteAdeleRing E)ˣ × (FiniteAdeleRing (𝓞 E) E)ˣ) ≃ₜ* (AE F E)ˣ :=
    (prodEquiv E).symm.trans (toEEquiv F E).symm
  let ψ := archEquiv F E
  let νi : Measure (InfiniteAdeleRing E)ˣ := μi.map ψ.symm
  haveI : νi.IsHaarMeasure := ψ.symm.isHaarMeasure_map μi
  let νf := finiteIdeleMeasure E
  haveI : (μ.map Φ.symm).IsHaarMeasure := Φ.symm.isHaarMeasure_map μ
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map Φ.symm) (νi.prod νf)
  let mΦ := Φ.toHomeomorph.toMeasurableEquiv
  suffices hI : Integrable (f ∘ Φ) (νi.prod νf) by
    have h1 : Integrable (f ∘ Φ) (μ.map Φ.symm) := by
      rw [hc]; exact hI.smul_measure ENNReal.coe_ne_top
    have h2 := (integrable_map_equiv mΦ.symm (f ∘ Φ)).1 h1
    convert h2 using 1
    funext l
    simp [mΦ]

  have hσ : (1 : ℝ) < (s : ℝ) := by exact_mod_cast (show 1 < s by omega)
  have hG : Integrable (fun a => ‖g (ψ a).1 * (absE F E (ψ a).1 : ℝ) ^ s‖) νi :=
    (integrable_comp_archEquiv μi (fun m : idelesAt E (evI F) => g m.1 * (absE F E m.1 : ℝ) ^ s) hint).norm
  have hprod := hG.mul_prod (integrable_finiteZetaBound L hσ) (μ := νi) (ν := νf)
  refine hprod.mono' (hfm.comp Φ.continuous.measurable).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  exact bound_at g hinv 𝔞 h𝔞 s p.1 p.2

end GlobalTheory.TateIdelic
