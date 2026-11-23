import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.ChiWPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopChiW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlace

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace KC
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def sec_k : (InfinitePlace F → ℂ) → AE F E := (Place.exists_sec d.cm d.B.emb).choose
theorem sec_spec_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d) ∧ (∀ x w, piInf (d.B.emb w) (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x) = x w) ∧ (∀ x, finOne F • _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x = 0) ∧
    (∀ x y, _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d (x + y) = _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x + _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d y) ∧ (∀ x y, _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d (x * y) = _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x * _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d y) :=
  (Place.exists_sec d.cm d.B.emb).choose_spec
theorem uW_eq_k (w : InfinitePlace F) (z : ℂ) :
    d.uW w z = _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d (Function.update (fun _ => 1) w z) + finOne F • (1 : AE F E) := rfl
theorem sec_mul_e_k (x : InfinitePlace F → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x * (finOne F • (1 : AE F E)) = 0 := by
  rw [mul_smul_comm, mul_one, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.1]
theorem e_mul_sec_k (x : InfinitePlace F → ℂ) : (finOne F • (1 : AE F E)) * _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x = 0 := by
  rw [smul_mul_assoc, one_mul, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.1]
theorem uW_mul_k (w : InfinitePlace F) (z z' : ℂ) : d.uW w (z * z') = d.uW w z * d.uW w z' := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, update_mul, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.2.2, add_mul, mul_add, mul_add, _root_.PositivityTheory.SiegelWeilFormula.KC.sec_mul_e_k, _root_.PositivityTheory.SiegelWeilFormula.KC.e_mul_sec_k, e_mul_e]
  abel
theorem uW_one_k (w : InfinitePlace F) : d.uW w 1 = 1 := by
  apply d.ae_ext
  · intro w'
    rw [_root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, map_add, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.1, Place.piInf_finOne, map_one]
    simp [Function.update_apply]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, smul_add, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.1, smul_smul, finOne_mul_self, zero_add]
theorem uW_isUnit_k (w : InfinitePlace F) {z : ℂ} (hz : z ≠ 0) : IsUnit (d.uW w z) := by
  have h : d.uW w z * d.uW w z⁻¹ = 1 := by rw [← _root_.PositivityTheory.SiegelWeilFormula.KC.uW_mul_k, mul_inv_cancel₀ hz, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_one_k]
  exact ⟨⟨d.uW w z, d.uW w z⁻¹, h, by rw [mul_comm]; exact h⟩, rfl⟩
theorem uW_cont_k (w : InfinitePlace F) : Continuous (d.uW w) := by
  have h : Continuous fun z : ℂ => Function.update (fun _ : InfinitePlace F => (1 : ℂ)) w z :=
    continuous_const.update w continuous_id
  exact ((_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).1.comp h).add continuous_const
end KC
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_mul_pf (w : InfinitePlace F) : ∀ z z' : ℂ, z ≠ 0 → z' ≠ 0 →
    d.chiW w (z * z') = d.chiW w z * d.chiW w z' := by
  intro z z' hz hz'
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w hz
  have h2 := _root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w hz'
  have h3 := _root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w (mul_ne_zero hz hz')
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW
  rw [dif_pos h3, dif_pos h1, dif_pos h2]
  have : h3.unit = h1.unit * h2.unit := Units.ext (by simp [_root_.PositivityTheory.SiegelWeilFormula.KC.uW_mul_k])
  rw [this, map_mul, Circle.coe_mul]
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_cont_pf (w : InfinitePlace F) : ContinuousOn (d.chiW w) {z : ℂ | z ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let U : {z : ℂ // z ≠ 0} → (AE F E)ˣ := fun z => (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w z.2).unit
  have hU : Continuous U := by
    rw [Units.continuous_iff]
    constructor
    · exact (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_cont_k d w).comp continuous_subtype_val
    · have e : ∀ z : {z : ℂ // z ≠ 0}, ((U z)⁻¹ : (AE F E)ˣ).1 = d.uW w (z.1)⁻¹ := fun z =>
        Units.inv_eq_of_mul_eq_one_right (by
          show d.uW w z.1 * d.uW w (z.1)⁻¹ = 1
          rw [← _root_.PositivityTheory.SiegelWeilFormula.KC.uW_mul_k, mul_inv_cancel₀ z.2, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_one_k])
      simp only [e]
      exact (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_cont_k d w).comp (continuous_subtype_val.inv₀ fun z => z.2)
  have e : Set.domRestrict {z : ℂ | z ≠ 0} (d.chiW w) = fun z => ((d.χ (U z) : Circle) : ℂ) := by
    funext z
    rw [Set.domRestrict_apply]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW
    rw [dif_pos (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w z.2)]
  rw [e]
  exact continuous_subtype_val.comp (d.ok.hecke.1.comp hU)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_pos_pf (w : InfinitePlace F) : ∀ r : ℝ, 0 < r → d.chiW w (r : ℂ) = 1 := by
  intro r hr
  set t := Real.sqrt r with ht
  have ht0 : (t : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.mpr hr).ne'
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc : cA σ (d.uW w t) = d.uW w t := by
    apply d.ae_ext
    · intro w'
      rw [Place.piInf_cA d.cm, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, map_add, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.1, Place.piInf_finOne, add_zero]
      by_cases h : w' = w
      · subst h; simp
      · simp [Function.update_apply, h]
    · rw [← map_smul, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, smul_add, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.1, zero_add, smul_smul, KC.finOne_mul_self, map_smul,
        map_one]
  have huw : d.uW w (r : ℂ) = d.uW w t * cA σ (d.uW w t) := by
    rw [hc, ← _root_.PositivityTheory.SiegelWeilFormula.KC.uW_mul_k, ← Complex.ofReal_mul, ht, Real.mul_self_sqrt hr.le]
  obtain ⟨ξ, hξ⟩ := GlobalTheory.SplitIdele.exists_isQuad d.cm
  have hn := hξ.algebraMap_norm (d.uW w t)
  let u := (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w ht0).unit
  let a : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) u
  have ha : Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) a = (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w hr0).unit :=
    Units.ext (by
      show algebraMap (AF F) (AE F E) (Algebra.norm (AF F) (d.uW w t)) = d.uW w (r : ℂ)
      rw [hn, huw])
  have hres := d.ok.res a
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨u, rfl⟩))] at hres
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW
  rw [dif_pos (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w hr0), ← ha]
  exact hres
end SD
end PositivityTheory.SiegelWeilFormula
end
end
