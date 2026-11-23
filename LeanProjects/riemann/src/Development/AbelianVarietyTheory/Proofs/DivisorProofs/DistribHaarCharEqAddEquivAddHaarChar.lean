import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleNormalizedAbsEqAdelicAbsNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ModuNorm

open scoped Pointwise

def mulUnitCE {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a : Rˣ) : R ≃ₜ+ R where
  toFun x := (a : R) * x
  invFun x := ((a⁻¹ : Rˣ) : R) * x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  map_add' x y := mul_add _ x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem distribHaarChar_eq_addEquivAddHaarChar {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R] (a : Rˣ) :
    distribHaarChar R a = addEquivAddHaarChar (mulUnitCE a) := by
  let μ : Measure R := Measure.addHaar
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : R)
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hKn).ne'
  have hT : μ K ≠ ⊤ := hK.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) h0 hT ?_
  have e := addEquivAddHaarChar_smul_preimage μ (X := a • K) (mulUnitCE a)
  have hpre : (mulUnitCE a : R → R) ⁻¹' (a • K) = K := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := (Units.mul_right_inj a).1 hxy
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hpre] at e
  rw [← e]
  rfl

def evalUnitCE (R : Type) [AddCommGroup R] [TopologicalSpace R] : (Unit → R) ≃ₜ+ R where
  toFun f := f ()
  invFun x := fun _ => x
  left_inv f := rfl
  right_inv x := rfl
  map_add' f g := rfl
  continuous_toFun := continuous_apply ()
  continuous_invFun := continuous_pi fun _ => continuous_id

theorem modu_norm_eq_absE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], NumberField.IsTotallyReal F →
    ∀ t : (AE F E)ˣ, (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t) : ℝ≥0) : ℝ) = (absE F E t : ℝ) := by
  intro F E _ _ _ _ _ hF t
  haveI := hF
  letI : MeasurableSpace (AF F) := borel _
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  set a : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) t with ha
  let M : Matrix Unit Unit (AF F) := fun _ _ => (a : AF F)
  have hdet : M.det = (a : AF F) := Matrix.det_unique M
  have hM : IsUnit M.det := hdet ▸ a.isUnit
  have hχ := GlobalTheory.ModuLR.chi_AF F M hM
  have htr := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (evalUnitCE (AF F)) (GlobalTheory.ModuLR.mulVecCE M hM)
  have hext : ((evalUnitCE (AF F)).symm.trans (GlobalTheory.ModuLR.mulVecCE M hM)).trans (evalUnitCE (AF F)) = mulUnitCE a := by
    ext x
    show (M *ᵥ fun _ => x) () = (a : AF F) * x
    simp [Matrix.mulVec, dotProduct, M]
  rw [hext] at htr
  show ((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) = _
  rw [show distribHaarChar (AdeleRing (𝓞 F) F) a = distribHaarChar (AF F) a from rfl,
    distribHaarChar_eq_addEquivAddHaarChar, htr, hχ, hdet]
  exact GlobalTheory.absE_eq_prod_norm_fstA_sndA F E t

end GlobalTheory.ModuNorm
