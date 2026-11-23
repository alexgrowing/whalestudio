import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsArchUnimodular
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramAtData
import GroundTheory.HeightsAndTheta.Theta.RealSignature
import GroundTheory.HeightsAndTheta.Theta.Unimodular.IndefiniteUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic GroundTheory.Heights₂.Theta Module Matrix MeasureTheory
open scoped NNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ArchUnimodular

abbrev sigP (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) : ℕ :=
  posEigenCount (GramAtData.proof h v w).1

abbrev sigQ (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) : ℕ :=
  negEigenCount (GramAtData.proof h v w).1

def placeEquiv (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) :
    unitaryGroupMatrix (starRingEnd ℂ) (gramAt h v w) ≃ₜ*
      indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
  unitaryHermitianEquiv (hH := (GramAtData.proof h v w).1) (GramAtData.proof h v w).2

def fromPi (h : HermitianForm F E W) (v : Basis ι E W) :
    (∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w)) →*
      archUnitary h v where
  toFun f := ⟨fun w => ((placeEquiv h v w).symm (f w) : GL ι ℂ),
    (Subgroup.mem_pi _).2 fun w _ => ((placeEquiv h v w).symm (f w)).2⟩
  map_one' := by
    apply Subtype.ext
    funext w
    simp
  map_mul' f g := by
    apply Subtype.ext
    funext w
    simp

theorem continuous_fromPi (h : HermitianForm F E W) (v : Basis ι E W) :
    Continuous (fromPi h v) :=
  Continuous.subtype_mk (continuous_pi fun w => continuous_subtype_val.comp
    ((placeEquiv h v w).symm.continuous.comp (continuous_apply w))) _

theorem mulEquivHaarChar_conjCME_eq_one_of_reflect {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {t j : G} (hjj : j * j = 1) (hjt : j * t * j = t⁻¹) : mulEquivHaarChar (conjCME t) = 1 := by
  have hJ : mulEquivHaarChar (conjCME j) * mulEquivHaarChar (conjCME j) = 1 := by
    rw [← mulEquivHaarChar_conjCME_mul, hjj, conjCME_one, mulEquivHaarChar_refl]
  have h1 : mulEquivHaarChar (conjCME t⁻¹) = mulEquivHaarChar (conjCME t) := by
    rw [← hjt, mulEquivHaarChar_conjCME_mul, mulEquivHaarChar_conjCME_mul]
    calc mulEquivHaarChar (conjCME j) * mulEquivHaarChar (conjCME t) *
          mulEquivHaarChar (conjCME j)
        = mulEquivHaarChar (conjCME t) *
            (mulEquivHaarChar (conjCME j) * mulEquivHaarChar (conjCME j)) := by ring
      _ = mulEquivHaarChar (conjCME t) := by rw [hJ, mul_one]
  have h2 := mulEquivHaarChar_conjCME_inv t
  rw [h1] at h2
  have h3 : ((mulEquivHaarChar (conjCME t) : ℝ≥0) : ℝ) * (mulEquivHaarChar (conjCME t) : ℝ) = 1 := by
    exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (mulEquivHaarChar (conjCME t) : ℝ) := NNReal.coe_nonneg _
  have h5 : ((mulEquivHaarChar (conjCME t) : ℝ≥0) : ℝ) = 1 := by nlinarith
  exact_mod_cast h5

theorem mulEquivHaarChar_conjCME_archUnitary (h : HermitianForm F E W) (v : Basis ι E W)
    (g : archUnitary h v) : mulEquivHaarChar (conjCME g) = 1 := by
  let f : ∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
    fun w => placeEquiv h v w ⟨g.1 w, (Subgroup.mem_pi _).1 g.2 w trivial⟩
  have hg : fromPi h v f = g := by
    apply Subtype.ext
    funext w
    simp [fromPi, f]
  let ks := fun w => cartanHomeomorph.symm (f w)
  let k : ∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
    fun w => ((ks w).1 : indefiniteUnitaryGroup _ _)
  let s : ∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
    fun w => upqOfMatrix (ks w).2.1 (ks w).2.2.2
  let Jm : ∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
    fun w => indefJElem _ _
  have hfks : f = k * s := funext fun w => (cartanHomeomorph.apply_symm_apply (f w)).symm
  have eJ : Jm * Jm = 1 := funext fun w => indefJElem_mul_self
  have eS : Jm * s * Jm = s⁻¹ := funext fun w => indefJElem_mul_mul_indefJElem (ks w).2
  let K : Subgroup (archUnitary h v) :=
    (Subgroup.pi Set.univ fun w : InfinitePlace E =>
      maxCompact (indefiniteUnitaryGroup (sigP h v w) (sigQ h v w))).map (fromPi h v)
  have hK : IsCompact (K : Set (archUnitary h v)) := by
    rw [Subgroup.coe_map, Subgroup.coe_pi]
    exact (isCompact_univ_pi fun w => isCompact_maxCompact_indefiniteUnitary).image
      (continuous_fromPi h v)
  have hk : fromPi h v k ∈ K :=
    Subgroup.mem_map_of_mem _ ((Subgroup.mem_pi _).2 fun w _ => (ks w).1.2)
  have hjj : fromPi h v Jm * fromPi h v Jm = 1 := by rw [← map_mul, eJ, map_one]
  have hjt : fromPi h v Jm * fromPi h v s * fromPi h v Jm = (fromPi h v s)⁻¹ := by
    rw [← map_mul, ← map_mul, eS, map_inv]
  rw [← hg, hfks, map_mul, mulEquivHaarChar_conjCME_mul, mulEquivHaarChar_conjCME_eq_one hK hk,
    one_mul]
  exact mulEquivHaarChar_conjCME_eq_one_of_reflect hjj hjt

end ArchUnimodular

theorem ArchUnimodular.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchUnimodular.Statement h v := by
  intro μ _
  refine ⟨fun g => ?_⟩
  have hc : μ.map (conjCME g⁻¹) = μ := by
    have e := mulEquivHaarChar_smul_map μ (conjCME g⁻¹)
    rwa [ArchUnimodular.mulEquivHaarChar_conjCME_archUnitary, one_smul] at e
  have hfun : (fun x => x * g) = (fun x => g * x) ∘ (conjCME g⁻¹) := by
    funext x
    simp [mul_assoc]
  have hm : Measurable (conjCME g⁻¹) := (map_continuous (conjCME g⁻¹)).measurable
  rw [hfun, ← Measure.map_map (measurable_const_mul g) hm, hc, map_mul_left_eq_self]

section Example

open GaussianPlane

example : muG.IsMulRightInvariant := ArchUnimodular.proof hG vG muG

end Example

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
