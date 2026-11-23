import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.SsetGroup

open MeasureTheory Matrix Topology
open scoped ENNReal NNReal

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW

open PI

variable {m : ℕ}

def MG (G : Set (Matrix (Fin m) (Fin m) ℂ)) (_hG : IsMatGroup G) : Type :=
  {x : MtM m // Matrix.of x ∈ G}

variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}

namespace MG

def toM (x : MG G hG) : Matrix (Fin m) (Fin m) ℂ := Matrix.of x.1

def val (x : MG G hG) : MtM m := x.1

theorem toM_mem (x : MG G hG) : x.toM ∈ G := x.2

def mk (hG : IsMatGroup G) (g : Matrix (Fin m) (Fin m) ℂ) (h : g ∈ G) : MG G hG :=
  ⟨Matrix.of.symm g, by simpa using h⟩

@[simp] theorem toM_mk (g : Matrix (Fin m) (Fin m) ℂ) (h : g ∈ G) : (mk hG g h).toM = g := by
  simp [mk, toM]

theorem toM_injective : Function.Injective (toM : MG G hG → Matrix (Fin m) (Fin m) ℂ) := by
  intro x y h
  exact Subtype.ext (Matrix.of.injective h)

@[ext] theorem ext {x y : MG G hG} (h : x.toM = y.toM) : x = y := toM_injective h

@[simp] theorem mk_toM (x : MG G hG) : mk hG x.toM x.toM_mem = x := toM_injective (toM_mk _ _)

instance : Mul (MG G hG) := ⟨fun x y => mk hG (x.toM * y.toM) (hG.2.2.1 _ x.2 _ y.2)⟩
instance : One (MG G hG) := ⟨mk hG 1 hG.2.1⟩
instance : Inv (MG G hG) := ⟨fun x => mk hG (x.toM)⁻¹ (hG.2.2.2 _ x.2).1⟩

@[simp] theorem toM_mul (x y : MG G hG) : (x * y).toM = x.toM * y.toM := toM_mk _ _
@[simp] theorem toM_one : (1 : MG G hG).toM = 1 := toM_mk _ _
@[simp] theorem toM_inv (x : MG G hG) : x⁻¹.toM = (x.toM)⁻¹ := toM_mk _ _

theorem mul_inv_toM (x : MG G hG) : x.toM * (x.toM)⁻¹ = 1 := (hG.2.2.2 _ x.toM_mem).2

theorem det_ne_zero (x : MG G hG) : x.toM.det ≠ 0 := by
  intro h
  have e := congrArg Matrix.det (mul_inv_toM x)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at e
  exact zero_ne_one e

theorem inv_mul_toM (x : MG G hG) : (x.toM)⁻¹ * x.toM = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (det_ne_zero x))

instance : Group (MG G hG) where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc a b c := ext (by simp [Matrix.mul_assoc])
  one_mul a := ext (by simp)
  mul_one a := ext (by simp)
  inv_mul_cancel a := ext (by simp [inv_mul_toM])

@[simp] theorem toM_mul' (x y : MG G hG) : (x * y).toM = x.toM * y.toM := toM_mul x y

theorem val_mul (x y : MG G hG) : (x * y).val = lmulQ x.toM y.val := rfl

theorem val_mul' (x y : MG G hG) : (x * y).val = rmulQ y.toM x.val := rfl

end MG

open MG

theorem isClosed_set (hG : IsMatGroup G) : IsClosed {x : MtM m | Matrix.of x ∈ G} :=
  hG.1.preimage continuous_id

theorem measurableSet_set (hG : IsMatGroup G) : MeasurableSet {x : MtM m | Matrix.of x ∈ G} :=
  (isClosed_set hG).measurableSet

instance : TopologicalSpace (MG G hG) :=
  inferInstanceAs (TopologicalSpace {x : MtM m // Matrix.of x ∈ G})
instance : T2Space (MG G hG) := inferInstanceAs (T2Space {x : MtM m // Matrix.of x ∈ G})
instance : SecondCountableTopology (MG G hG) :=
  inferInstanceAs (SecondCountableTopology {x : MtM m // Matrix.of x ∈ G})
instance : LocallyCompactSpace (MG G hG) :=
  (isClosed_set hG).locallyCompactSpace
instance : MeasurableSpace (MG G hG) :=
  inferInstanceAs (MeasurableSpace {x : MtM m // Matrix.of x ∈ G})
instance : BorelSpace (MG G hG) := inferInstanceAs (BorelSpace {x : MtM m // Matrix.of x ∈ G})

theorem continuous_val : Continuous (val : MG G hG → MtM m) := continuous_subtype_val

theorem continuous_toM : Continuous (toM : MG G hG → Matrix (Fin m) (Fin m) ℂ) := continuous_subtype_val

theorem continuous_iff_toM {X : Type*} [TopologicalSpace X] {f : X → MG G hG} :
    Continuous f ↔ Continuous (fun x => (f x).toM) :=
  ⟨fun h => continuous_toM.comp h, fun h => continuous_induced_rng.2 h⟩

instance : IsTopologicalGroup (MG G hG) where
  continuous_mul := by
    rw [continuous_iff_toM]
    simp only [toM_mul']
    exact (continuous_toM.comp continuous_fst).matrix_mul (continuous_toM.comp continuous_snd)
  continuous_inv := by
    rw [continuous_iff_toM]
    simp only [toM_inv]
    refine continuous_iff_continuousAt.2 fun x => ?_
    refine (continuousAt_matrix_inv _ ?_).comp continuous_toM.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (det_ne_zero x)

theorem isClosedEmbedding_val : IsClosedEmbedding (val : MG G hG → MtM m) :=
  (isClosed_set hG).isClosedEmbedding_subtypeVal

theorem measEmb : MeasurableEmbedding (val : MG G hG → MtM m) :=
  MeasurableEmbedding.subtype_coe (measurableSet_set hG)

theorem continuous_lmulQ (a : Matrix (Fin m) (Fin m) ℂ) : Continuous (lmulQ (m := m) a) := by
  unfold lmulQ
  exact continuous_const.matrix_mul continuous_id

theorem continuous_rmulQ (a : Matrix (Fin m) (Fin m) ℂ) : Continuous (rmulQ (m := m) a) := by
  unfold rmulQ
  exact continuous_id.matrix_mul continuous_const

def onG (hG : IsMatGroup G) (μ : Measure (MtM m)) : Measure (MG G hG) := μ.comap val

theorem map_onG (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) : (onG hG μ).map val = μ := by
  rw [onG, measEmb.map_comap]
  have hr : Set.range (val : MG G hG → MtM m) = {x | Matrix.of x ∈ G} := Subtype.range_coe
  rw [hr]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  simpa using hμ.2.2.1

theorem onG_left (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) : Measure.IsMulLeftInvariant (onG hG μ) := by
  refine ⟨fun g => ?_⟩
  have hcomp : (val ∘ (fun x : MG G hG => g * x)) = lmulQ g.toM ∘ val := funext fun x => rfl
  have hmeasL : Measurable (lmulQ (m := m) g.toM) := (continuous_lmulQ _).measurable
  have hmul : Measurable (fun x : MG G hG => g * x) :=
    (measEmb (hG := hG)).measurable_comp_iff.1 (by rw [hcomp]; exact hmeasL.comp measEmb.measurable)
  calc Measure.map (fun x => g * x) (onG hG μ)
      = Measure.comap val (Measure.map val (Measure.map (fun x => g * x) (onG hG μ))) :=
        (measEmb.comap_map _).symm
    _ = Measure.comap val (Measure.map (lmulQ g.toM) (Measure.map val (onG hG μ))) := by
        rw [Measure.map_map measEmb.measurable hmul, hcomp, ← Measure.map_map hmeasL measEmb.measurable]
    _ = Measure.comap val μ := by rw [map_onG μ hμ, hμ.2.2.2 _ g.toM_mem]
    _ = onG hG μ := rfl

theorem onG_sigmaFinite (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) : SigmaFinite (onG hG μ) := by
  haveI := hμ.1
  exact SigmaFinite.of_map _ (measEmb (hG := hG)).measurable.aemeasurable (by rw [map_onG μ hμ]; exact hμ.1)

theorem onG_ne_zero (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) : onG hG μ ≠ 0 := by
  intro h
  have e := map_onG (hG := hG) μ hμ
  rw [h, Measure.map_zero] at e
  exact hμ.2.1 e.symm

end PI.QuotSetU.UnitaryGroupMassFormula.ModW
