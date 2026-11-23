import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Topology

noncomputable section
namespace GlobalTheory.ColFourier

section Curry
variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)] {Y : (i : ι) → κ i → Type*}
  [∀ i j, MeasurableSpace (Y i j)]

theorem measurePreserving_piCurry (μ : ∀ i j, Measure (Y i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry Y) (Measure.pi fun p : (i : ι) × κ i => μ p.1 p.2)
      (Measure.pi fun i => Measure.pi fun j => μ i j) := by
  refine ⟨(MeasurableEquiv.piCurry Y).measurable, ?_⟩
  symm
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.univ.pi '' Set.univ.pi fun j => {s : Set (Y i j) | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi fun j => (μ i j).toFiniteSpanningSetsIn) fun s hs => ?_
  choose S hS hSs using hs
  have hpre : (MeasurableEquiv.piCurry Y) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun p : (i : ι) × κ i => S p.1 p.2 := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi, ← hSs, MeasurableEquiv.piCurry_apply, Sigma.forall]
    rfl
  rw [Measure.map_apply (MeasurableEquiv.piCurry Y).measurable (MeasurableSet.univ_pi fun i => by
      rw [← hSs i]; exact MeasurableSet.univ_pi fun j => hS i j (Set.mem_univ j)), hpre, Measure.pi_pi,
    Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hSs i, Measure.pi_pi]

end Curry

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A C : Type*} [Fintype A] [DecidableEq C]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in

def restrictCols (P : Finset C) (X : Matrix A C k) : Matrix A P k := Matrix.of fun i j => X i j

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
@[simp] theorem restrictCols_setCols (P : Finset C) (Y : Matrix A C k) (U : Matrix A P k) :
    restrictCols P (setCols P Y U) = U := by
  ext i j; simp [restrictCols, setCols, j.2]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
@[simp] theorem setCols_restrictCols (P : Finset C) (Y : Matrix A C k) : setCols P Y (restrictCols P Y) = Y := by
  ext i j; by_cases h : j ∈ P <;> simp [restrictCols, setCols, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
@[simp] theorem setCols_setCols (P : Finset C) (Y : Matrix A C k) (U V : Matrix A P k) :
    setCols P (setCols P Y U) V = setCols P Y V := by
  ext i j; by_cases h : j ∈ P <;> simp [setCols, h]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_restrictCols (P : Finset C) : Continuous (restrictCols (k := k) (A := A) P) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (j : C)).comp (continuous_apply i)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_setCols (P : Finset C) (Y : Matrix A C k) : Continuous (setCols P Y) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : j ∈ P
  · simp only [setCols, of_apply, dif_pos h]
    exact (continuous_apply (⟨j, h⟩ : P)).comp (continuous_apply i)
  · simp only [setCols, of_apply, dif_neg h]
    exact continuous_const

theorem comp_setCols_mem_SB {Ξ : Matrix A C k → ℂ} (hΞ : Ξ ∈ SB (Matrix A C k)) (P : Finset C)
    (Y : Matrix A C k) : (fun U => Ξ (setCols P Y U)) ∈ SB (Matrix A P k) := by
  haveI := t2Space k
  refine ⟨hΞ.1.comp_continuous (continuous_setCols P Y),
    HasCompactSupport.intro (hΞ.2.image (continuous_restrictCols P)) fun U hU => ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h => hU ⟨_, h, restrictCols_setCols P Y U⟩

theorem pairCols_eq_dotProduct (P : Finset C) (Y : Matrix A C k) (U : Matrix A P k) :
    pairCols P Y U = (fun p : (_ : A) × P => U p.1 p.2) ⬝ᵥ (fun p : (_ : A) × P => Y p.1 p.2) := by
  simp only [pairCols, dotProduct, Fintype.sum_sigma]

variable [MeasurableSpace k] [BorelSpace k]

omit [DecidableEq C] in

theorem isAddHaarMeasure_volM (m : Measure k) [m.IsAddHaarMeasure] (B : Type*) [Fintype B] :
    (volM m A B).IsAddHaarMeasure := by
  haveI := secondCountable k; haveI := t2Space k
  haveI : (Measure.pi fun _ : B => m).IsAddHaarMeasure := inferInstance
  exact Measure.pi.isAddHaarMeasure (fun _ : A => (Measure.pi fun _ : B => m))

omit [DecidableEq C] in

theorem integral_volM (m : Measure k) [SigmaFinite m] (B : Type*) [Fintype B] (f : Matrix A B k → ℂ) :
    ∫ U, f U ∂(volM m A B) =
      ∫ x : (_ : A) × B → k, f (Matrix.of fun i j => x ⟨i, j⟩) ∂(Measure.pi fun _ => m) := by
  have h := measurePreserving_piCurry (Y := fun (_ : A) (_ : B) => k) (fun _ _ => m)
  exact (h.integral_comp' (g := f)).symm

theorem fourierInt_eq_pi (ψ : AddChar k Circle) (m : Measure k) [SigmaFinite m] (P : Finset C)
    (Φ : Matrix A C k → ℂ) (Y : Matrix A C k) :
    fourierInt ψ m P Φ Y = ∫ x : (_ : A) × P → k, Φ (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩)) *
      (ψ (x ⬝ᵥ fun p => Y p.1 p.2) : ℂ) ∂(Measure.pi fun _ => m) := by
  rw [fourierInt, integral_volM]
  congr 1
  funext x
  rw [pairCols_eq_dotProduct]
  rfl

end GlobalTheory.ColFourier

namespace GlobalTheory.ColFourier
variable {k : Type*} [Field k] [ValuativeRel k]

theorem hasConductor_inv {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) : HasConductor ψ⁻¹ c := fun x => by
  simpa only [AddChar.inv_apply', inv_eq_one] using h x

end GlobalTheory.ColFourier
