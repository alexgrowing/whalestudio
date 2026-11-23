import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace MatrixSubsetMeasurability

variable {k r : ℕ} {U : Set (Mat k r)}

def SG (_hU : IsClosedSubgroup U) : Type := {x : Mt k r // (Matrix.of x : Mat k r) ∈ U}

def mat {hU : IsClosedSubgroup U} (g : SG hU) : Mat k r := Matrix.of g.1

theorem mat_mem {hU : IsClosedSubgroup U} (g : SG hU) : mat g ∈ U := by
  exact g.2

def mk (hU : IsClosedSubgroup U) (A : Mat k r) (hA : A ∈ U) : SG hU := ⟨Matrix.of.symm A, hA⟩

theorem mat_mk (hU : IsClosedSubgroup U) (A : Mat k r) (hA : A ∈ U) : mat (mk hU A hA) = A := rfl

variable {hU : IsClosedSubgroup U}

instance : One (SG hU) := ⟨mk hU 1 hU.one_mem⟩
instance : Mul (SG hU) := ⟨fun a b => mk hU (mat a * mat b) (hU.mul_mem _ a.2 _ b.2)⟩
instance : Inv (SG hU) := ⟨fun a => mk hU (mat a)⁻¹ (hU.inv_mem _ a.2)⟩

theorem mat_one : mat (1 : SG hU) = 1 := rfl
theorem mat_mul (a b : SG hU) : mat (a * b) = mat a * mat b := rfl
theorem mat_inv (a : SG hU) : mat a⁻¹ = (mat a)⁻¹ := rfl

theorem ext' {a b : SG hU} (h : mat a = mat b) : a = b := by
  exact Subtype.ext (Matrix.of.injective h)

instance : Group (SG hU) :=
  Group.ofLeftAxioms (fun a b c => ext' (Matrix.mul_assoc (mat a) (mat b) (mat c)))
    (fun a => ext' (Matrix.one_mul (mat a)))
    (fun a => ext' (Matrix.nonsing_inv_mul (mat a) (hU.unit _ a.2)))

instance : TopologicalSpace (SG hU) := instTopologicalSpaceSubtype
instance : MeasurableSpace (SG hU) := Subtype.instMeasurableSpace
instance : BorelSpace (SG hU) :=
  inferInstanceAs (BorelSpace ({x : Mt k r | (Matrix.of x : Mat k r) ∈ U} : Set (Mt k r)))

private theorem continuous_matrix_of_Mt : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) :=
  continuous_matrix (fun i j => (continuous_apply j).comp (continuous_apply i))

theorem continuous_val : Continuous (fun g : SG hU => g.1) := by
  exact continuous_subtype_val

theorem continuous_mat : Continuous (fun g : SG hU => mat g) := by
  exact continuous_matrix_of_Mt.comp continuous_subtype_val

instance : ContinuousMul (SG hU) := by
  refine ⟨Continuous.subtype_mk ?_ _⟩
  exact (continuous_mat.comp continuous_fst).matrix_mul (continuous_mat.comp continuous_snd)

instance : ContinuousInv (SG hU) := by
  refine ⟨Continuous.subtype_mk ?_ _⟩
  have h : (fun a : SG hU => (mat a)⁻¹) = fun a => (mat a).det⁻¹ • (mat a).adjugate := by
    funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv]
  show Continuous fun a : SG hU => (mat a)⁻¹
  rw [h]
  exact ((continuous_mat.matrix_det).inv₀ fun a => (hU.unit _ a.2).ne_zero).smul continuous_mat.matrix_adjugate

instance : IsTopologicalGroup (SG hU) := {}

theorem measurableSet_U (hU : IsClosedSubgroup U) : MeasurableSet {x : Mt k r | (Matrix.of x : Mat k r) ∈ U} := by
  exact (hU.closed.preimage continuous_matrix_of_Mt).measurableSet

theorem me_val (hU : IsClosedSubgroup U) : MeasurableEmbedding (fun g : SG hU => g.1) := by
  exact MeasurableEmbedding.subtype_coe (measurableSet_U hU)

def nu (hU : IsClosedSubgroup U) (μ : Measure (Mt k r)) : Measure (SG hU) := μ.comap (fun g : SG hU => g.1)

theorem map_nu {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ) : (nu hU μ).map (fun g : SG hU => g.1) = μ := by
  unfold nu
  rw [(me_val hU).map_comap]
  first | rw [Subtype.range_coe_subtype] | rw [Subtype.range_val_subtype] | skip
  have hae : ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := ae_iff.mpr hμ.conc
  exact Measure.restrict_eq_self_of_ae_mem (hae.mono fun x hx => ⟨⟨x, hx⟩, rfl⟩)

theorem nu_left {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ) : (nu hU μ).IsMulLeftInvariant := by
  constructor
  intro g
  have hc : Continuous (lmulM (k := k) (r := r) (mat g)) :=
    (continuous_const.mul continuous_matrix_of_Mt : Continuous fun x : Mt k r => (mat g * Matrix.of x : Mat k r))
  have hm : Measurable (fun x : SG hU => g * x) := by
    refine Measurable.subtype_mk ?_
    exact hc.measurable.comp measurable_subtype_coe
  have hval : (fun g : SG hU => g.1) ∘ (fun x : SG hU => g * x) = lmulM (mat g) ∘ (fun g : SG hU => g.1) := rfl
  have hmap : ((nu hU μ).map (fun x : SG hU => g * x)).map (fun g : SG hU => g.1)
      = (nu hU μ).map (fun g : SG hU => g.1) := by
    rw [Measure.map_map (me_val hU).measurable hm, hval,
      ← Measure.map_map hc.measurable (me_val hU).measurable, map_nu hμ, hμ.left _ (mat_mem g)]
  ext s hs
  have h1 := congrArg (fun m : Measure (Mt k r) => m ((fun g : SG hU => g.1) '' s)) hmap
  rwa [(me_val hU).map_apply, (me_val hU).map_apply,
    Set.preimage_image_eq s (me_val hU).injective] at h1

theorem nu_inv (HI : HaarInv) {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ) : (nu hU μ).IsInvInvariant := by
  have hae : AEMeasurable invM μ := by
    by_contra h
    exact hμ.ne_zero (by rw [← HI k r U μ hU hμ, Measure.map_of_not_aemeasurable h])
  constructor
  ext s hs
  have hset : (fun g : SG hU => g.1) '' s⁻¹ = invM ⁻¹' ((fun g : SG hU => g.1) '' s) ∩
      {x : Mt k r | (Matrix.of x : Mat k r) ∈ U} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(@id (SG hU) x)⁻¹, hx, rfl⟩, x.2⟩
    · rintro ⟨⟨x, hx, hxy⟩, hy⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      have e : (@id (SG hU) ⟨y, hy⟩)⁻¹ = x := by
        apply ext'
        rw [mat_inv]
        show (Matrix.of y : Mat k r)⁻¹ = Matrix.of x.1
        rw [show x.1 = invM y from hxy]
        all_goals rfl
      show (@id (SG hU) ⟨y, hy⟩)⁻¹ ∈ s
      rw [e]
      exact hx
  rw [Measure.inv_apply]
  simp only [nu]
  rw [(me_val hU).comap_apply, (me_val hU).comap_apply, hset,
    measure_inter_conull (t := {x : Mt k r | (Matrix.of x : Mat k r) ∈ U}) hμ.conc,
    ← Measure.map_apply_of_aemeasurable hae ((me_val hU).measurableSet_image.mpr hs), HI k r U μ hU hμ]

end MatrixSubsetMeasurability

end ReciprocityTheory.ChartRestriction.DS.Mult1
