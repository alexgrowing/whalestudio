import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SimplexCompact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.PosDefOfSphere
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SmoothCompositionIdentity.ContDiffAtComp

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL Topology Filter
open scoped ContDiff

namespace PositivityTheory.KB.TwAG

open BlockInvariants

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

def bf (a b Y : HS L N) : HS L N :=
  mkHS (fun w => (2 : ℝ)⁻¹ • (mat a w * mat Y w * mat b w + mat b w * mat Y w * mat a w)) fun w => by
    simp only [IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_mul, (mat_herm a w).eq, (mat_herm b w).eq,
      (mat_herm Y w).eq, star_trivial, mul_assoc, add_comm]

theorem mat_bf (a b Y : HS L N) (w : InfinitePlace L) :
    mat (bf a b Y) w = (2 : ℝ)⁻¹ • (mat a w * mat Y w * mat b w + mat b w * mat Y w * mat a w) := rfl

def bl (a b : HS L N) : HS L N →ₗ[ℝ] HS L N where
  toFun := bf a b
  map_add' Y Z := HS_ext fun w => by simp only [mat_bf, mat_add, Matrix.mul_add, Matrix.add_mul]; module
  map_smul' c Y := HS_ext fun w => by
    simp only [mat_bf, mat_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]; module

theorem mat_bl (a b Y : HS L N) (w : InfinitePlace L) :
    mat (bl a b Y) w = (2 : ℝ)⁻¹ • (mat a w * mat Y w * mat b w + mat b w * mat Y w * mat a w) := rfl

def b3 : HS L N →ₗ[ℝ] HS L N →ₗ[ℝ] HS L N →ₗ[ℝ] HS L N :=
  LinearMap.mk₂ ℝ bl
    (fun a a' b => LinearMap.ext fun Y => HS_ext fun w => by
      simp only [LinearMap.add_apply, mat_bl, mat_add, Matrix.mul_add, Matrix.add_mul]; module)
    (fun c a b => LinearMap.ext fun Y => HS_ext fun w => by
      simp only [LinearMap.smul_apply, mat_bl, mat_smul, Matrix.mul_smul, Matrix.smul_mul]; module)
    (fun a b b' => LinearMap.ext fun Y => HS_ext fun w => by
      simp only [LinearMap.add_apply, mat_bl, mat_add, Matrix.mul_add, Matrix.add_mul]; module)
    (fun c a b => LinearMap.ext fun Y => HS_ext fun w => by
      simp only [LinearMap.smul_apply, mat_bl, mat_smul, Matrix.mul_smul, Matrix.smul_mul]; module)

theorem mat_one (w : InfinitePlace L) : mat (one L N).1 w = 1 := rfl

open ComplexOrder in
theorem at_one {q : ℕ} (o : Form (HS L N) q) (ho : ∀ g, FInv o g) :
    ContDiffAt ℝ ∞ o (one L N).1 ∧ extDeriv o (one L N).1 = 0 := by
  obtain ⟨B, hB⟩ := exists_clm (b3 (L := L) (N := N))
  have hm : ∀ a b Y w, mat (B a b Y) w = (2 : ℝ)⁻¹ • (mat a w * mat Y w * mat b w + mat b w * mat Y w * mat a w) :=
    fun a b Y w => by rw [hB]; rfl
  refine core B _ ?_ (fun x y => HS_ext fun w => ?_) (fun y => HS_ext fun w => ?_) o ?_
  · refine ContinuousLinearMap.ext fun Y => HS_ext fun w => ?_
    rw [hm, mat_one, Matrix.mul_one, Matrix.one_mul]
    change _ = mat Y w
    module
  · simp only [mat_add, hm, mat_one, Matrix.mul_one, Matrix.one_mul]; module
  · simp only [mat_add, mat_smul, hm, mat_one, Matrix.mul_one, Matrix.one_mul]; module
  · filter_upwards [(PositivityTheory.KB.WhittakerCocycle.pos_open_convex L N).1.mem_nhds (one L N).2] with x hx
    let g : Gp L N := fun w => (hx w).isUnit.unit⁻¹
    have e : B x x = actL g := ContinuousLinearMap.ext fun Y => HS_ext fun w => by
      have h1 : (((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = mat x w := by
        simp only [g, inv_inv]; exact IsUnit.unit_spec _
      rw [hm, mat_actL, h1, (mat_herm x w).eq]
      module
    rw [e]
    exact ho g _ (one L N).2

theorem aGood : BlockInvariants.AGood := by
  intro hS L _ _ N q o ho
  have hop := (PositivityTheory.KB.WhittakerCocycle.pos_open_convex L N).1
  have key : ∀ h ∈ Pos L N, ContDiffAt ℝ ∞ o h ∧ extDeriv o h = 0 := fun h hh => by
    obtain ⟨g, hg⟩ := trans_pos hh
    have h1 := at_one o ho
    rw [← hg] at h1
    exact transport (actL g) o h1.1 h1.2 (Filter.eventually_of_mem (hop.mem_nhds hh) fun x hx => ho g x hx)
  refine ⟨fun h hh => (key h hh).1.continuousAt.continuousWithinAt, funext fun y => ?_⟩
  have h2 := hS (HS L N) (Pos L N) hop (PositivityTheory.KB.WhittakerCocycle.pos_open_convex L N).2 q o
    (fun h hh => ((key h hh).1.of_le (by simp)).contDiffWithinAt) (fun j => (y j).1) fun j => (y j).2
  refine Eq.trans h2 ?_
  unfold intS
  refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
  rw [(key _ (simplex_mem (fun j => (y j).2) ht)).2]
  rfl

end PositivityTheory.KB.TwAG

end
