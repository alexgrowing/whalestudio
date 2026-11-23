import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory

namespace GlobalTheory.GodementJacquet.TestNearE

open ValuativeRel Filter Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def topRows (r t : ℕ) (x : Matrix (Fin (r + t)) (Fin r) k) : Matrix (Fin r) (Fin r) k :=
  x.submatrix (Fin.castAdd t) id

theorem continuous_topRows (r t : ℕ) : Continuous (topRows (k := k) r t) :=
  Continuous.matrix_submatrix continuous_id _ _

theorem topRows_eMat_mul (r t : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    topRows r t (eMat k r t * g) = g := by
  ext i j
  simp [topRows, eMat, Matrix.mul_apply, Fin.val_inj]

theorem topRows_eMat (r t : ℕ) : topRows r t (eMat k r t) = 1 := by
  simpa using topRows_eMat_mul (k := k) r t 1

theorem isOpen_vle {δ : ValueGroupWithZero k} (hδ : δ ≠ 0) :
    IsOpen {z : k | valuation k z ≤ δ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 δ hδ, fun z hz => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hz hx ⊢
  calc valuation k z = valuation k ((z - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (valuation k (z - x)) (valuation k x) := Valuation.map_add _ _ _
    _ ≤ δ := max_le hz.le hx

theorem isCompact_vle_sub (δ : ValueGroupWithZero k) (c : k) :
    IsCompact {z : k | valuation k (z - c) ≤ δ} := by
  have h := (IsNonarchimedeanLocalField.isCompact_closedBall k δ).image (continuous_add_right c)
  convert h using 1
  ext z
  constructor
  · intro hz
    exact ⟨z - c, hz, sub_add_cancel z c⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem exists_nhds_one (r : ℕ) (S : Set (GL (Fin r) k)) (hS : IsOpen S) (h1 : (1 : GL (Fin r) k) ∈ S) :
    ∃ W ∈ 𝓝 (1 : Matrix (Fin r) (Fin r) k), ∀ g : GL (Fin r) k, g.val ∈ W → g ∈ S := by
  obtain ⟨U, hU, hUS⟩ := (Units.isEmbedding_embedProduct (M := Matrix (Fin r) (Fin r) k)).isInducing.isOpen_iff.mp hS
  let φ : Matrix (Fin r) (Fin r) k → Matrix (Fin r) (Fin r) k × (Matrix (Fin r) (Fin r) k)ᵐᵒᵖ :=
    fun x => (x, MulOpposite.op x⁻¹)
  have hφ : ContinuousAt φ 1 := by
    refine continuousAt_id.prodMk (MulOpposite.continuous_op.continuousAt.comp ?_)
    apply continuousAt_matrix_inv
    rw [Matrix.det_one, Ring.inverse_eq_inv']
    exact continuousAt_inv₀ one_ne_zero
  have hemb : ∀ g : GL (Fin r) k, Units.embedProduct _ g = φ g.val := by
    intro g
    simp [φ, Units.embedProduct_apply, Matrix.coe_units_inv]
  refine ⟨φ ⁻¹' U, hφ.preimage_mem_nhds (hU.mem_nhds ?_), fun g hg => ?_⟩
  · have : (1 : GL (Fin r) k) ∈ Units.embedProduct _ ⁻¹' U := by rw [hUS]; exact h1
    simpa [hemb] using this
  · rw [← hUS]
    show Units.embedProduct _ g ∈ U
    rw [hemb]; exact hg

end GlobalTheory.GodementJacquet.TestNearE

namespace GlobalTheory.GodementJacquet.TestNearE

open ValuativeRel Filter Topology

theorem nhds_zero_basis (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) : (𝓝 (0 : Matrix (Fin n) (Fin m) k)).HasBasis
      (fun IJ : Set (Fin n) × (Set (Fin m) × (ValueGroupWithZero k)ˣ) => IJ.1.Finite ∧ (IJ.2.1.Finite ∧ True))
      (fun IJ => IJ.1.pi fun _ => IJ.2.1.pi fun _ => {x : k | valuation k x < IJ.2.2}) := by
  have h0 := IsValuativeTopology.hasBasis_nhds_zero k
  have h1 : (𝓝 (0 : Fin m → k)).HasBasis (fun Ik : Set (Fin m) × (ValueGroupWithZero k)ˣ => Ik.1.Finite ∧ True)
      (fun Ik => Ik.1.pi fun _ => {x : k | valuation k x < Ik.2}) := by
    rw [nhds_pi]; exact h0.pi_self
  have h2 : (𝓝 (0 : Fin n → Fin m → k)).HasBasis
      (fun IJ : Set (Fin n) × (Set (Fin m) × (ValueGroupWithZero k)ˣ) => IJ.1.Finite ∧ (IJ.2.1.Finite ∧ True))
      (fun IJ => IJ.1.pi fun _ => IJ.2.1.pi fun _ => {x : k | valuation k x < IJ.2.2}) := by
    rw [nhds_pi]; exact h1.pi_self
  exact h2

theorem exists_test (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (S : Set (GL (Fin r) k)) (hS : IsOpen S) (h1 : (1 : GL (Fin r) k) ∈ S) :
    ∃ Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ, Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) ∧
      Φ (eMat k r t) = 1 ∧ (∀ x, Φ x = 0 ∨ Φ x = 1) ∧
      ∀ g : GL (Fin r) k, Φ (eMat k r t * g.val) ≠ 0 → g ∈ S := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  set e := eMat k r t
  obtain ⟨W, hW, hWS⟩ := exists_nhds_one r S hS h1
  have hP : topRows r t ⁻¹' W ∈ 𝓝 e :=
    (continuous_topRows (k := k) r t).continuousAt.preimage_mem_nhds (by rw [topRows_eMat]; exact hW)
  have hP' : (fun y => y + e) ⁻¹' (topRows r t ⁻¹' W) ∈ 𝓝 (0 : Matrix (Fin (r + t)) (Fin r) k) :=
    (continuous_add_right e).continuousAt.preimage_mem_nhds (by rw [zero_add]; exact hP)
  obtain ⟨⟨I, J, γ⟩, -, hsub⟩ := (nhds_zero_basis k (r + t) r).mem_iff.mp hP'
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  set δ : ValueGroupWithZero k := (γ : ValueGroupWithZero k) * valuation k ϖ
  have hδ0 : δ ≠ 0 := mul_ne_zero γ.ne_zero (by simpa using hϖ0)
  have hδγ : δ < γ := mul_lt_of_lt_one_right (zero_lt_iff.mpr γ.ne_zero) hϖ1
  set N : Set (Matrix (Fin (r + t)) (Fin r) k) := {x | ∀ i j, valuation k (x i j - e i j) ≤ δ}
  have hNpi : N = Set.pi Set.univ fun i => Set.pi Set.univ fun j => {z : k | valuation k (z - e i j) ≤ δ} :=
    Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
  have hNc : IsCompact N := by
    rw [hNpi]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_vle_sub δ (e i j)
  have hNo : IsOpen N := by
    have : N = ⋂ i, ⋂ j, (fun x : Matrix (Fin (r + t)) (Fin r) k => x i j - e i j) ⁻¹' {z : k | valuation k z ≤ δ} := by
      ext x; simp [N]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (isOpen_vle hδ0).preimage ((Continuous.matrix_elem continuous_id i j).sub continuous_const)
  have hNcl : IsClosed N := hNc.isClosed
  have heN : e ∈ N := fun i j => by simp
  have hNP : ∀ x ∈ N, topRows r t x ∈ W := by
    intro x hx
    have : x - e ∈ I.pi fun _ => J.pi fun _ => {z : k | valuation k z < γ} :=
      fun i _ j _ => lt_of_le_of_lt (by simpa using hx i j) hδγ
    simpa using hsub this
  classical
  refine ⟨N.indicator 1, ⟨?_, ?_⟩, by simp [heN], fun x => ?_, fun g hg => ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ N
    · exact ⟨N, hNo, hx, fun y hy => by simp [hx, hy]⟩
    · exact ⟨Nᶜ, hNcl.isOpen_compl, hx, fun y hy => by simp [hx, Set.indicator_of_notMem hy]⟩
  · exact HasCompactSupport.intro' hNc hNcl fun x hx => Set.indicator_of_notMem hx _
  · by_cases hx : x ∈ N <;> simp [hx]
  · have hm : e * g.val ∈ N := by
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    have := hNP _ hm
    rw [topRows_eMat_mul] at this
    exact hWS g this

end GlobalTheory.GodementJacquet.TestNearE
