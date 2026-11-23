import Mathlib
import GroundTheory.PAdicHodge.GaloisOnCp
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open UniformSpace Topology Filter Set

noncomputable section

variable {p : ℕ} [Fact p.Prime]

section Closure

variable (E : IntermediateField ℚ_[p] (PadicAlgCl p))

def closureInCp : Set ℂ_[p] :=
  closure (((↑) : PadicAlgCl p → ℂ_[p]) '' (E : Set (PadicAlgCl p)))

variable {E} in
theorem coe_mem_closureInCp {y : PadicAlgCl p} (hy : y ∈ E) : (y : ℂ_[p]) ∈ closureInCp E :=
  subset_closure ⟨y, hy, rfl⟩

def toClosureInCp (y : E) : closureInCp E :=
  ⟨((y : PadicAlgCl p) : ℂ_[p]), coe_mem_closureInCp y.2⟩

theorem isometry_toClosureInCp : Isometry (toClosureInCp E) :=
  Isometry.of_dist_eq fun x y => by
    change dist ((x : PadicAlgCl p) : ℂ_[p]) ((y : PadicAlgCl p) : ℂ_[p]) = dist x y
    rw [UniformSpace.Completion.dist_eq]
    rfl

theorem denseRange_toClosureInCp : DenseRange (toClosureInCp E) := by
  rw [DenseRange, Topology.IsInducing.subtypeVal.dense_iff]
  rintro ⟨x, hx⟩
  have : Subtype.val '' range (toClosureInCp E) =
      ((↑) : PadicAlgCl p → ℂ_[p]) '' (E : Set (PadicAlgCl p)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  rw [this]
  exact hx

theorem isDenseInducing_toClosureInCp : IsDenseInducing (toClosureInCp E) :=
  (isometry_toClosureInCp E).isUniformInducing.isDenseInducing (denseRange_toClosureInCp E)

variable (R : PadicAlgCl p → PadicAlgCl p)

def extendOnClosure : closureInCp E → ℂ_[p] :=
  (isDenseInducing_toClosureInCp E).extend fun y : E => ((R y : PadicAlgCl p) : ℂ_[p])

open Classical in

def extendToClosure (x : ℂ_[p]) : ℂ_[p] :=
  if hx : x ∈ closureInCp E then extendOnClosure E R ⟨x, hx⟩ else 0

variable {E R}

theorem extendToClosure_of_mem {x : ℂ_[p]} (hx : x ∈ closureInCp E) :
    extendToClosure E R x = extendOnClosure E R ⟨x, hx⟩ :=
  dif_pos hx

theorem isClosed_image_coe (k : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] k] :
    IsClosed (((↑) : PadicAlgCl p → ℂ_[p]) '' (k : Set (PadicAlgCl p))) := by
  have : FiniteDimensional ℚ_[p] (Subalgebra.toSubmodule k.toSubalgebra) :=
    ‹FiniteDimensional ℚ_[p] k›
  have hc : IsComplete (k : Set (PadicAlgCl p)) :=
    Submodule.complete_of_finiteDimensional (Subalgebra.toSubmodule k.toSubalgebra)
  exact ((UniformSpace.Completion.isUniformEmbedding_coe
    (PadicAlgCl p)).isUniformInducing.isComplete_iff.2 hc).isClosed

section Bounded

variable {c : ℝ} (hadd : ∀ y ∈ E, ∀ z ∈ E, R (y + z) = R y + R z)
  (hbound : ∀ y ∈ E, ‖R y‖ ≤ c * ‖y‖)
include hadd

theorem map_sub_of_add {y z : PadicAlgCl p} (hy : y ∈ E) (hz : z ∈ E) :
    R (y - z) = R y - R z := by
  have h := hadd (y - z) (sub_mem hy hz) z hz
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

include hbound

theorem lipschitzWith_coe_comp :
    LipschitzWith (Real.toNNReal c) fun y : E => ((R y : PadicAlgCl p) : ℂ_[p]) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [UniformSpace.Completion.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm,
    ← map_sub_of_add hadd y.2 z.2]
  exact (hbound _ (sub_mem y.2 z.2)).trans
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal c) (norm_nonneg _))

theorem uniformContinuous_coe_comp :
    UniformContinuous fun y : E => ((R y : PadicAlgCl p) : ℂ_[p]) :=
  (lipschitzWith_coe_comp hadd hbound).uniformContinuous

theorem uniformContinuous_extendOnClosure : UniformContinuous (extendOnClosure E R) :=
  uniformContinuous_uniformly_extend (isometry_toClosureInCp E).isUniformInducing
    (denseRange_toClosureInCp E) (uniformContinuous_coe_comp hadd hbound)

theorem continuous_extendOnClosure : Continuous (extendOnClosure E R) :=
  (uniformContinuous_extendOnClosure hadd hbound).continuous

theorem extendOnClosure_toClosureInCp (y : E) :
    extendOnClosure E R (toClosureInCp E y) = ((R y : PadicAlgCl p) : ℂ_[p]) :=
  uniformly_extend_of_ind (isometry_toClosureInCp E).isUniformInducing
    (denseRange_toClosureInCp E) (uniformContinuous_coe_comp hadd hbound) y

theorem extendToClosure_coe {y : PadicAlgCl p} (hy : y ∈ E) :
    extendToClosure E R (y : ℂ_[p]) = ((R y : PadicAlgCl p) : ℂ_[p]) := by
  rw [extendToClosure_of_mem (coe_mem_closureInCp hy)]
  exact extendOnClosure_toClosureInCp hadd hbound ⟨y, hy⟩

theorem extendToClosure_induction {P : ℂ_[p] → ℂ_[p] → Prop}
    (hP : IsClosed {q : ℂ_[p] × ℂ_[p] | P q.1 q.2})
    (h : ∀ y ∈ E, P (y : ℂ_[p]) ((R y : PadicAlgCl p) : ℂ_[p])) :
    ∀ x ∈ closureInCp E, P x (extendToClosure E R x) := by
  intro x hx
  rw [extendToClosure_of_mem hx]
  have hcont : Continuous fun s : closureInCp E => ((s : ℂ_[p]), extendOnClosure E R s) :=
    continuous_subtype_val.prodMk (continuous_extendOnClosure hadd hbound)
  refine (denseRange_toClosureInCp E).induction_on (p := fun s : closureInCp E =>
    P (s : ℂ_[p]) (extendOnClosure E R s)) ⟨x, hx⟩ (hP.preimage hcont) fun y => ?_
  rw [extendOnClosure_toClosureInCp hadd hbound]
  exact h y y.2

omit hadd hbound in

theorem sub_mem_closureInCp {x x' : ℂ_[p]} (hx : x ∈ closureInCp E) (hx' : x' ∈ closureInCp E) :
    x - x' ∈ closureInCp E :=
  map_mem_closure₂ continuous_sub hx hx' (by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact ⟨y - z, sub_mem hy hz, UniformSpace.Completion.coe_sub y z⟩)

theorem extendToClosure_sub {x x' : ℂ_[p]} (hx : x ∈ closureInCp E) (hx' : x' ∈ closureInCp E) :
    extendToClosure E R (x - x') = extendToClosure E R x - extendToClosure E R x' := by
  have hsub : ∀ s t : closureInCp E, (s : ℂ_[p]) - t ∈ closureInCp E := fun s t =>
    sub_mem_closureInCp s.2 t.2
  rw [extendToClosure_of_mem hx, extendToClosure_of_mem hx',
    extendToClosure_of_mem (hsub ⟨x, hx⟩ ⟨x', hx'⟩)]
  have he := continuous_extendOnClosure hadd hbound
  have hdiff : Continuous fun q : closureInCp E × closureInCp E =>
      (⟨(q.1 : ℂ_[p]) - q.2, hsub q.1 q.2⟩ : closureInCp E) :=
    ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  refine (denseRange_toClosureInCp E).induction_on₂ (p := fun s t : closureInCp E =>
    extendOnClosure E R ⟨(s : ℂ_[p]) - t, hsub s t⟩ = extendOnClosure E R s - extendOnClosure E R t)
    (isClosed_eq (he.comp hdiff) ((he.comp continuous_fst).sub (he.comp continuous_snd)))
    (fun y z => ?_) ⟨x, hx⟩ ⟨x', hx'⟩
  have hyz : (⟨((toClosureInCp E y : closureInCp E) : ℂ_[p]) - (toClosureInCp E z : closureInCp E),
      hsub _ _⟩ : closureInCp E) = toClosureInCp E (y - z) := by
    apply Subtype.ext
    change ((y : PadicAlgCl p) : ℂ_[p]) - ((z : PadicAlgCl p) : ℂ_[p]) =
      (((y : PadicAlgCl p) - z : PadicAlgCl p) : ℂ_[p])
    exact (UniformSpace.Completion.coe_sub _ _).symm
  rw [hyz, extendOnClosure_toClosureInCp hadd hbound, extendOnClosure_toClosureInCp hadd hbound,
    extendOnClosure_toClosureInCp hadd hbound]
  change ((R ((y : PadicAlgCl p) - z) : PadicAlgCl p) : ℂ_[p]) = _
  rw [map_sub_of_add hadd y.2 z.2, UniformSpace.Completion.coe_sub]

theorem extendToClosure_add {x x' : ℂ_[p]} (hx : x ∈ closureInCp E) (hx' : x' ∈ closureInCp E) :
    x + x' ∈ closureInCp E ∧
      extendToClosure E R (x + x') = extendToClosure E R x + extendToClosure E R x' := by
  have h0 : (0 : ℂ_[p]) ∈ closureInCp E := by
    simpa using coe_mem_closureInCp (zero_mem E)
  have hneg : -x' ∈ closureInCp E := by simpa using sub_mem_closureInCp h0 hx'
  have h1 : x + x' = x - -x' := by rw [sub_neg_eq_add]
  have hR0 : extendToClosure E R 0 = 0 := by
    have := extendToClosure_sub hadd hbound h0 h0
    rwa [sub_self, sub_self] at this
  have hRneg : extendToClosure E R (-x') = -extendToClosure E R x' := by
    have := extendToClosure_sub hadd hbound h0 hx'
    rwa [zero_sub, hR0, zero_sub] at this
  refine ⟨h1 ▸ sub_mem_closureInCp hx hneg, ?_⟩
  rw [h1, extendToClosure_sub hadd hbound hx hneg, hRneg, sub_neg_eq_add]

theorem norm_extendToClosure_le {x : ℂ_[p]} (hx : x ∈ closureInCp E) :
    ‖extendToClosure E R x‖ ≤ c * ‖x‖ := by
  refine extendToClosure_induction hadd hbound (P := fun u v => ‖v‖ ≤ c * ‖u‖)
    (isClosed_le (continuous_norm.comp continuous_snd)
      (continuous_const.mul (continuous_norm.comp continuous_fst))) (fun y hy => ?_) x hx
  rw [PadicComplex.norm_extends, PadicComplex.norm_extends]
  exact hbound y hy

section Projection

variable {k : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] k]
  (hkE : k ≤ E) (hmaps : ∀ y ∈ E, R y ∈ k) (hfix : ∀ a ∈ k, R a = a)
  (hmul : ∀ a ∈ k, ∀ y ∈ E, R (a * y) = a * R y)

include hmaps in

theorem extendToClosure_mem {x : ℂ_[p]} (hx : x ∈ closureInCp E) :
    extendToClosure E R x ∈ ((↑) : PadicAlgCl p → ℂ_[p]) '' (k : Set (PadicAlgCl p)) :=
  extendToClosure_induction hadd hbound
    (P := fun _ v => v ∈ ((↑) : PadicAlgCl p → ℂ_[p]) '' (k : Set (PadicAlgCl p)))
    ((isClosed_image_coe k).preimage continuous_snd) (fun y hy => ⟨R y, hmaps y hy, rfl⟩) x hx

omit [FiniteDimensional ℚ_[p] k] in
include hkE hfix in

theorem extendToClosure_coe_of_mem {a : PadicAlgCl p} (ha : a ∈ k) :
    extendToClosure E R (a : ℂ_[p]) = a := by
  rw [extendToClosure_coe hadd hbound (hkE ha), hfix a ha]

omit hadd hbound [FiniteDimensional ℚ_[p] k] in
include hkE in

theorem mul_mem_closureInCp {a : PadicAlgCl p} (ha : a ∈ k) {x : ℂ_[p]}
    (hx : x ∈ closureInCp E) : (a : ℂ_[p]) * x ∈ closureInCp E :=
  map_mem_closure (continuous_const.mul continuous_id) hx (by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨a * y, mul_mem (hkE ha) hy, UniformSpace.Completion.coe_mul a y⟩)

omit [FiniteDimensional ℚ_[p] k] in
include hkE hmul in

theorem extendToClosure_mul {a : PadicAlgCl p} (ha : a ∈ k) {x : ℂ_[p]}
    (hx : x ∈ closureInCp E) :
    extendToClosure E R ((a : ℂ_[p]) * x) = (a : ℂ_[p]) * extendToClosure E R x := by
  have hmem := fun s : closureInCp E => mul_mem_closureInCp hkE ha s.2
  rw [extendToClosure_of_mem hx, extendToClosure_of_mem (hmem ⟨x, hx⟩)]
  have he := continuous_extendOnClosure hadd hbound
  have hcont : Continuous fun s : closureInCp E =>
      (⟨(a : ℂ_[p]) * s, hmem s⟩ : closureInCp E) :=
    (continuous_const.mul continuous_subtype_val).subtype_mk _
  refine (denseRange_toClosureInCp E).induction_on (p := fun s : closureInCp E =>
    extendOnClosure E R ⟨(a : ℂ_[p]) * s, hmem s⟩ = (a : ℂ_[p]) * extendOnClosure E R s)
    ⟨x, hx⟩ (isClosed_eq (he.comp hcont) (continuous_const.mul he)) fun y => ?_
  have : (⟨(a : ℂ_[p]) * (toClosureInCp E y : closureInCp E), hmem _⟩ : closureInCp E) =
      toClosureInCp E ⟨a * y, mul_mem (hkE ha) y.2⟩ := by
    apply Subtype.ext
    exact (UniformSpace.Completion.coe_mul a (y : PadicAlgCl p)).symm
  rw [this, extendOnClosure_toClosureInCp hadd hbound, extendOnClosure_toClosureInCp hadd hbound]
  change ((R (a * y) : PadicAlgCl p) : ℂ_[p]) = _
  rw [hmul a ha y y.2, UniformSpace.Completion.coe_mul]

end Projection

section Galois

variable {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)}

omit hadd hbound in

theorem smul_mem_closureInCp (σ : Gal(PadicAlgCl p/K₀)) (hσ : ∀ y ∈ E, σ y ∈ E) {x : ℂ_[p]}
    (hx : x ∈ closureInCp E) : σ • x ∈ closureInCp E :=
  map_mem_closure (continuous_const_smul σ) hx (by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨σ y, hσ y hy, (gal_smul_coe σ y).symm⟩)

theorem extendToClosure_smul (σ : Gal(PadicAlgCl p/K₀)) (hσ : ∀ y ∈ E, σ y ∈ E)
    (hσR : ∀ y ∈ E, R (σ y) = σ (R y)) {x : ℂ_[p]} (hx : x ∈ closureInCp E) :
    extendToClosure E R (σ • x) = σ • extendToClosure E R x := by
  have hmem := fun s : closureInCp E => smul_mem_closureInCp σ hσ s.2
  rw [extendToClosure_of_mem hx, extendToClosure_of_mem (hmem ⟨x, hx⟩)]
  have he := continuous_extendOnClosure hadd hbound
  have hcont : Continuous fun s : closureInCp E => (⟨σ • (s : ℂ_[p]), hmem s⟩ : closureInCp E) :=
    ((continuous_const_smul σ).comp continuous_subtype_val).subtype_mk _
  refine (denseRange_toClosureInCp E).induction_on (p := fun s : closureInCp E =>
    extendOnClosure E R ⟨σ • (s : ℂ_[p]), hmem s⟩ = σ • extendOnClosure E R s)
    ⟨x, hx⟩ (isClosed_eq (he.comp hcont) ((continuous_const_smul σ).comp he)) fun y => ?_
  have : (⟨σ • ((toClosureInCp E y : closureInCp E) : ℂ_[p]), hmem _⟩ : closureInCp E) =
      toClosureInCp E ⟨σ y, hσ y y.2⟩ := by
    apply Subtype.ext
    exact gal_smul_coe σ (y : PadicAlgCl p)
  rw [this, extendOnClosure_toClosureInCp hadd hbound, extendOnClosure_toClosureInCp hadd hbound]
  change ((R (σ y) : PadicAlgCl p) : ℂ_[p]) = _
  rw [hσR y y.2, gal_smul_coe]

omit hadd hbound in
variable (E R) in

def kernelInCp : Set ℂ_[p] :=
  closureInCp E ∩ extendToClosure E R ⁻¹' {0}

variable {k : IntermediateField ℚ_[p] (PadicAlgCl p)}
  (hkE : k ≤ E) (hmaps : ∀ y ∈ E, R y ∈ k) (hfix : ∀ a ∈ k, R a = a)
  (γ : Gal(PadicAlgCl p/K₀)) (hγ : ∀ y ∈ E, γ y ∈ E) (hγR : ∀ y ∈ E, R (γ y) = γ (R y))
  {C : ℝ} (hC : ∀ y ∈ E, R y = 0 → ‖y‖ ≤ C * ‖γ y - y‖)
include hkE hmaps hfix hC

end Galois

end Bounded

end Closure

end

end GroundTheory.PAdicHodge
