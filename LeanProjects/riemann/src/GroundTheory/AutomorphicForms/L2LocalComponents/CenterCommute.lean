import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.GL2BumpFunctions.ParametrixLie

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace IsExpLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

theorem listOp_add {v w : E} (hv : h.IsSmoothVector π v) (hw : h.IsSmoothVector π w) :
    ∀ L : List 𝔤, h.listOp π L (v + w) = h.listOp π L v + h.listOp π L w
  | [] => rfl
  | X :: L => by
    rw [listOp_cons, listOp_cons, listOp_cons, listOp_add hv hw L,
      h.derivOp_add π (h.isSmoothVector_listOp π hv L) (h.isSmoothVector_listOp π hw L)]

theorem listOp_smul {v : E} (hv : h.IsSmoothVector π v) (c : ℂ) :
    ∀ L : List 𝔤, h.listOp π L (c • v) = c • h.listOp π L v
  | [] => rfl
  | X :: L => by
    rw [listOp_cons, listOp_cons, listOp_smul hv c L, h.derivOp_smul π (h.isSmoothVector_listOp π hv L)]

theorem listOp_zero (L : List 𝔤) : h.listOp π L (0 : E) = 0 := by
  have := h.listOp_smul π (h.isSmoothVector_zero π) 0 L
  rwa [zero_smul, zero_smul] at this

def wordSum (L : List (ℂ × List 𝔤)) (v : E) : E := (L.map fun p => p.1 • h.listOp π p.2 v).sum

@[simp] theorem wordSum_nil (v : E) : h.wordSum π [] v = 0 := rfl

theorem wordSum_cons (p : ℂ × List 𝔤) (L : List (ℂ × List 𝔤)) (v : E) :
    h.wordSum π (p :: L) v = p.1 • h.listOp π p.2 v + h.wordSum π L v := rfl

theorem wordSum_append (L₁ L₂ : List (ℂ × List 𝔤)) (v : E) :
    h.wordSum π (L₁ ++ L₂) v = h.wordSum π L₁ v + h.wordSum π L₂ v := by
  simp [wordSum, List.map_append, List.sum_append]

theorem isSmoothVector_wordSum {v : E} (hv : h.IsSmoothVector π v) :
    ∀ L : List (ℂ × List 𝔤), h.IsSmoothVector π (h.wordSum π L v)
  | [] => h.isSmoothVector_zero π
  | p :: L => (h.smoothVectors π).add_mem ((h.smoothVectors π).smul_mem p.1
      (h.isSmoothVector_listOp π hv p.2)) (isSmoothVector_wordSum hv L)

theorem listOp_wordSum {v : E} (hv : h.IsSmoothVector π v) (l : List 𝔤) :
    ∀ L : List (ℂ × List 𝔤),
      h.listOp π l (h.wordSum π L v) = h.wordSum π (L.map fun p => (p.1, l ++ p.2)) v
  | [] => h.listOp_zero π l
  | p :: L => by
    rw [wordSum_cons, h.listOp_add π ((h.smoothVectors π).smul_mem p.1 (h.isSmoothVector_listOp π hv p.2))
      (h.isSmoothVector_wordSum π hv L), h.listOp_smul π (h.isSmoothVector_listOp π hv p.2),
      ← listOp_append, listOp_wordSum hv l L, List.map_cons, wordSum_cons]

theorem wordSum_wordSum {v : E} (hv : h.IsSmoothVector π v) (L₂ : List (ℂ × List 𝔤)) :
    ∀ L₁ : List (ℂ × List 𝔤), h.wordSum π L₁ (h.wordSum π L₂ v) =
      h.wordSum π (L₁.flatMap fun p => L₂.map fun q => (p.1 * q.1, p.2 ++ q.2)) v
  | [] => rfl
  | p :: L₁ => by
    rw [wordSum_cons, List.flatMap_cons, wordSum_append, wordSum_wordSum hv L₂ L₁,
      h.listOp_wordSum π hv p.2 L₂]
    congr 1
    clear L₁
    induction L₂ with
    | nil => simp
    | cons q L ih =>
      rw [List.map_cons, List.map_cons, wordSum_cons, wordSum_cons, smul_add, ih, smul_smul]

theorem exists_wordSum (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    ∃ L : List (ℂ × List 𝔤), ∀ v : h.smoothVectors π, (h.uAction π u v : E) = h.wordSum π L v := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    refine ⟨[((r : ℂ), [])], fun v => ?_⟩
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    rw [wordSum_cons, wordSum_nil, add_zero, listOp_nil, Submodule.coe_smul_of_tower]
    exact (Complex.coe_smul r (v : E)).symm
  | ι x =>
    refine ⟨[(1, [h.ofLie x])], fun v => ?_⟩
    show (h.uAction π (UniversalEnvelopingAlgebra.ι ℝ x) v : E) = _
    rw [uAction_ι, coe_derivEnd, wordSum_cons, wordSum_nil, add_zero, one_smul, listOp_cons, listOp_nil]
  | mul a b iha ihb =>
    obtain ⟨La, ha⟩ := iha
    obtain ⟨Lb, hb⟩ := ihb
    refine ⟨La.flatMap fun p => Lb.map fun q => (p.1 * q.1, p.2 ++ q.2), fun v => ?_⟩
    rw [map_mul, map_mul, Module.End.mul_apply, ha, hb, h.wordSum_wordSum π v.2]
  | add a b iha ihb =>
    obtain ⟨La, ha⟩ := iha
    obtain ⟨Lb, hb⟩ := ihb
    refine ⟨La ++ Lb, fun v => ?_⟩
    rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, ha, hb, wordSum_append]

variable [CompleteSpace E]

theorem hasDerivAt_wordSum_expG (hπ : ∀ g, ‖π g‖ ≤ 1) {w : E} (hw : h.IsSmoothVector π w) (X : 𝔤) :
    ∀ L : List (ℂ × List 𝔤), HasDerivAt (fun s : ℝ => h.wordSum π L (π (h.expG (s • X)) w))
      (h.wordSum π L (h.derivOp π X w)) 0
  | [] => hasDerivAt_const _ _
  | p :: L => by
    have h1 : HasDerivAt (fun s : ℝ => h.listOp π p.2 (π (h.expG (s • X)) w))
        (h.listOp π p.2 (h.derivOp π X w)) 0 := by
      have e : (fun s : ℝ => h.listOp π p.2 (π (h.expG (s • X)) w)) =
          fun s => h.wordOp π (fun i : Fin p.2.length => p.2[i]) (π (h.expG (s • X)) w) :=
        funext fun s => h.listOp_eq_wordOp π _ _
      rw [e, h.listOp_eq_wordOp π]
      exact h.hasDerivAt_wordOp_expG π hπ hw X _
    exact (h1.const_smul p.1).add (hasDerivAt_wordSum_expG hπ hw X L)

theorem uAction_map_expG (hπ : ∀ g, ‖π g‖ ≤ 1) {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra}
    (hz : z ∈ h.centerU) {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) :
    (h.uAction π z ⟨π (h.expG X) v, h.isSmoothVector_map π hv _⟩ : E) =
      π (h.expG X) (h.uAction π z ⟨v, hv⟩) := by
  obtain ⟨L, hL⟩ := h.exists_wordSum π z
  have hX : h.derivEnd π X = h.uAction π (UniversalEnvelopingAlgebra.ι ℝ (h.toLie X)) := by
    rw [uAction_ι, ofLie_toLie]
  have hc : UniversalEnvelopingAlgebra.ι ℝ (h.toLie X) * z =
      z * UniversalEnvelopingAlgebra.ι ℝ (h.toLie X) :=
    Subalgebra.mem_center_iff.1 hz _

  have hzero : ∀ w : h.smoothVectors π, HasDerivAt
      (fun s : ℝ => π (h.expG (s • (-X))) (h.wordSum π L (π (h.expG (s • X)) (w : E)))) 0 0 := by
    intro w
    have h1 := h.hasDerivAt_expG_apply π hπ
      (w := fun s => h.wordSum π L (π (h.expG (s • X)) (w : E)))
      (h.hasDerivAt_wordSum_expG π hπ w.2 X L) (by simpa using h.isSmoothVector_wordSum π w.2 L) (-X)
    convert h1 using 1
    simp only [zero_smul, h.expG_zero, BanachRep.map_one_apply, h.derivOp_neg_left]
    rw [show h.derivOp π X (w : E) = ((h.derivEnd π X w : h.smoothVectors π) : E) from
        (coe_derivEnd _ _ _ _).symm, ← hL, ← hL,
      show h.derivOp π X ((h.uAction π z w : h.smoothVectors π) : E) =
        ((h.derivEnd π X (h.uAction π z w) : h.smoothVectors π) : E) from (coe_derivEnd _ _ _ _).symm,
      hX, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hc, neg_add_cancel]

  set c : ℝ → E := fun t => π (h.expG (t • (-X))) (h.wordSum π L (π (h.expG (t • X)) v)) with hcdef
  have hderiv : ∀ t, HasDerivAt c 0 t := by
    intro t
    set w : h.smoothVectors π := ⟨π (h.expG (t • X)) v, h.isSmoothVector_map π hv _⟩
    have h2 := ((π (h.expG (t • (-X)))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (hzero w)
    simp only [map_zero] at h2
    have h3 : HasDerivAt (fun s : ℝ => π (h.expG (t • (-X)))
        (π (h.expG ((s - t) • (-X))) (h.wordSum π L (π (h.expG ((s - t) • X)) (w : E))))) 0 t := by
      have h2' : HasDerivAt (fun s : ℝ => π (h.expG (t • (-X)))
          (π (h.expG (s • (-X))) (h.wordSum π L (π (h.expG (s • X)) (w : E))))) 0 (t - t) := by
        rw [sub_self]; exact h2
      exact h2'.comp_sub_const t t
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    show π (h.expG (s • (-X))) (h.wordSum π L (π (h.expG (s • X)) v)) = _
    simp only [w]
    rw [← BanachRep.map_mul_apply, ← h.expG_add_smul, add_sub_cancel, ← BanachRep.map_mul_apply,
      ← h.expG_add_smul, sub_add_cancel]
  have hconst : c 1 = c 0 :=
    is_const_of_deriv_eq_zero (fun t => (hderiv t).differentiableAt) (fun t => (hderiv t).deriv) 1 0
  simp only [hcdef, one_smul, zero_smul, h.expG_zero, BanachRep.map_one_apply] at hconst
  have e3 := congrArg (π (h.expG X)) hconst
  rw [← BanachRep.map_mul_apply, h.expG_neg, mul_inv_cancel, BanachRep.map_one_apply] at e3
  exact (hL ⟨_, h.isSmoothVector_map π hv _⟩).trans (e3.trans (congrArg _ (hL ⟨v, hv⟩).symm))

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]

theorem wordSum_integrated (hπ : ∀ g, ‖π g‖ ≤ 1) {w : E} (hw : h.IsSmoothVector π w)
    {f : G → ℂ} (hf : h.IsTestFunction f) :
    ∀ L : List (ℂ × List 𝔤),
      h.wordSum π L (π.integrated μ f w) = ∫ g, f g • h.wordSum π L (π g w) ∂μ
  | [] => by simp
  | p :: L => by
    have := secondCountableTopology_subgroup_units G
    have hfc := hf.continuous h
    have hint1 : Integrable (fun g => f g • (p.1 • h.listOp π p.2 (π g w))) μ := by
      have hc : Continuous fun g : G => h.listOp π p.2 (π g w) := by
        have e : (fun g : G => h.listOp π p.2 (π g w)) =
            fun g => h.wordOp π (fun i : Fin p.2.length => p.2[i]) (π g w) :=
          funext fun g => h.listOp_eq_wordOp π _ _
        rw [e]
        exact h.continuous_wordOp_map π hπ hw _
      exact (hfc.smul (hc.const_smul p.1)).integrable_of_hasCompactSupport hf.2.smul_right
    have hint2 : Integrable (fun g => f g • h.wordSum π L (π g w)) μ := by
      have hc : Continuous fun g : G => h.wordSum π L (π g w) := by
        clear hint1
        induction L with
        | nil => exact continuous_const
        | cons q L ih =>
          have e : (fun g : G => h.listOp π q.2 (π g w)) =
              fun g => h.wordOp π (fun i : Fin q.2.length => q.2[i]) (π g w) :=
            funext fun g => h.listOp_eq_wordOp π _ _
          have hq : Continuous fun g : G => h.listOp π q.2 (π g w) := by
            rw [e]; exact h.continuous_wordOp_map π hπ hw _
          exact (hq.const_smul q.1).add ih
      exact (hfc.smul hc).integrable_of_hasCompactSupport hf.2.smul_right
    rw [wordSum_cons, wordSum_integrated hπ hw hf L, h.listOp_eq_wordOp π,
      h.wordOp_integrated π μ hπ hw hf, ← integral_smul, ← integral_add _ hint2]
    · refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only [wordSum_cons, smul_add, h.listOp_eq_wordOp π]
      rw [smul_comm]
    · simpa only [smul_comm (f _) p.1, h.listOp_eq_wordOp π] using hint1

theorem uAction_integrated (hπ : ∀ g, ‖π g‖ ≤ 1) {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra}
    (hz : z ∈ h.centerU) {f : G → ℂ} (hf : h.IsTestFunction f)
    (hsupp : ∀ g, f g ≠ 0 → ∃ X : 𝔤, g = h.expG X) {w : E} (hw : h.IsSmoothVector π w) :
    (h.uAction π z ⟨π.integrated μ f w, h.isSmoothVector_integrated π μ hf w⟩ : E) =
      π.integrated μ f (h.uAction π z ⟨w, hw⟩) := by
  obtain ⟨L, hL⟩ := h.exists_wordSum π z
  refine (hL ⟨_, h.isSmoothVector_integrated π μ hf w⟩).trans ?_
  show h.wordSum π L (π.integrated μ f w) = _
  rw [h.wordSum_integrated π μ hπ hw hf L]
  unfold BanachRep.integrated
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  by_cases hg : f g = 0
  · simp [hg]
  · obtain ⟨X, rfl⟩ := hsupp g hg
    show f _ • h.wordSum π L (π (h.expG X) w) = f _ • π (h.expG X) _
    congr 1
    exact (hL ⟨π (h.expG X) w, h.isSmoothVector_map π hw _⟩).symm.trans (h.uAction_map_expG π hπ hz hw X)

end IsExpLieAlgebra

end

end GroundTheory.Automorphic
