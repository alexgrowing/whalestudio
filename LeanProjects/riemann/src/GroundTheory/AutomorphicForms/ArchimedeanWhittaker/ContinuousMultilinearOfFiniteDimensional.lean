import Mathlib
import GroundTheory.AutomorphicForms.GKModules.GKModule
import GroundTheory.AutomorphicForms.GKModules.Garding
import GroundTheory.AutomorphicForms.GKModules.Casimir

namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

noncomputable def wordOp : {k : ℕ} → (Fin k → 𝔤) → E → E
  | 0, _, v => v
  | _ + 1, Y, v => h.derivOp π (Y 0) (wordOp (Fin.tail Y) v)

@[simp] theorem wordOp_zero' (Y : Fin 0 → 𝔤) (v : E) : h.wordOp π Y v = v := rfl

theorem wordOp_succ {k : ℕ} (Y : Fin (k + 1) → 𝔤) (v : E) :
    h.wordOp π Y v = h.derivOp π (Y 0) (h.wordOp π (Fin.tail Y) v) := rfl

theorem isSmoothVector_wordOp {v : E} (hv : h.IsSmoothVector π v) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤), h.IsSmoothVector π (h.wordOp π Y v)
  | 0, _ => hv
  | _ + 1, Y => h.isSmoothVector_derivOp π (isSmoothVector_wordOp hv (Fin.tail Y)) (Y 0)

theorem wordOp_add {v w : E} (hv : h.IsSmoothVector π v) (hw : h.IsSmoothVector π w) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤), h.wordOp π Y (v + w) = h.wordOp π Y v + h.wordOp π Y w
  | 0, _ => rfl
  | _ + 1, Y => by
    rw [wordOp_succ, wordOp_add hv hw (Fin.tail Y),
      h.derivOp_add π (h.isSmoothVector_wordOp π hv _) (h.isSmoothVector_wordOp π hw _)]
    rfl

theorem wordOp_smul {v : E} (hv : h.IsSmoothVector π v) (c : ℂ) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤), h.wordOp π Y (c • v) = c • h.wordOp π Y v
  | 0, _ => rfl
  | _ + 1, Y => by
    rw [wordOp_succ, wordOp_smul hv c (Fin.tail Y),
      h.derivOp_smul π (h.isSmoothVector_wordOp π hv _)]
    rfl

theorem isSmoothVector_zero : h.IsSmoothVector π (0 : E) := (h.smoothVectors π).zero_mem

theorem wordOp_neg {v : E} (hv : h.IsSmoothVector π v) {k : ℕ} (Y : Fin k → 𝔤) :
    h.wordOp π Y (-v) = -h.wordOp π Y v := by
  have := h.wordOp_smul π hv (-1) Y
  simpa using this

theorem wordOp_sub {v w : E} (hv : h.IsSmoothVector π v) (hw : h.IsSmoothVector π w)
    {k : ℕ} (Y : Fin k → 𝔤) : h.wordOp π Y (v - w) = h.wordOp π Y v - h.wordOp π Y w := by
  have hw' : h.IsSmoothVector π (-w) := (h.smoothVectors π).neg_mem hw
  rw [sub_eq_add_neg, h.wordOp_add π hv hw', h.wordOp_neg π hw, ← sub_eq_add_neg]

theorem Ad_Ad_inv (g : G) (X : 𝔤) : h.Ad g (h.Ad g⁻¹ X) = X := by
  have := h.Ad_inv_Ad g⁻¹ X
  rwa [inv_inv] at this

theorem wordOp_map {v : E} (hv : h.IsSmoothVector π v) (g : G) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤),
      h.wordOp π Y (π g v) = π g (h.wordOp π (fun i => h.Ad g⁻¹ (Y i)) v)
  | 0, _ => rfl
  | k + 1, Y => by
    rw [wordOp_succ, wordOp_map hv g (Fin.tail Y), wordOp_succ]
    have := h.derivOp_map π (h.isSmoothVector_wordOp π hv (fun i => h.Ad g⁻¹ (Fin.tail Y i)))
      g (h.Ad g⁻¹ (Y 0))
    rw [Ad_Ad_inv] at this
    rw [this]
    rfl

end IsExpLieAlgebra

end GroundTheory.Automorphic

namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

omit [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in

theorem _root_.GroundTheory.Automorphic.continuous_multilinear_of_finiteDimensional {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : MultilinearMap ℝ (fun _ : ι => M) F) : Continuous f := by
  let b := Module.finBasis ℝ M
  have key : ∀ Y : ι → M, f Y = ∑ r ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset (Fin (Module.finrank ℝ M)))),
      (∏ i, b.repr (Y i) (r i)) • f (fun i => b (r i)) := by
    intro Y
    have hY : Y = fun i => ∑ j, b.repr (Y i) j • b j := funext fun i => (b.sum_repr (Y i)).symm
    conv_lhs => rw [hY]
    rw [f.map_sum_finset]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact f.map_smul_univ (fun i => b.repr (Y i) (r i)) (fun i => b (r i))
  have e : (f : (ι → M) → F) = fun Y => ∑ r ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset (Fin (Module.finrank ℝ M)))),
      (∏ i, b.repr (Y i) (r i)) • f (fun i => b (r i)) := funext key
  rw [e]
  refine continuous_finsetSum _ fun r _ => ?_
  refine (continuous_finsetProd _ fun i _ => ?_).smul continuous_const
  exact ((b.coord (r i)).continuous_of_finiteDimensional).comp (continuous_apply i)

noncomputable def wordML {v : E} (hv : h.IsSmoothVector π v) :
    (k : ℕ) → MultilinearMap ℝ (fun _ : Fin k => 𝔤) (h.smoothVectors π)
  | 0 => MultilinearMap.constOfIsEmpty ℝ _ ⟨v, hv⟩
  | k + 1 => LinearMap.uncurryLeft
      { toFun := fun X => ((h.derivEnd π X).restrictScalars ℝ).compMultilinearMap (wordML hv k)
        map_add' := fun X Y => by
          ext m
          simp [h.derivOp_add_left]
        map_smul' := fun r X => by
          ext m
          simp [h.derivOp_smul_left] }

theorem coe_wordML {v : E} (hv : h.IsSmoothVector π v) :
    ∀ (k : ℕ) (Y : Fin k → 𝔤), ((h.wordML π hv k Y : h.smoothVectors π) : E) = h.wordOp π Y v
  | 0, _ => rfl
  | k + 1, Y => by
    rw [wordML, LinearMap.uncurryLeft_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compMultilinearMap_apply,
      LinearMap.coe_restrictScalars, coe_derivEnd]
    rw [coe_wordML hv k (Fin.tail Y)]
    rfl

theorem exists_wordOp_cml {v : E} (hv : h.IsSmoothVector π v) (k : ℕ) :
    ∃ Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) E, ∀ Y, Φ Y = h.wordOp π Y v := by
  let M : MultilinearMap ℝ (fun _ : Fin k => 𝔤) E :=
    ((h.smoothVectors π).subtype.restrictScalars ℝ).compMultilinearMap (h.wordML π hv k)
  refine ⟨⟨M, continuous_multilinear_of_finiteDimensional M⟩, fun Y => ?_⟩
  show ((h.wordML π hv k Y : h.smoothVectors π) : E) = _
  exact h.coe_wordML π hv k Y

end IsExpLieAlgebra

end GroundTheory.Automorphic

namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

noncomputable def brSum (X : 𝔤) : {k : ℕ} → (Fin k → 𝔤) → E → E
  | 0, _, _ => 0
  | _ + 1, Y, v => h.derivOp π (h.bracket X (Y 0)) (h.wordOp π (Fin.tail Y) v) +
      h.derivOp π (Y 0) (brSum X (Fin.tail Y) v)

theorem isSmoothVector_brSum {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤), h.IsSmoothVector π (h.brSum π X Y v)
  | 0, _ => h.isSmoothVector_zero π
  | _ + 1, Y => (h.smoothVectors π).add_mem
      (h.isSmoothVector_derivOp π (h.isSmoothVector_wordOp π hv _) _)
      (h.isSmoothVector_derivOp π (isSmoothVector_brSum hv X (Fin.tail Y)) _)

theorem derivOp_wordOp {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤),
      h.derivOp π X (h.wordOp π Y v) = h.brSum π X Y v + h.wordOp π Y (h.derivOp π X v)
  | 0, _ => by simp [brSum]
  | k + 1, Y => by
    have hu := h.isSmoothVector_wordOp π hv (Fin.tail Y)
    have hb := h.derivOp_bracket π hu X (Y 0)
    rw [wordOp_succ, wordOp_succ, brSum]
    rw [eq_sub_iff_add_eq] at hb
    rw [← hb, derivOp_wordOp hv X (Fin.tail Y),
      h.derivOp_add π (h.isSmoothVector_brSum π hv X _)
        (h.isSmoothVector_wordOp π (h.isSmoothVector_derivOp π hv X) _), add_assoc]

theorem derivOp_sum {ι : Type*} (s : Finset ι) {w : ι → E} (hw : ∀ i, h.IsSmoothVector π (w i))
    (X : 𝔤) : h.derivOp π X (∑ i ∈ s, w i) = ∑ i ∈ s, h.derivOp π X (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using h.derivOp_smul π (h.isSmoothVector_zero π) 0 X
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      h.derivOp_add π (hw a) ((h.smoothVectors π).sum_mem fun i _ => hw i), ih]

theorem sum_wordOp_update {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤),
      ∑ i, h.wordOp π (Function.update Y i (h.bracket X (Y i))) v = h.brSum π X Y v
  | 0, _ => by simp [brSum]
  | k + 1, Y => by
    rw [Fin.sum_univ_succ, brSum]
    congr 1
    have e : ∀ j : Fin k, h.wordOp π (Function.update Y j.succ (h.bracket X (Y j.succ))) v =
          h.derivOp π (Y 0) (h.wordOp π
            (Function.update (Fin.tail Y) j (h.bracket X (Fin.tail Y j))) v) := by
      intro j
      rw [wordOp_succ, Fin.tail_update_succ,
        Function.update_of_ne (Fin.succ_ne_zero j).symm]
      rfl
    simp_rw [e]
    rw [← h.derivOp_sum π _ (fun j => h.isSmoothVector_wordOp π hv _),
      sum_wordOp_update hv X (Fin.tail Y)]

theorem hasDerivAt_expG_apply (hπ : ∀ g, ‖π g‖ ≤ 1) {w : ℝ → E} {w' : E}
    (hw : HasDerivAt w w' 0) (hw0 : h.IsSmoothVector π (w 0)) (X : 𝔤) :
    HasDerivAt (fun t : ℝ => π (h.expG (t • X)) (w t)) (h.derivOp π X (w 0) + w') 0 := by
  have hA := h.hasDerivAt_derivOp π hw0 X
  have hB : HasDerivAt (fun t : ℝ => π (h.expG (t • X)) (w t - w 0)) w' 0 := by
    rw [hasDerivAt_iff_isLittleO] at hw ⊢
    have hc : Tendsto (fun t : ℝ => π (h.expG (t • X)) w') (𝓝 0) (𝓝 w') := by
      have hcont : Continuous fun t : ℝ => π (h.expG (t • X)) w' :=
        (π.continuous_orbit w').comp (h.continuous_expG.comp (continuous_id.smul continuous_const))
      simpa using hcont.tendsto 0
    rw [isLittleO_iff] at hw ⊢
    intro c hc0
    have h1 := hw (half_pos hc0)
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), ‖π (h.expG (t • X)) w' - w'‖ ≤ c / 2 := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hc)
      exact (this.eventually (ge_mem_nhds (half_pos hc0))).mono fun t ht => ht
    filter_upwards [h1, h2] with t ht1 ht2
    simp only [sub_zero, zero_smul, sub_self, map_zero] at ht1 ⊢
    have e : π (h.expG (t • X)) (w t - w 0) - t • w' =
        π (h.expG (t • X)) (w t - w 0 - t • w') + t • (π (h.expG (t • X)) w' - w') := by
      simp only [map_sub, ContinuousLinearMap.map_smul_of_tower, smul_sub]; abel
    rw [e]
    calc ‖π (h.expG (t • X)) (w t - w 0 - t • w') + t • (π (h.expG (t • X)) w' - w')‖
        ≤ ‖π (h.expG (t • X)) (w t - w 0 - t • w')‖ + ‖t • (π (h.expG (t • X)) w' - w')‖ :=
          norm_add_le _ _
      _ ≤ ‖w t - w 0 - t • w'‖ + ‖t‖ * (c / 2) := by
          gcongr
          · calc ‖π (h.expG (t • X)) (w t - w 0 - t • w')‖
                ≤ ‖π (h.expG (t • X))‖ * ‖w t - w 0 - t • w'‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ 1 * ‖w t - w 0 - t • w'‖ := by gcongr; exact hπ _
              _ = _ := one_mul _
          · rw [norm_smul]; gcongr
      _ ≤ c / 2 * ‖t‖ + ‖t‖ * (c / 2) := by gcongr
      _ = c * ‖t‖ := by ring
  have := hA.add hB
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, map_sub]
  abel

end IsExpLieAlgebra

end GroundTheory.Automorphic

namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

theorem expG_smul_inv (t : ℝ) (X : 𝔤) : (h.expG (t • X))⁻¹ = h.expG (-(t • X)) := by
  rw [← h.expG_neg]

theorem hasDerivAt_wordOp_expG (hπ : ∀ g, ‖π g‖ ≤ 1) {v : E} (hv : h.IsSmoothVector π v)
    (X : 𝔤) {k : ℕ} (Y : Fin k → 𝔤) :
    HasDerivAt (fun t : ℝ => h.wordOp π Y (π (h.expG (t • X)) v))
      (h.wordOp π Y (h.derivOp π X v)) 0 := by
  obtain ⟨Φ, hΦ⟩ := h.exists_wordOp_cml π hv k
  set c : ℝ → (Fin k → 𝔤) := fun t i => h.Ad (h.expG (-(t • X))) (Y i) with hcdef
  have hfun : (fun t : ℝ => h.wordOp π Y (π (h.expG (t • X)) v)) =
      fun t => π (h.expG (t • X)) (Φ (c t)) := by
    funext t
    rw [h.wordOp_map π hv, hΦ, h.expG_smul_inv]
  have hc0 : c 0 = Y := by
    funext i
    simp [hcdef]
  have hcd : HasDerivAt c (fun i => -(h.bracket X (Y i))) 0 := by
    rw [hasDerivAt_pi]
    intro i
    have := (h.hasDerivAt_Ad_expG X (Y i)).scomp_of_eq 0 (hasDerivAt_neg (0 : ℝ)) (by simp)
    simpa [hcdef, Function.comp_def] using this
  have hΦc : HasDerivAt (fun t => Φ (c t))
      (∑ i, Φ (Function.update Y i (-(h.bracket X (Y i))))) 0 := by
    let _inst : NormedSpace ℝ (Fin k → 𝔤) := Pi.normedSpace
    have hF := Φ.hasFDerivAt (c 0)
    have := hF.comp_hasDerivAt (𝕜 := ℝ) (0 : ℝ) hcd
    rw [hc0, ContinuousMultilinearMap.linearDeriv_apply] at this
    exact this
  have hsum : ∑ i, Φ (Function.update Y i (-(h.bracket X (Y i)))) = -h.brSum π X Y v := by
    rw [← h.sum_wordOp_update π hv X Y, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hΦ, ← neg_one_smul ℝ (h.bracket X (Y i)), Φ.map_update_smul, neg_one_smul]
  have hw0 : h.IsSmoothVector π (Φ (c 0)) := by
    rw [hc0, hΦ]; exact h.isSmoothVector_wordOp π hv Y
  have hP := h.hasDerivAt_expG_apply π hπ hΦc hw0 X
  rw [hfun]
  convert hP using 1
  rw [hsum, hc0, hΦ, h.derivOp_wordOp π hv X Y]
  abel

theorem hasDerivAt_wordOp_map_expG (hπ : ∀ g, ‖π g‖ ≤ 1) {v : E} (hv : h.IsSmoothVector π v)
    (X : 𝔤) (g : G) {k : ℕ} (Y : Fin k → 𝔤) :
    HasDerivAt (fun t : ℝ => h.wordOp π Y (π g (π (h.expG (t • X)) v)))
      (h.wordOp π Y (π g (h.derivOp π X v))) 0 := by
  have e : (fun t : ℝ => h.wordOp π Y (π g (π (h.expG (t • X)) v))) =
      fun t => ((π g).restrictScalars ℝ)
        (h.wordOp π (fun i => h.Ad g⁻¹ (Y i)) (π (h.expG (t • X)) v)) := by
    funext t
    rw [h.wordOp_map π (h.isSmoothVector_map π hv _)]
    rfl
  rw [e, h.wordOp_map π (h.isSmoothVector_derivOp π hv X)]
  exact ((π g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (h.hasDerivAt_wordOp_expG π hπ hv X _)

theorem continuous_Ad_apply (X : 𝔤) : Continuous fun g : G => h.Ad g X := by
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous fun g : G => ((g : 𝔸ˣ) : 𝔸) := continuous_val_val G
  have h2 : Continuous fun g : G => (((g⁻¹ : G) : 𝔸ˣ) : 𝔸) := h1.comp continuous_inv
  exact (h1.mul continuous_const).mul h2

theorem continuous_apply_apply (hπ : ∀ g, ‖π g‖ ≤ 1) {T : Type*} [TopologicalSpace T]
    {p : T → G} {u : T → E} (hp : Continuous p) (hu : Continuous u) :
    Continuous fun x => π (p x) (u x) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun x => ‖u x - u x₀‖) (𝓝 x₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hu.tendsto x₀)
  have h2 : Tendsto (fun x => ‖π (p x) (u x₀) - π (p x₀) (u x₀)‖) (𝓝 x₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (((π.continuous_orbit (u x₀)).comp hp).tendsto x₀)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) (by simpa using h1.add h2)
  calc ‖π (p x) (u x) - π (p x₀) (u x₀)‖
      = ‖π (p x) (u x - u x₀) + (π (p x) (u x₀) - π (p x₀) (u x₀))‖ := by
        rw [map_sub]; try abel
    _ ≤ ‖π (p x) (u x - u x₀)‖ + ‖π (p x) (u x₀) - π (p x₀) (u x₀)‖ := norm_add_le _ _
    _ ≤ ‖u x - u x₀‖ + ‖π (p x) (u x₀) - π (p x₀) (u x₀)‖ := by
        gcongr
        calc ‖π (p x) (u x - u x₀)‖ ≤ ‖π (p x)‖ * ‖u x - u x₀‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖u x - u x₀‖ := by gcongr; exact hπ _
          _ = _ := one_mul _

theorem continuous_wordOp_map (hπ : ∀ g, ‖π g‖ ≤ 1) {v : E} (hv : h.IsSmoothVector π v)
    {k : ℕ} (Y : Fin k → 𝔤) : Continuous fun g : G => h.wordOp π Y (π g v) := by
  obtain ⟨Φ, hΦ⟩ := h.exists_wordOp_cml π hv k
  have e : (fun g : G => h.wordOp π Y (π g v)) =
      fun g => π g (Φ (fun i => h.Ad g⁻¹ (Y i))) := by
    funext g; rw [h.wordOp_map π hv, hΦ]
  rw [e]
  refine continuous_apply_apply π hπ continuous_id (Φ.cont.comp ?_)
  exact continuous_pi fun i => (h.continuous_Ad_apply (Y i)).comp continuous_inv

theorem exists_norm_wordOp_map_le (hπ : ∀ g, ‖π g‖ ≤ 1) {v : E} (hv : h.IsSmoothVector π v)
    {k : ℕ} (Y : Fin k → 𝔤) : ∃ C, ∀ g : G, ‖h.wordOp π Y (π g v)‖ ≤ C * ‖h.AdL g⁻¹‖ ^ k := by
  obtain ⟨Φ, hΦ⟩ := h.exists_wordOp_cml π hv k
  refine ⟨‖Φ‖ * ∏ i, ‖Y i‖, fun g => ?_⟩
  rw [h.wordOp_map π hv, ← hΦ]
  calc ‖π g (Φ (fun i => h.Ad g⁻¹ (Y i)))‖ ≤ ‖π g‖ * ‖Φ (fun i => h.Ad g⁻¹ (Y i))‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖Φ (fun i => h.Ad g⁻¹ (Y i))‖ := by gcongr; exact hπ _
    _ = ‖Φ (fun i => h.Ad g⁻¹ (Y i))‖ := one_mul _
    _ ≤ ‖Φ‖ * ∏ i, ‖h.Ad g⁻¹ (Y i)‖ := Φ.le_opNorm _
    _ ≤ ‖Φ‖ * ∏ i, (‖h.AdL g⁻¹‖ * ‖Y i‖) := by
        gcongr with i
        exact (h.AdL g⁻¹).le_opNorm (Y i)
    _ = (‖Φ‖ * ∏ i, ‖Y i‖) * ‖h.AdL g⁻¹‖ ^ k := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring

end IsExpLieAlgebra

end GroundTheory.Automorphic
