import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LBumpExA
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.IntMatIsCompact

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace PositivityTheory.Rg.Rsw.L.LBumpEx

variable {D : D7}

theorem theta_e (θ : InfFam D) (hθ : IsInfFam θ) {e : AE D} (he : ∀ w, compInf D.host.F D.host.E w e = 1)
    (τ : D.what₂.Tau) : θ τ (infPart D e) = 1 := by
  have h := ((GlobalTheory.StdUnn.RealComp.real_components D θ hθ).1 (e - 1)).1
    (fun w => by rw [map_sub, map_one, he w, sub_self])
  have h' := h τ
  rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h'
  exact h'

end PositivityTheory.Rg.Rsw.L.LBumpEx

open PositivityTheory.Rg.Rsw.L.LBumpEx Classical in
theorem PositivityTheory.Rg.Rsw.L.bumpEx : IdemEx → BumpEx := by
  intro hI D θ hθ a b S e he C hC hCi
  obtain ⟨hee, -⟩ := (hI D S).2 e he
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨hom⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have : T2Space (AE D) := hom.isEmbedding.t2Space
  set ef : AfE D := finPart D e with hef_def
  have hef : ef * ef = ef := by rw [hef_def, ← map_mul, hee]
  have hefI : ef ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D ef hef
  have hS : ∀ v : Pl D, PositivityTheory.Rg.Rsw.L.LBumpEx.cf v ef = if v ∈ S then 1 else 0 := fun v => by
    rw [← cv_eq]; exact he.2 v
  have hθe := theta_e θ hθ he.1
  obtain ⟨N, hN, hNC⟩ := exists_nat_mul_mem (D := D)
    (Q := ⋃ i, ⋃ j, (fun x : Mx D a b => ef * finPart D (x i j)) '' C)
    (isCompact_iUnion fun i => isCompact_iUnion fun j => hC.image
      (continuous_const.mul ((GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j))))
  let W := U S ef N 1 b
  have hWo : IsOpen (W : Set (Matrix (Fin 1) (Fin b) (AfE D))) := U_isOpen hefI N 1 b
  have hWc : IsCompact (W : Set (Matrix (Fin 1) (Fin b) (AfE D))) := U_isCompact hefI hS hN 1 b
  let g : Matrix (Fin 1) (Fin b) (AfE D) → ℂ := fun w =>
    if (QuotientAddGroup.mk w : _ ⧸ W) = 0 then 1 else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin b → AfE D) := GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  have hg1 : ∀ w, g w = if w ∈ W then 1 else 0 := fun w => by
    simp only [g, QuotientAddGroup.eq_zero_iff]
  let rc : Mx D 1 b → (D.what₂.Tau → Fin 1 → Fin b → ℂ) := fun y τ i j => compAt θ τ y i j
  have hrc : Continuous rc := continuous_pi fun τ => GlobalTheory.RealWeil.continuous_compAt hθ τ 1 b
  have hK : IsCompact (⋃ i, (fun x : Mx D a b => rc (x.submatrix (fun _ : Fin 1 => i) id)) '' C) :=
    isCompact_iUnion fun i => hC.image (hrc.comp (continuous_id.matrix_submatrix _ _))
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  let bump : ContDiffBump (0 : D.what₂.Tau → Fin 1 → Fin b → ℂ) :=
    ⟨max R 1, max R 1 + 1, lt_max_of_lt_right one_pos, by linarith⟩
  have hc : HasCompactSupport fun y => ((bump y : ℝ) : ℂ) :=
    bump.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  let f : SchwartzMap (D.what₂.Tau → Fin 1 → Fin b → ℂ) ℂ :=
    hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp bump.contDiff)
  have hf : ∀ y, f y = ((bump y : ℝ) : ℂ) := fun y => rfl
  let η₀ : Mx D 1 b → ℂ := fun y => f (fun τ i j => compAt θ τ y i j) * g (fun i j => finPart D (y i j))
  have hη : ∀ y, η₀ y = ((bump (rc y) : ℝ) : ℂ) *
      (if (Matrix.of fun i j => finPart D (y i j)) ∈ W then 1 else 0) := fun y => by
    show f _ * g _ = _
    rw [hf]
    congr 1
    exact hg1 _
  refine ⟨fun _ => η₀, fun i => ⟨Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    obtain ⟨Ka, hKa, hKaC⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (max R 1 + 1)
      (⋃ i, ⋃ j, (fun w : Matrix (Fin 1) (Fin b) (AfE D) => w i j) '' (W : Set _))
      (isCompact_iUnion fun i => isCompact_iUnion fun j =>
        (hWc.image ((continuous_apply j).comp (continuous_apply i)) :
          IsCompact ((fun w : Matrix (Fin 1) (Fin b) (AfE D) => w i j) '' (W : Set _))))
    have hKc : IsCompact {y : Mx D 1 b | ∀ i j, y i j ∈ Ka} :=
      isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hKa
    refine HasCompactSupport.intro' hKc hKc.isClosed fun y hy => ?_
    by_contra hne
    change ¬ η₀ y = 0 at hne
    apply hy
    intro i j
    rw [hη] at hne
    have h1 := left_ne_zero_of_mul hne
    have h2 := right_ne_zero_of_mul hne
    have hw : (Matrix.of fun i j => finPart D (y i j)) ∈ W := by
      by_contra h
      exact h2 (if_neg h)
    refine hKaC _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, _, hw, rfl⟩⟩) fun ρ => ?_
    have hb : bump (rc y) ≠ 0 := fun h => h1 (by rw [h, Complex.ofReal_zero])
    have hmem : rc y ∈ Metric.ball (0 : D.what₂.Tau → Fin 1 → Fin b → ℂ) (max R 1 + 1) := by
      rw [← bump.support_eq]; exact hb
    rw [mem_ball_zero_iff] at hmem
    have h3 : ‖rc y ρ i j‖ ≤ ‖rc y‖ :=
      ((norm_le_pi_norm (rc y ρ i) j).trans (norm_le_pi_norm (rc y ρ) i)).trans (norm_le_pi_norm (rc y) ρ)
    exact h3.trans hmem.le
  ·
    intro y
    show η₀ y = if IntOff S y then η₀ (e • y) else 0
    by_cases hy : IntOff S y
    · rw [if_pos hy, hη, hη]
      have hr : rc (e • y) = rc y := by
        funext τ i j
        show θ τ (infPart D ((e • y) i j)) = θ τ (infPart D (y i j))
        rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_mul, hθe τ, one_mul]
      have hw : (Matrix.of fun i j => finPart D ((e • y) i j)) = Matrix.of fun i j => ef * finPart D (y i j) := by
        funext i j
        rw [Matrix.of_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      have hiff := mem_U_iff (N := N) hef hS (w := Matrix.of fun i j => finPart D (y i j))
        (fun v hv i j => by rw [Matrix.of_apply, ← cv_eq]; exact hy v hv i j)
      rw [hr, hw]
      simp only [Matrix.of_apply] at hiff
      by_cases hm : (Matrix.of fun i j => finPart D (y i j)) ∈ W
      · rw [if_pos hm, if_pos (hiff.1 hm)]
      · rw [if_neg hm, if_neg (fun h => hm (hiff.2 h))]
    · rw [if_neg hy, hη, if_neg, mul_zero]
      intro hm
      exact hy fun v hv i j => by rw [cv_eq]; exact hm.1 v hv i j
  ·
    intro y
    show 0 ≤ (η₀ y).re ∧ (η₀ y).re ≤ 1 ∧ (η₀ y).im = 0
    rw [hη]
    split_ifs
    · rw [mul_one, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨bump.nonneg, bump.le_one, rfl⟩
    · simp
  ·
    intro x hx
    show η₀ (x.submatrix (fun _ => i) id) = 1
    rw [hη, if_pos, bump.one_of_mem_closedBall]
    · simp
    · exact Metric.closedBall_subset_closedBall (le_max_left _ _)
        (hR (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩))
    · refine ⟨fun v hv i' j => ?_, fun i' j => ?_⟩
      · rw [Matrix.of_apply, ← cv_eq]; exact hCi x hx v hv i j
      · exact hNC _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, x, hx, rfl⟩⟩)

end
