import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianUnitaryGroupOneParameterChartStatement

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.UnitChart

open GlobalTheory.Orb (archMat)

def lieU {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * H + H * X = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hX, smul_zero]

theorem exists_realLines_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) ∧
      ∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u := by
  intro F E _ _ _ _ _ σ h n J hJ
  classical
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.choice inferInstance
  let H : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ := fun w => J.map (τ w).1
  have hHu : ∀ w, IsUnit (H w).det := fun w => by
    show IsUnit (J.map (τ w).1).det
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hHh : ∀ w, (H w)ᴴ = H w := fun w => by
    ext i k
    simp only [H, conjTranspose_apply, map_apply]
    rw [← h.2.2.2, hJ.1 i k]
  let e : InfinitePlace F → ℕ := fun w => Module.finrank ℝ (lieU (H w))
  let b : ∀ w, Module.Basis (Fin (e w)) ℝ (lieU (H w)) := fun w => Module.finBasis ℝ _
  let q : (Σ w : InfinitePlace F, Fin (e w)) ≃ Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) :=
    Fintype.equivFin _
  let Zg : Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → Matrix (Fin n) (Fin n) ℂ :=
    fun a => (b (q.symm a).1 (q.symm a).2 : Matrix (Fin n) (Fin n) ℂ)
  have hZg : ∀ a, (Zg a)ᴴ * H (q.symm a).1 + H (q.symm a).1 * Zg a = 0 := fun a => (b (q.symm a).1 (q.symm a).2).2
  have hy : ∀ a (t : ℝ), ∃ y : GArch σ J (q.symm a).1,
      archMat σ J (τ (q.symm a).1) y = NormedSpace.exp (t • Zg a) := fun a t => by
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Zg a)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (hHu (q.symm a).1) (X := t • Zg a) ((lieU (H (q.symm a).1)).smul_mem t (hZg a))
    refine ⟨(archEquiv J h (τ (q.symm a).1)).symm ⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    exact hu
  choose y hy using hy
  let δ : Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → ℝ → GAd σ J :=
    fun a t => embArch σ J (q.symm a).1 (y a t)
  let Zw : InfinitePlace F → Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → Matrix (Fin n) (Fin n) ℂ :=
    fun w a => if (q.symm a).1 = w then Zg a else 0
  have hK : ∀ w a (t : ℝ), archMat σ J (τ w) (projArch σ J w (δ a t)) = NormedSpace.exp (t • Zw w a) := by
    intro w a t
    by_cases hw : (q.symm a).1 = w
    · subst hw
      simp only [δ, Zw, if_pos rfl, projArch_embArch_self, hy]
    · simp only [δ, Zw, if_neg hw, smul_zero, NormedSpace.exp_zero, projArch_embArch_ne σ J (Ne.symm hw), map_one]
  have hunit : ∀ w (g : GArch σ J w), (archMat σ J (τ w) g)ᴴ * H w * archMat σ J (τ w) g = H w := fun w g => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact (archEquiv J h (τ w) g).2
  have hinj : ∀ w, Function.Injective (archMat σ J (τ w)) := fun w g g' hg =>
    (archEquiv J h (τ w)).injective (Subtype.ext (Units.ext (by
      rwa [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at hg)))
  have hloc : ∀ w, ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin _ → ℝ),
      ContinuousAt s 1 ∧ ∀ g ∈ V, gᴴ * H w * g = H w → g = (List.ofFn fun a => NormedSpace.exp (s g a • Zw w a)).prod := by
    intro w
    have hj : Function.Injective fun i : Fin (e w) => q ⟨w, i⟩ := fun i i' hi => by
      simpa using q.injective hi
    have hZj : ∀ i, Zw w (q ⟨w, i⟩) = (b w i : Matrix (Fin n) (Fin n) ℂ) := fun i => by
      show (if (q.symm (q ⟨w, i⟩)).1 = w then Zg (q ⟨w, i⟩) else 0) = _
      rw [if_pos (by simp)]
      show ((b (q.symm (q ⟨w, i⟩)).1 (q.symm (q ⟨w, i⟩)).2 : Matrix (Fin n) (Fin n) ℂ)) = _
      rw [q.symm_apply_apply]
    refine GlobalTheory.T.hermitian_unitary_group_one_parameter_chart n (H w) (hHh w) (hHu w) _ (e w) (Zw w) (fun i => q ⟨w, i⟩) hj ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Zw]
      rw [if_neg]
      intro hw
      apply ha
      rcases hqa : q.symm a with ⟨w', i⟩
      rw [hqa] at hw
      subst hw
      have h2 := congrArg q hqa
      rw [Equiv.apply_symm_apply] at h2
      exact ⟨i, h2.symm⟩
    · intro a
      simp only [Zw]
      split_ifs with hw
      · subst hw; exact hZg a
      · simp
    · simp only [hZj]
      refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
      refine Fintype.linearIndependent_iff.1 (b w).linearIndependent c (Subtype.ext ?_) i
      simpa using hc
    · intro X hX
      simp only [hZj]
      have e1 := congrArg Subtype.val ((b w).sum_repr ⟨X, hX⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e1
      rw [← e1]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose V hV sw hsw hdec using hloc
  let gw : InfinitePlace F → GAd σ J → Matrix (Fin n) (Fin n) ℂ := fun w x => archMat σ J (τ w) (projArch σ J w x)
  have hgc : ∀ w, Continuous (gw w) := fun w =>
    (GlobalTheory.Orb.continuous_archMat σ J (τ w)).comp (continuous_projArch σ J w)
  have hg1 : ∀ w, gw w 1 = 1 := fun w => by simp [gw]
  refine ⟨_, δ, fun a => ⟨(q.symm a).1, τ _, Zg a, hZg a, fun t => ⟨y a t, rfl, hy a t⟩⟩, fun U hU => ?_⟩
  have hfc : Continuous fun x => ofFin σ J (projFin σ J x) := (continuous_ofFin σ J).comp (continuous_projFin σ J)
  refine ⟨{x | ∀ w, gw w x ∈ V w} ∩ {x | ofFin σ J (projFin σ J x) ∈ U}, ?_,
    fun x a => sw (q.symm a).1 (gw (q.symm a).1 x) a, ?_, ?_⟩
  · refine Filter.inter_mem (Filter.eventually_all.2 fun w => (hgc w).continuousAt.preimage_mem_nhds ?_)
      (hfc.continuousAt.preimage_mem_nhds ?_)
    · rw [hg1]; exact hV w
    · simpa using hU
  · exact continuousAt_pi.2 fun a =>
      (continuous_apply a).continuousAt.comp ((hsw _).comp_of_eq (hgc _).continuousAt (hg1 _))
  · intro x hx
    refine ⟨ofFin σ J (projFin σ J x), hx.2, mem_finPts.2 (projInf_ofFin _ _ _), ?_⟩
    conv_lhs => rw [← ofInf_projInf_mul_ofFin_projFin σ J x]
    congr 1
    apply GAd_ext σ J
    · intro w
      apply hinj w
      rw [projArch_ofInf, projInfArch_projInf, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      have e2 : (⇑(archMat σ J (τ w)) ∘ ⇑(projArch σ J w) ∘ fun a => δ a (sw (q.symm a).1 (gw (q.symm a).1 x) a)) =
          fun a => NormedSpace.exp (sw w (gw w x) a • Zw w a) := funext fun a => by
        simp only [Function.comp_apply]
        rw [hK]
        by_cases hw : (q.symm a).1 = w
        · subst hw; rfl
        · simp [Zw, hw]
      rw [e2]
      exact hdec w _ (hx.1 w) (hunit w _)
    · intro v
      rw [proj_ofInf, map_list_prod, List.map_ofFn]
      have e3 : (⇑(proj σ J v) ∘ fun a => δ a (sw (q.symm a).1 (gw (q.symm a).1 x) a)) = fun _ => 1 :=
        funext fun a => by simp [δ]
      rw [e3]
      simp

end GlobalTheory.UnitChart
