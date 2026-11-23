import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LWMajA
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsClopenCompactNbhdZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatDoubledPairSchrodingerFunction

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Pointwise

namespace PositivityTheory.Rg.Rsw.L.LWMaj

variable {D : D7}

theorem adMaj (θ : InfFam D) (hθ : IsInfFam θ) {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) (S : Set (Mx D m n → ℂ))
    (hsupp : ∀ u ∈ S, ∀ x, u x ≠ 0 → GlobalTheory.Unf.InBox K x)
    (hdec : ∀ N : ℕ, ∃ B : ℝ, ∀ u ∈ S, ∀ x, ‖u x‖ * (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ B) :
    ∃ M ∈ schwartzA θ m n, ∀ u ∈ S, ∀ x, ‖u x‖ ≤ ‖M x‖ := by
  classical

  let rc : Mx D m n → (D.what₂.Tau → Fin m → Fin n → ℂ) := fun x τ i j => compAt θ τ x i j
  have hrc : ∀ x, ‖rc x‖ ≤ GlobalTheory.Unf.realSize θ x := by
    intro x
    have h0 := GlobalTheory.Unf.realSize_nonneg θ x
    refine (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun i =>
      (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
    unfold GlobalTheory.Unf.realSize
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, ‖compAt θ τ x i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖compAt θ τ x i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖compAt θ τ x i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

  let S' : Set ((D.what₂.Tau → Fin m → Fin n → ℂ) → ℂ) :=
    {v | ∃ u ∈ S, ∃ x, v = fun z => if z = rc x then u x else 0}
  have hS' : ∀ N : ℕ, ∃ B : ℝ, ∀ v ∈ S', ∀ z, (1 + ‖z‖) ^ N * ‖v z‖ ≤ B := by
    intro N
    obtain ⟨B, hB⟩ := hdec N
    refine ⟨max B 0, ?_⟩
    rintro v ⟨u, hu, x, rfl⟩ z
    by_cases hz : z = rc x
    · subst hz
      simp only [if_true]
      calc (1 + ‖rc x‖) ^ N * ‖u x‖ ≤ (1 + GlobalTheory.Unf.realSize θ x) ^ N * ‖u x‖ :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith [hrc x]) N) (norm_nonneg _)
        _ = ‖u x‖ * (1 + GlobalTheory.Unf.realSize θ x) ^ N := mul_comm _ _
        _ ≤ max B 0 := (hB u hu x).trans (le_max_left _ _)
    · simp only [hz, if_false, norm_zero, mul_zero]
      exact le_max_right _ _
  obtain ⟨F, hF⟩ := schDom S' hS'

  let fp : Mx D m n → (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := fun x i j => finPart D (x i j)
  have hfp : Continuous fp :=
    continuous_pi fun i => continuous_pi fun j =>
      GlobalTheory.SchwartzSch.continuous_finPart'.comp ((continuous_apply j).comp (continuous_apply i))
  obtain ⟨U₀, hU₀, hU₀c, h0⟩ := GlobalTheory.AfTensNbhd.exists_clopen_compact_nbhd_zero D m n
  let _ : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : ContinuousAdd (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousAdd (Af D.host.F) _
  have : IsTopologicalAddGroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.topologicalAddGroup (Af D.host.F) _
  let W := fp '' K + U₀
  have hWc : IsCompact W := (hK.image hfp).add hU₀c
  have hWo : IsOpen W := IsOpen.add_left hU₀.isOpen
  have hWcl : IsClosed W := hU₀.isClosed.add_left_of_isCompact (hK.image hfp)
  have hKW : ∀ x, GlobalTheory.Unf.InBox K x → fp x ∈ W := by
    rintro x ⟨k, hk, hxk⟩
    refine ⟨fp k, ⟨k, hk, rfl⟩, 0, h0, ?_⟩
    show fp k + 0 = fp x
    rw [add_zero]
    funext i j
    have := congrFun (congrFun hxk i) j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.zero_apply] at this
    rw [(finPart D).map_sub, sub_eq_zero] at this
    exact this.symm
  let g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := W.indicator 1
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    show IsLocallyConstant g ∧ HasCompactSupport g
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun y => ?_, ?_⟩
    · by_cases hy : y ∈ W
      · exact ⟨W, hWo, hy, fun y' hy' => by simp [g, hy, hy']⟩
      · exact ⟨Wᶜ, hWcl.isOpen_compl, hy, fun y' hy' => by
          rw [Set.mem_compl_iff] at hy'
          simp only [g, Set.indicator_of_notMem hy', Set.indicator_of_notMem hy]⟩
    · refine HasCompactSupport.intro' (f := g) hWc hWcl fun y hy => ?_
      simp only [g, Set.indicator_of_notMem hy]
  refine ⟨fun x => F (rc x) * g (fp x), Submodule.subset_span ⟨F, g, hg, rfl⟩, fun u hu x => ?_⟩
  by_cases hx : u x = 0
  · rw [hx, norm_zero]; exact norm_nonneg _
  · have hW : fp x ∈ W := hKW x (hsupp u hu x hx)
    have h1 := hF _ ⟨u, hu, x, rfl⟩ (rc x)
    simp only [if_true] at h1
    simp only [g, Set.indicator_of_mem hW, Pi.one_apply, mul_one]
    exact h1

end PositivityTheory.Rg.Rsw.L.LWMaj

end
