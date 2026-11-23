import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open Filter Topology
open scoped TensorProduct

namespace GlobalTheory.ThetaVacuumAE

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_finset_of_mem_nhds {F : Type} [Field F] [NumberField F] {N : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)} (hN : N ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ α ∈ intAf F, (∀ v ∈ S, evalV F v α = 0) → α ∈ N := by
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := cofinite)).continuous
  have h := hc.tendsto (fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩) hN
  have h' := mem_map.1 h
  rw [nhds_pi, mem_pi'] at h'
  obtain ⟨I, t, ht, hI⟩ := h'
  refine ⟨I, fun α hα h0 => ?_⟩
  have hm : (fun w => (⟨evalV F w α, hα w⟩ : (w.adicCompletionIntegers F : Set (w.adicCompletion F)))) ∈
      Set.pi (I : Set (HeightOneSpectrum (𝓞 F))) t := by
    intro w hw
    have := mem_of_mem_nhds (ht w)
    convert this using 2
    exact h0 w hw
  exact hI hm

theorem fg_int {E : Type} [Field E] [NumberField E] {M : Submodule (𝓞 E) E} (h : M.FG) : (M.restrictScalars ℤ).FG :=
  Submodule.FG.restrictScalars h

theorem exists_fg_coord {D : D7} (V : HSp D) :
    ∃ M : Submodule ℤ D.host.E, M.FG ∧ ∀ x ∈ L0c D V, ∀ i, x i ∈ M ∧ star (x i) ∈ M := by
  let P : Submodule (𝓞 D.host.E) D.host.E := ⨆ i, V.L0.map ((V.frame.coord i).restrictScalars (𝓞 D.host.E))
  have hP : P.FG := Submodule.fg_iSup _ fun i => V.standardTuple_isLattice.fg.map _
  have hx : ∀ x ∈ L0c D V, ∀ i, x i ∈ P := fun x hx i =>
    Submodule.mem_iSup_of_mem i ⟨_, hx, by simp [Finsupp.single_apply]⟩
  let c : D.host.E →ₗ[ℤ] D.host.E := (starRingEnd D.host.E).toAddMonoidHom.toIntLinearMap
  refine ⟨P.restrictScalars ℤ ⊔ (P.restrictScalars ℤ).map c, (fg_int hP).sup ((fg_int hP).map c), fun x h i =>
    ⟨Submodule.mem_sup_left (hx x h i), Submodule.mem_sup_right ⟨x i, hx x h i, rfl⟩⟩⟩

theorem continuous_tmul (D : D7) (e : D.host.E) :
    Continuous fun α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => (pairA D.host.F 0 α ⊗ₜ[D.host.F] e : AE D) := by
  have hp : Continuous fun β : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => pairA D.host.F 0 β := continuous_const.prodMk continuous_id
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h := hp.smul (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D)))
  refine h.congr fun α => ?_
  simp only [Pi.smul_apply', TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end GlobalTheory.ThetaVacuumAE

end
