import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder Topology

namespace GlobalTheory.FockCompare.ThetaCont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem infPart_eq_zero (h : Chart θ σ) (a : AE D) (ha : ∀ τ, θ τ (infPart D a) = 0) : infPart D a = 0 := by
  let e : AF D.host.F := ((1 : Ainf D.host.F), (0 : Af D.host.F))
  let E : AE D := e ⊗ₜ[D.host.F] (1 : D.host.E)
  have h1 : infPart D E = 1 := rfl
  have h2 : finPart D E = 0 := by
    show (0 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  have h3 : infPart D (E * a) = infPart D a := by rw [RingHom.map_mul, h1, one_mul]
  have h4 : E * a = 0 := h.ext _ (by rw [RingHom.map_mul, h2, zero_mul]) fun τ => by rw [h3]; exact ha τ
  rw [← h3, h4, RingHom.map_zero]

theorem continuous_conj : Continuous (cA D) := by
  let f : AE D →ₐ[AF D.host.F] AE D :=
    Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig
  exact IsModuleTopology.continuous_of_linearMap f.toLinearMap

theorem continuous_hHom (V W : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WA V W} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => hHom V W (x t) (y t) := by
  have hx' : ∀ i j, Continuous fun t => cA D (x t i j) := fun i j =>
    continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp hx))
  have hy' : ∀ i j, Continuous fun t => y t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hy)
  unfold hHom
  split_ifs <;>
    exact continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ =>
      continuous_finset_sum _ fun _ _ => (((hx' _ _).mul continuous_const).mul continuous_const).mul (hy' _ _)

theorem continuous_symplH (V W : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WA V W} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplH V W (x t) (y t) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul (continuous_hHom V W hy hx)))

theorem continuous_of_level_of_smooth (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (V W : HSp D) (f : WA V W → ℂ)
    (hU : ∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u f = f)
    (hs : Sm (iotaW σ V W) f) : Continuous f := by
  obtain ⟨U, hUo, hU⟩ := hU
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
  haveI : ContinuousSub (WA V W) := IsTopologicalAddGroup.to_continuousSub
  refine continuous_iff_continuousAt.2 fun w => ?_
  let x : WA V W → RW V W := fun w' => piW θ V W (w' - w)
  let a : WA V W → WA V W := fun w' => w + iotaW σ V W (x w')
  let u : WA V W → WA V W := fun w' => w' - a w'
  have hx : Continuous x := (continuous_pi' h.inf V W).comp (continuous_id.sub continuous_const)
  have ha : Continuous a := continuous_const.add ((h.continuous_iota V W).comp hx)
  have hu : Continuous u := continuous_id.sub ha
  have huw : u w = 0 := by
    show w - (w + iotaW σ V W (piW θ V W (w - w))) = 0
    rw [sub_self, AddMonoidHom.map_zero, AddMonoidHom.map_zero, add_zero, sub_self]
  have hinf : ∀ w', (u w').map (infPart D) = 0 := by
    intro w'
    have hp : piW θ V W (u w') = 0 := by
      show piW θ V W (w' - (w + iotaW σ V W (piW θ V W (w' - w)))) = 0
      rw [← sub_sub, AddMonoidHom.map_sub, h.pi_iota, sub_self]
    ext i j
    exact infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
  have hg : Continuous fun w' => ψ (-symplH V W (a w') (u w')) * f (a w') :=
    (hψ.comp (continuous_symplH V W ha hu).neg).mul ((hs w).continuous.comp hx)
  have hev : ∀ᶠ w' in 𝓝 w, u w' ∈ U :=
    hu.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [huw]; exact U.zero_mem))
  refine hg.continuousAt.congr (hev.mono fun w' hw' => ?_)
  have e := congrFun (hU _ hw' (hinf w')) (a w')
  have e2 : a w' + u w' = w' := add_sub_cancel _ _
  show ψ (-symplH V W (a w') (u w')) * f (a w') = f w'
  rw [← e]
  show _ * (ψ (symplH V W (a w') (u w')) * f (a w' + u w')) = _
  rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.FockCompare.ThetaCont

end
