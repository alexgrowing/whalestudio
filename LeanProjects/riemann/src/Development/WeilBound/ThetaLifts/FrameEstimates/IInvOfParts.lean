import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.WeilBound.ThetaLifts.FrameEstimates.BlockForm
import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem topGroup_UA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) : IsTopologicalGroup (UA σ J) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin n) (AE F E)) := inferInstance
  exact Subgroup.instIsTopologicalGroupSubtypeMem _

theorem iInv_of_parts (hB : ThetaBasic) (hU : PositivityTheory.ThKF.Unimod) (hE : EpsOf) : IInv := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp Φ hΦ
  have hi := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1
  refine ⟨fun γ hγ h => ?_, fun g₀ => funext fun h => ?_, fun h h' => ?_⟩
  · simp only [Model.I]
    congr 1
    funext g
    simpa using hi 1 (one_mem _) γ hγ g h
  · obtain ⟨h1, -, h3⟩ := hU F E σ hp.base.cm n X.J 1 (fun i j => by simpa using hp.herm.herm i j)
      (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1.2
    have := topGroup_UA σ X.J
    have := h3 _ hp.good.haar
    have := hp.good.haar
    have : BorelSpace (UA σ X.J) := ⟨rfl⟩
    have e : ∀ g, theta om (om (g₀, 1) Φ) g h = theta om Φ (g * g₀) h := fun g => by
      simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [Model.I, e]
    exact PositivityTheory.ThKF.L2.integral_right hp.good.dom (fun g => theta om Φ g h)
      (fun γ hγ g => by simpa using hi γ hγ 1 (one_mem _) g h) g₀
  · simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem iInv_of (hB : ThetaBasic) : IInv := iInv_of_parts hB PositivityTheory.ThKF.unimodularity_holds epsOf_of

end PositivityTheory.ThKEst

end
