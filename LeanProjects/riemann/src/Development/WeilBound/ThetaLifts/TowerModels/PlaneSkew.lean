import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm
import Development.WeilBound.ThetaLifts.TowerModels.PlaneMain

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem planeHerm : PlaneHerm := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  simp only [Pln.isHerm_iff] at hY ⊢
  exact Pln.exists_plane hB (Or.inl rfl) (by simp) (fun e => by simp) _ isIntegral_one
    (fun v => Pln.val_le_one_of_intE (B.τ v)) n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n

theorem planeSkew : PlaneSkew := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  simp only [Pln.isSkew_iff] at hY ⊢
  exact Pln.exists_plane hB (Or.inr rfl) (by simp) (fun e => by simp) _ Pln.one_mem_codE
    (fun v => Pln.val_le_one_of_codE hB.cm hB.std (hB.psiP v v.2) (B.τ v)) n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n

end PositivityTheory.ThKG.Tow

end
