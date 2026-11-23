import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement

noncomputable section

namespace PositivityTheory.ThKCT.So

open NumberField GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_of_map (B : Base F E) (w : InfinitePlace F) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (hJ : (J.map (B.emb w).1).det ≠ 0) : J.det ≠ 0 := fun h0 =>
  hJ (((RingHom.map_det _ J).symm.trans (congrArg _ h0)).trans (map_zero _))

theorem det_herm {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact det_ne_of_map B w _ (GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w))

theorem det_skew {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact det_ne_of_map B w _ fun h0 =>
    GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w) (by rw [Matrix.det_smul, h0, mul_zero])

theorem _root_.PositivityTheory.ThKCT.soStab_of : SoStab := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP x
  exact PositivityTheory.KCo.so_stable M hP.base.cm hP.base.std (det_herm hP.herm) (det_skew hP.skew) hP.good
    (IsUWeilPair.isUSplitting hP.weil).toIsSplitting B.τ₁ x

end PositivityTheory.ThKCT.So

end
