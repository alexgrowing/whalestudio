import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem exists_normOneAt_of_rank_one (D : D7) (L : HSp D) (v : GlobalTheory.FinPl.Pl D) (γ : GA D L) (hr : L.rank = 1)
    (hγ : γ ∈ grpAt L (· = v)) :
    ∃ c : AE D, NormOneAt v c ∧ NormOneAt v (cA D c) ∧
      Formalism.L2.Theta.mt L γ = c • (1 : Matrix (Fin L.rank) (Fin L.rank) (AE D)) := by
  haveI hs : Subsingleton (Fin L.rank) := ⟨fun a b => Fin.ext (by have := a.2; have := b.2; omega)⟩
  let i₀ : Fin L.rank := ⟨0, by omega⟩
  set c : AE D := Formalism.L2.Theta.mt L γ i₀ i₀ with hc
  have hmat : Formalism.L2.Theta.mt L γ = c • (1 : Matrix (Fin L.rank) (Fin L.rank) (AE D)) := by
    ext i j
    rw [Subsingleton.elim i i₀, Subsingleton.elim j i₀]
    simp [hc]
  have hid : c - 1 ∈ idAt D (· = v) := by
    have h := (GlobalTheory.IwaPlace.mem_congGrp_iff L _ γ).1 hγ i₀ i₀
    simpa [hc] using h

  have hu := congrFun (congrFun (GlobalTheory.MixModel.mt_unitary L γ) i₀) i₀
  simp only [Matrix.mul_apply, Fintype.sum_subsingleton _ i₀, GlobalTheory.MixModel.adj, GlobalTheory.MixModel.gA,
    GlobalTheory.MixModel.rat, Matrix.map_apply, Matrix.transpose_apply] at hu
  have hg : HSpace.gram L i₀ i₀ ≠ 0 := by
    have := GlobalTheory.MixModel.gram_isUnit_det L
    rw [Matrix.det_eq_elem_of_subsingleton _ i₀] at this
    exact this.ne_zero
  have hgu : IsUnit (incA D (HSpace.gram L i₀ i₀)) := (Ne.isUnit hg).map _
  have h1 : cA D c * c = 1 := by
    rw [← hc] at hu
    have : (cA D c * c) * incA D (HSpace.gram L i₀ i₀) = 1 * incA D (HSpace.gram L i₀ i₀) := by
      rw [one_mul]
      calc (cA D c * c) * incA D (HSpace.gram L i₀ i₀)
          = cA D c * (incA D (HSpace.gram L i₀ i₀) * c) := by ring
        _ = incA D (HSpace.gram L i₀ i₀) := hu
    exact hgu.mul_right_cancel this
  have h2 : c * cA D c = 1 := by rw [mul_comm]; exact h1
  refine ⟨c, ⟨h2, hid⟩, ⟨?_, ?_⟩, hmat⟩
  · rw [← map_mul, h2, map_one]
  · have : cA D c - 1 = -(cA D c) * (c - 1) := by
      linear_combination h1
    rw [this]
    exact Ideal.mul_mem_left _ _ hid

end GlobalTheory.Core.Mi.LatMatch
