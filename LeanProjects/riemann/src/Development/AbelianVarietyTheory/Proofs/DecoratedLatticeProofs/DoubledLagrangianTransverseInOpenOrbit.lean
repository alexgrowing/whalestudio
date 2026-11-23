import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecPairVecDiag
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

namespace GlobalTheory.Core.Rk.Dich

theorem exists_mem_siegel_of_diagSnd : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → x = 0) → ∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V := by
  intro D V γ hγ γi hγi hinj
  have hinc : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  obtain ⟨g, hg, hg1, hg2⟩ := exists_rat (dblSp V) hγ
  have hγi' : γi = (g⁻¹).1 := Matrix.map_injective hinc (hγi.symm.trans hg2)
  have hgγ : g.1 * γi = 1 := by rw [hγi']; exact Units.mul_inv g
  have hgi : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * dblGram finSumFinEquiv V.gram * γi =
      dblGram finSumFinEquiv V.gram := by
    have h := inv_mem hg
    change Formalism.UG.cT _ (g⁻¹).1 * (dblSp V).gram * (g⁻¹).1 = (dblSp V).gram at h
    rw [gram_hdbl] at h
    rw [hγi']; exact h
  have hiso := isotropic_diag hgi
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ
  set P := leviMat finSumFinEquiv γi with hP
  set Q := diagSnd γi with hQ
  have hQu : IsUnit Q := Matrix.mulVec_injective_iff_isUnit.1 fun x y h =>
    sub_eq_zero.1 (hinj _ (by rw [Matrix.mulVec_sub, h, sub_self]))
  have hQ1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hQu)
  have hcT : ∀ M N : Matrix (Fin V.rank) (Fin V.rank) D.host.E,
      Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
    intro M N; simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcT1 : Formalism.UG.cT σ Q⁻¹ * Formalism.UG.cT σ Q = 1 := by
    rw [← hcT, hQ1]; simp [Formalism.UG.cT]
  have hδ : Formalism.UG.cT σ (P * Q⁻¹) * V.gram * (P * Q⁻¹) = V.gram := by
    calc Formalism.UG.cT σ (P * Q⁻¹) * V.gram * (P * Q⁻¹)
        = Formalism.UG.cT σ Q⁻¹ * (Formalism.UG.cT σ P * V.gram * P) * Q⁻¹ := by simp only [hcT, Matrix.mul_assoc]
      _ = V.gram := by
        rw [hiso]; simp only [Matrix.mul_assoc]
        rw [hQ1, Matrix.mul_one, ← Matrix.mul_assoc, hcT1, Matrix.one_mul]
  have hdet : IsUnit (P * Q⁻¹).det := by
    have h := congrArg Matrix.det hδ
    rw [Matrix.det_mul, Matrix.det_mul] at h
    have hJ : IsUnit V.gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V
    rw [← h] at hJ
    exact isUnit_of_mul_isUnit_right hJ
  set d : GL (Fin V.rank) D.host.E := ((Matrix.isUnit_iff_isUnit_det (P * Q⁻¹)).2 hdet).unit with hd
  have hdv : d.1 = P * Q⁻¹ := rfl
  have hdU : d ∈ Formalism.UG.UJ σ V.gram := by
    change Formalism.UG.cT σ d.1 * V.gram * d.1 = V.gram
    rw [hdv]; exact hδ
  obtain ⟨δ', hδ'Q, hδ'⟩ := exists_of_rat V hdU
  refine ⟨δ'⁻¹, inv_mem hδ'Q, ?_⟩
  rw [show (io V (δ'⁻¹, 1))⁻¹ = io V (δ', 1) by rw [← map_inv, Prod.inv_mk, inv_inv, inv_one]]
  have hm : (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (δ', 1))).1 =
      (g.1 * blkMat finSumFinEquiv (P * Q⁻¹) 1).map (incA D) := by
    rw [map_mul, Units.val_mul, hg1, matHom_io, val_blkGL, hδ', map_one, Units.val_one, hdv]
    conv_rhs => rw [Matrix.map_mul, blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  refine mem_siegelOf.2 ?_
  change KeepsDiag finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (δ', 1))).1
  rw [hm]
  refine KeepsDiag.map _ (keepsDiag_of_mulVec fun w hw => ?_) _
  obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hw
  rw [← Matrix.mulVec_mulVec, blkMat_mulVec, Matrix.one_mulVec]
  have h2 : pairVec finSumFinEquiv ((P * Q⁻¹) *ᵥ x) x = γi *ᵥ pairVec finSumFinEquiv (Q⁻¹ *ᵥ x) (Q⁻¹ *ᵥ x) := by
    rw [mulVec_pairVec_diag, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec]
  rw [h2, Matrix.mulVec_mulVec, hgγ, Matrix.one_mulVec]
  exact (pairVec_mem_diagSub _).2 rfl

end GlobalTheory.Core.Rk.Dich
