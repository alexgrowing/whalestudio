import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.DetEqEllUB

noncomputable section

open scoped Matrix

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem cornerU_holds (M : Model F E) (r : ℕ) : CornerU M r := by
  intro Z₁ Zh₂ Y₁ Y₂ be₁ be₂ al₁ al₂ hY hb hdet hφ
  obtain ⟨⟨φ, hφb, hφl⟩⟩ := hφ
  have hsub₁ : (Z₁.Z.map M.R.subtype).submatrix Fin.castSucc Fin.castSucc = Y₁.Z.map M.R.subtype :=
    head_map (fun a b => (hY a b).1)
  have hsub₂ : Zh₂.submatrix Fin.castSucc Fin.castSucc = Y₂.Z.map M.R.subtype := by
    ext a b
    simp [(hY a b).2]
  have hu₁ : IsUnit (Y₁.Z.map M.R.subtype).det := Y₁.unit
  have hu₂ : IsUnit (Y₂.Z.map M.R.subtype).det := Y₂.unit
  have h1 : (Z₁.Z.map M.R.subtype).det =
      (Y₁.Z.map M.R.subtype).det * ((Z₁.Z (Fin.last r) (Fin.last r) : E) - lamE Y₁ al₁ be₁) := by
    rw [det_schur _ (by rw [hsub₁]; exact hu₁), hsub₁, lamE_apply]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    have hv : (fun j : Fin r => (Z₁.Z.map M.R.subtype) j.castSucc (Fin.last r)) = fun j => ((be₁ j : M.R) : E) := by
      funext j
      simp [(hb j).1]
    rw [hv]
    simp [(hb i).2.2.1]
  have h2 : Zh₂.det = (Y₂.Z.map M.R.subtype).det * (Zh₂ (Fin.last r) (Fin.last r) - lamE Y₂ al₂ be₂) := by
    rw [det_schur _ (by rw [hsub₂]; exact hu₂), hsub₂, lamE_apply]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    have hv : (fun j : Fin r => Zh₂ j.castSucc (Fin.last r)) = fun j => ((be₂ j : M.R) : E) := by
      funext j
      rw [(hb j).2.1]
    rw [hv, (hb i).2.2.2]
  have hh : headDet M Z₁.Z = (Y₁.Z.map M.R.subtype).det := by
    unfold headDet
    rw [hsub₁]
  rw [hh, h1, h2, hsub₂] at hdet
  have hkey : Zh₂ (Fin.last r) (Fin.last r) - lamE Y₂ al₂ be₂ =
      (Z₁.Z (Fin.last r) (Fin.last r) : E) - lamE Y₁ al₁ be₁ := by
    have hu := hu₁.mul hu₂
    apply hu.mul_left_cancel
    linear_combination hdet
  have hq := hφl (Submodule.Quotient.mk be₁)
  rw [hφb, linQ_mk, linQ_mk] at hq
  have hmem : lamE Y₂ al₂ be₂ - lamE Y₁ al₁ be₁ ∈ M.Rsub := (Submodule.Quotient.eq _).1 hq
  obtain ⟨x, hx⟩ := hmem
  have hc : Zh₂ (Fin.last r) (Fin.last r) =
      (Z₁.Z (Fin.last r) (Fin.last r) : E) + (lamE Y₂ al₂ be₂ - lamE Y₁ al₁ be₁) := by
    linear_combination hkey
  rw [hc, ← hx]
  exact M.R.add_mem (Z₁.Z (Fin.last r) (Fin.last r)).2 x.2

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL
