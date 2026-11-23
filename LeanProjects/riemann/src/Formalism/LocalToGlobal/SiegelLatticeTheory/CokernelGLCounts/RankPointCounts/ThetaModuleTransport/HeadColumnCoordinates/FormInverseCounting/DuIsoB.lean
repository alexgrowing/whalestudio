import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SecondProjIotaOneEqZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GSteps

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem isoB_of (hs : M.split = some g) (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    {Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)} {TT : M.R}
    (hG₁ : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₁ (algebraMap F E T)
      (algebraMap F E T')).det)
    (hG₂ : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₂ (algebraMap F E T)
      (algebraMap F E T')).det)
    (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (h : ∀ l l₂ w w₂ : Fin (r + 1) → M.R, θ₁ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂ →
      θ₂ (mk1 hs Zσ₁ TT w) = mk1 hs Zσ₂ TT w₂ →
      dotProduct (uV g l₂) (Matrix.mulVec (gHat g Zh₂ T T')⁻¹ (uV g w₂)) -
        dotProduct (uV g l) (Matrix.mulVec (gHat g Zh₁ T T')⁻¹ (uV g w)) ∈ 𝒪[F]) :
    IsoB hs Zh₁ Zh₂ T T' θ₁ θ₂ := by
  intro l l₂ w w₂ hl hw
  apply mem_O_of_comp g
  · rw [map_sub, Prod.fst_sub, ← firstProj_apply, ← firstProj_apply, splitForm_iota_firstProj hs Zh₂ T T' hG₂,
      splitForm_iota_firstProj hs Zh₁ T T' hG₁]
    exact h l l₂ w w₂ hl hw
  · rw [map_sub, Prod.snd_sub, ← secondProj_apply, ← secondProj_apply, splitForm_iota_secondProj, splitForm_iota_secondProj, sub_zero]
    exact zero_mem _

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
