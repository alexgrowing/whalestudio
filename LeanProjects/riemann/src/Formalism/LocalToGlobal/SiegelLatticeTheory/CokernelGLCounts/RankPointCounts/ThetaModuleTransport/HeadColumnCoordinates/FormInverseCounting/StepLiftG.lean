import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SecondProjDiagonalEmbed

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

def StepLiftG : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (_hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ →
    ∀ γ : IsoMbe Z₁.Z Z₂.Z, ∃ (P Q P' : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R) (γ' : IsoMbe Zσ₁.Z Zσ₂.Z),
      (∀ v, γ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (P.mulVec v)) ∧
      (∀ w, γ'.1 (Submodule.Quotient.mk w) = Submodule.Quotient.mk (P'.mulVec w)) ∧
      P * Z₁.Z = Z₂.Z * Q ∧
      (∀ i, P i (Fin.last r) = if i = Fin.last r then 1 else 0) ∧
      (∀ j, Q (Fin.last r) j = if j = Fin.last r then 1 else 0) ∧
      ∀ w : Fin (r + 1) → M.R, ∃ m : Fin (r + 1) → M.R, m (Fin.last r) = 0 ∧
        ∀ i, ∑ j, M.L.cj (Q j i : E) * ((P'.mulVec w) j : E) = (w i : E) + ((Zσ₁.Z.mulVec m) i : E)

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
