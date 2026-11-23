import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.CardThetaGCScale
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondProjConjAlgebra

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

def AlgGAllT : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (T T' : F), (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det =
      Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det →
    IsUnit (Zh₁.det * M.L.cj Zh₁.det - algebraMap F E (T * T') *
      ((Zh₁.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₁.submatrix Fin.castSucc Fin.castSucc).det)) →
    IsUnit (Zh₂.det * M.L.cj Zh₂.det - algebraMap F E (T * T') *
      ((Zh₂.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₂.submatrix Fin.castSucc Fin.castSucc).det)) →
    T ∈ 𝒪[F] →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card (IsoMbe Z₁ Z₂)

section Fin

variable {E : Type} [CommRing E] {r : ℕ}

theorem det_dlast (α : E) : (dlast r α).det = α := by
  rw [dlast, Matrix.det_diagonal, Finset.prod_eq_single (Fin.last r)]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem head_dlast (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (α : E) :
    (Zh * dlast r α).submatrix Fin.castSucc Fin.castSucc = Zh.submatrix Fin.castSucc Fin.castSucc := by
  ext a b
  simp [dlast, Matrix.mul_diagonal, Fin.castSucc_ne_last]

end Fin

theorem algGAllT_holds : AlgGAllT := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT hq Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ hrel hG₁ hG₂ hT0
  obtain ⟨α, hα, hαO, hβO, Z₁', Z₂', e₁', e₂', d₁, d₂, s₁, s₂, hcard⟩ :=
    Formalism.L2.SG.LocalCountModules.AlgGSplit.scaleChoice_holds F E M g hs r T T' hT hq hT0 Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ hrel
  have hαu : IsUnit α := ⟨⟨α, M.L.cj α, hα, by rw [mul_comm]; exact hα⟩, rfl⟩
  have hcj : ∀ x : E, (M.L.cj : E →+* E) ((M.L.cj : E →+* E) x) = x := M.L.cj_cj
  have hH : ScHyp M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (algebraMap F E T) (algebraMap F E T') α :=
    { cjcj := hcj
      cjO := fun x hx => cj_mem_O M.L hx
      qic := AlgEquiv.commutes _ _
      Tc := AlgEquiv.commutes _ _
      T'c := AlgEquiv.commutes _ _
      αO := hαO
      αn := hα
      βO := hβO }
  have hqq : algebraMap F E (g.q : F) * algebraMap F E ((g.q : F)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (q_ne g), map_one]
  have hqO : algebraMap F E (g.q : F) ∈ M.L.O :=
    mem_O_of_comp g _ (by rw [AlgEquiv.commutes]; exact g.q.2) (by rw [AlgEquiv.commutes]; exact g.q.2)
  have hdet : ∀ Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Zh * dlast r α).det = Zh.det * α := fun Zh => by
    rw [Matrix.det_mul, det_dlast]
  have hN : ∀ Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (Zh * dlast r α).det * M.L.cj (Zh * dlast r α).det = Zh.det * M.L.cj Zh.det := fun Zh => by
    rw [hdet, map_mul]; linear_combination (Zh.det * M.L.cj Zh.det) * hα
  have key := Formalism.L2.SG.LocalCountModules.AlgGSplit.algGAllNS_holds F E M g hs r T T' hT hq (Zh₁ * dlast r α) (Zh₂ * dlast r α) Z₁' Z₂'
    e₁' e₂' (by rw [hdet]; exact u₁.mul hαu) (by rw [hdet]; exact u₂.mul hαu)
    (by rw [hdet, hdet, head_dlast, head_dlast]; linear_combination α * hrel)
    (by rw [hN, head_dlast]; exact hG₁) (by rw [hN, head_dlast]; exact hG₂) hT0 d₁ d₂ s₁ s₂
  rw [card_thetaGC_scale _ hH hqq hqO, hcard] at key
  exact key

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
