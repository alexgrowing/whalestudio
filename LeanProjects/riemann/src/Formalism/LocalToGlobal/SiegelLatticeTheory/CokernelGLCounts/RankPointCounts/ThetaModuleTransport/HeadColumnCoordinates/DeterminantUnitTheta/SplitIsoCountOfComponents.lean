import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.HeadMapCj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.Development

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

def StepZsig0 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g → ∀ (r : ℕ) (T T' : F), T ∈ 𝒪[F] →
    (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) → (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
    ∀ (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
      Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T' → IsUnit Zh.det →
      (Zh.submatrix Fin.castSucc Fin.castSucc).det = 0 →
      (∃ TT : M.R, g.e (TT : E) = (T, T')) ∧ IsUnit (Z.map M.R.subtype).det ∧
      ∃ Zσ : M.Mat (r + 1), Zσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T'

def SplitIsometryCountIntegral : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (T T' : F), T ∈ 𝒪[F] → (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    (Zh₁.submatrix Fin.castSucc Fin.castSucc).det = 0 → (Zh₂.submatrix Fin.castSucc Fin.castSucc).det = 0 →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card (IsoMbe Z₁ Z₂)

theorem splitIsoCount_of_components (hZ : StepZsig0) (h0 : StepSplit) (h1 : FirstIsometryForward) (h2 : FirstIsometryBackward) (h3 : FirstIsometryUniqueness)
    (h4 : StepDu) (h5 : StepDuU) : SplitIsometryCountIntegral := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT huv hc Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ s₁ s₂
  obtain ⟨⟨TT, hTT⟩, hZ₁, Zσ₁, hσ₁⟩ := hZ F E M g hs r T T' hT huv hc Zh₁ Z₁ e₁ u₁ s₁
  obtain ⟨_, hZ₂, Zσ₂, hσ₂⟩ := hZ F E M g hs r T T' hT huv hc Zh₂ Z₂ e₂ u₂ s₂
  let W₁ : M.Mat (r + 1) := ⟨Z₁, hZ₁⟩
  let W₂ : M.Mat (r + 1) := ⟨Z₂, hZ₂⟩
  have gh : ∀ {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {W Wσ : M.Mat (r + 1)},
      W.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T' →
      Wσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T' →
      IsUnit Zh.det → (Zh.submatrix Fin.castSucc Fin.castSucc).det = 0 →
      GHyp M g T T' TT Zh W Wσ := by
    intro Zh W Wσ hW hWσ hu hz
    refine ⟨huv, hc, hTT, hW, hWσ, hu, ?_⟩
    rw [hz, map_zero, zero_mul, mul_zero, sub_zero]
    exact hu.mul (hu.map M.L.cj)
  have G₁ : GHyp M g T T' TT Zh₁ W₁ Zσ₁ := gh e₁ hσ₁ u₁ s₁
  have G₂ : GHyp M g T T' TT Zh₂ W₂ Zσ₂ := gh e₂ hσ₂ u₂ s₂
  have K : KapEq Zh₁ Zh₂ := by
    unfold KapEq
    rw [s₁, s₂, mul_zero, mul_zero]
  have Gσ₁ := gHyp_cj G₁
  have Gσ₂ := gHyp_cj G₂
  have Kσ := kapEq_cj (M := M) K
  rw [h0 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K]
  refine Nat.card_eq_of_bijective
    (fun p => (h1 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K p.1.1 p.2.1 p.2.2.2.1).choose)
    ⟨?_, ?_⟩
  · intro p p' hpp
    have i1 := (h1 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K p.1.1 p.2.1 p.2.2.2.1).choose_spec
    have i2 := (h1 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K p'.1.1 p'.2.1 p'.2.2.2.1).choose_spec
    simp only at hpp
    rw [hpp] at i1
    have q1 : p.1.1 = p'.1.1 := ind_det hs _ _ _ i1 i2
    have hb := p'.2.2.2.2.2
    rw [← q1] at hb
    have q2 : p.1.2 = p'.1.2 :=
      h5 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K p.1.1 p.1.2 p'.1.2 p.2.2.2.2.2 hb
    exact Subtype.ext (Prod.ext q1 q2)
  · intro γ
    obtain ⟨θ₁, o₁, m₁, i₁⟩ := h2 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K γ
    obtain ⟨γ', hγ'⟩ := h4 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K γ
    obtain ⟨θ₂, o₂, m₂, i₂⟩ := h2 F E M g hs r T T' TT (Zh₁.map M.L.cj) (Zh₂.map M.L.cj)
      Zσ₁ Zσ₂ W₁ W₂ Gσ₁ Gσ₂ Kσ γ'
    refine ⟨⟨(θ₁, θ₂), o₁, o₂, m₁, m₂, hγ' θ₁ θ₂ i₁ i₂⟩, ?_⟩
    exact h3 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K θ₁ _ γ
      (h1 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K θ₁ o₁ m₁).choose_spec i₁

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
