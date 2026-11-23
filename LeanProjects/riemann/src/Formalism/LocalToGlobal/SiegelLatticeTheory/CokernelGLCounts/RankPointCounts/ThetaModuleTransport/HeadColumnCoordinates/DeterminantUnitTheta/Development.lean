import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ThetaGC

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section Steps

def DetG : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F),
    (Zh.submatrix Fin.castSucc Fin.castSucc).det = 0 →
    IsUnit (HermSp.ZZplusOf M Zh T T').det → IsUnit Zh.det

def CoordG : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r n : ℕ) (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    H.Dl t₁.f t₁.f' r = 0 → IsUnit (H.Dl f₂ f₂' (r + 1)) →
    (∀ a b, HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a b ∈ M.R) →
    Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') =
      Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t₁.f t₁.f') (H.Zhat f₂ f₂')
        (algebraMap F E t₁.T) (algebraMap F E t₁.T'))

def SplitIsometryCountVanishes : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (T T' : F), (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    (Zh₁.submatrix Fin.castSucc Fin.castSucc).det = 0 → (Zh₂.submatrix Fin.castSucc Fin.castSucc).det = 0 →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card (IsoMbe Z₁ Z₂)

end Steps

section Deriv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem thetaMbe0G_of (h0 : DetG) (h1 : CoordG) (h2 : SplitIsometryCountVanishes) (M : Model F E) (r n : ℕ) :
    ThetaMbe0 M r n true := by
  intro hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hDl Z₁ Z₂ hZ₁ hZ₂
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hmode
  have hminor : ∀ f f' : Fin (r + 1) → V,
      ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det = H.Dl f f' r := by
    intro f f'
    unfold HermSp.Dl
    rw [dif_pos (Nat.le_succ r)]
    rfl
  have hfull : ∀ f f' : Fin (r + 1) → V, H.Dl f f' (r + 1) = (H.Zhat f f').det := by
    intro f f'
    unfold HermSp.Dl
    rw [dif_pos le_rfl]
    rfl
  have hyp' := hyp
  obtain ⟨⟨hterm, _⟩, _, _, hid, _, _⟩ := hyp'
  obtain ⟨_, _, _, hD1, _, hsp⟩ := hterm
  obtain ⟨hTu, hTT, _⟩ := hsp g hg
  have hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1) :=
    hid.2.2.2.2.2
  rw [hDl, zero_mul] at hrel
  have hD2r : H.Dl f₂ f₂' r = 0 := hD1.mul_left_eq_zero.mp hrel.symm
  have hZ₁' : Z₁.Z.map M.R.subtype = HermSp.ZZplusOf M (H.Zhat t₁.f t₁.f') t₁.T t₁.T' := hZ₁
  have hU₂ : IsUnit (HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T').det := hZ₂ ▸ Z₂.unit
  have hm₁ : ((H.Zhat t₁.f t₁.f').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [hminor]; exact hDl
  have hm₂ : ((H.Zhat f₂ f₂').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [hminor]; exact hD2r
  have hd₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← hfull]; exact hD1
  have hd₂ : IsUnit (H.Zhat f₂ f₂').det := h0 F E M g hg r _ t₁.T t₁.T' hm₂ hU₂
  have hR : ∀ a b, HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a b ∈ M.R := by
    intro a b
    rw [← hZ₂]
    exact (Z₂.Z a b).2
  have hc := h1 F E M g hg r n V H hn t₁ f₂ f₂' φ φ' hyp hDl (by rw [hfull]; exact hd₂) hR
  rw [hc]
  exact h2 F E M g hg r t₁.T t₁.T' hTu hTT _ _ Z₁.Z Z₂.Z hZ₁' hZ₂ hd₁ hd₂ hm₁ hm₂

end Deriv

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
