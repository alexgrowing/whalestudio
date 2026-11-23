import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Common
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.SharpEquivApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section Coord

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

abbrev Ix (r : ℕ) : Type := Fin (r + 1) ⊕ Fin (r + 1)

def gramC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Matrix (Ix r) (Ix r) E :=
  Matrix.fromBlocks (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T else 0)
    (Matrix.of fun a b => cj (Z a b)) Z.transpose
    (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T' else 0)

def relC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Submodule O (Ix r → O) where
  carrier := {y | ∃ c : Ix r → O, ∀ j, (y j : E) = ∑ i, (c i : E) * gramC cj Z T T' i j}
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, fun j => ?_⟩
    simp only [Pi.add_apply, Subring.coe_add, hc j, hd j, add_mul, Finset.sum_add_distrib]
  zero_mem' := ⟨0, fun j => by simp⟩
  smul_mem' := by
    rintro a y ⟨c, hc⟩
    refine ⟨a • c, fun j => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, hc j, Finset.mul_sum, mul_assoc]

abbrev DDc (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Type :=
  (Ix r → O) ⧸ relC O cj Z T T'

def formC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y W : Ix r → O) : E :=
  ∑ i, ∑ j, (Y i : E) * (gramC cj Z T T')⁻¹ i j * cj (W j)

def lamC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (y : Fin (r + 1) → E) : E :=
  (Z⁻¹.mulVec y) (Fin.last r)

def lamStarC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (y : Fin (r + 1) → E) : E :=
  ∑ b, cj (Z⁻¹ b (Fin.last r)) * y b

def GamC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Set (DDc O cj Z T T' × (E × E)) :=
  {p | ∃ Y : Ix r → O, (∀ a : Fin r, Y (Sum.inl a.castSucc) = 0) ∧
    p = (Submodule.Quotient.mk Y, ((Y (Sum.inl (Fin.last r)) : E),
      lamStarC cj Z (fun b => (Y (Sum.inr b) : E))))}

def GamC' (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Set (DDc O cj Z T T' × (E × E)) :=
  {p | ∃ Y : Ix r → O, (∀ b : Fin r, Y (Sum.inr b.castSucc) = 0) ∧
    p = (Submodule.Quotient.mk Y, (lamC Z (fun a => (Y (Sum.inl a) : E)),
      (Y (Sum.inr (Fin.last r)) : E)))}

def ThetaC (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) :
    Set (DDc O cj Z₁ T T' ≃ₗ[O] DDc O cj Z₂ T T') :=
  {θ | (∀ Y W Y₂ W₂ : Ix r → O, θ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₂ →
      θ (Submodule.Quotient.mk W) = Submodule.Quotient.mk W₂ →
      formC O cj Z₂ T T' Y₂ W₂ - formC O cj Z₁ T T' Y W ∈ O) ∧
    (fun p => (θ p.1, p.2)) '' GamC O cj Z₁ T T' = GamC O cj Z₂ T T' ∧
    (fun p => (θ p.1, p.2)) '' GamC' O cj Z₁ T T' = GamC' O cj Z₂ T T'}

end Coord

section Steps

def CoordL : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → M.split = none →
  ∀ (r n : ℕ) (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    H.Dl t₁.f t₁.f' r = 0 → IsUnit (H.Dl f₂ f₂' (r + 1)) →
    (∀ a b, H.Zhat f₂ f₂' a b ∈ M.L.O) →
    Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') =
      Nat.card (ThetaC M.L.O (M.L.cj : E →+* E) (H.Zhat t₁.f t₁.f') (H.Zhat f₂ f₂')
        (algebraMap F E t₁.T) (algebraMap F E t₁.T'))

def UnramifiedIsoCountZero : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    (∀ x ∈ O, cj x ∈ O) →
  ∀ (r : ℕ) (T T' : E), T ∈ O → T' ∈ O → cj T = T → cj T' = T' →
  ∀ (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    ((Z₁.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    ((Z₂.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    IsUnit (gramC cj (Z₁.map O.subtype) T T').det → IsUnit (gramC cj (Z₂.map O.subtype) T T').det →
    Nat.card (ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) T T') = Nat.card (IsoMbe Z₁ Z₂)

end Steps

section Deriv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem R_eq_O (hs : M.split = none) : M.R = M.L.O := by
  unfold Model.R; rw [hs]

theorem dl_full (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  unfold HermSp.Dl
  rw [dif_pos le_rfl]
  congr 1

theorem gramC_eq (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F)
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') :
    gramC (M.L.cj : E →+* E) (H.Zhat f f') (algebraMap F E T) (algebraMap F E T') =
      (H.gram (Sum.elim f f')).transpose := by
  rw [gram_eq_fromBlocks H f f' T T' hF hF', Matrix.fromBlocks_transpose]
  ext (a | a) (b | b) <;> simp [gramC, cornerM, and_comm]

theorem unit_gramC (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F)
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD1 : IsUnit (H.Dl f f' (r + 1))) (hD0 : H.Dl f f' r = 0) :
    IsUnit (gramC (M.L.cj : E →+* E) (H.Zhat f f') (algebraMap F E T) (algebraMap F E T')).det := by
  rw [gramC_eq H f f' T T' hF hF', Matrix.det_transpose]
  obtain ⟨s, hs, hdet⟩ := gram_det H f f' T T' hF hF' hD1
  have hGd : IsUnit (H.Gdet f f' T T') := by
    unfold HermSp.Gdet HermSp.normE
    rw [hD0, map_zero, mul_zero, mul_zero, sub_zero]
    exact hD1.mul (hD1.map M.L.cj)
  have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
  have : (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' * s := by
    rw [← hdet, mul_assoc, hs, mul_one]
  rw [this]
  exact hGd.mul hsu

theorem thetaMbe0_L_of (h1 : CoordL) (h2 : UnramifiedIsoCountZero) :
    Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbe0 M r n false) := by
  intro F _ _ _ E _ _ _ _ M hOK r n hmode
  obtain ⟨L, sp, mu⟩ := M
  cases sp with
  | some g => simp at hmode
  | none =>
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂
  have hs : (⟨L, none, mu⟩ : Model F E).split = none := rfl
  have z₁ : Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype = H.Zhat t₁.f t₁.f' := by
    rw [e₁]; exact zzplusOf_none hs _ _ _
  have z₂ : Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype = H.Zhat f₂ f₂' := by
    rw [e₂]; exact zzplusOf_none hs _ _ _
  have hD2 : H.Dl f₂ f₂' r = 0 := dl_zero_two hyp hD
  have hU1 : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := dl_succ_unit hyp
  have hU2 : IsUnit (H.Dl f₂ f₂' (r + 1)) := by rw [dl_full, ← z₂]; exact Z₂.unit
  have hint : ∀ a b, H.Zhat f₂ f₂' a b ∈ L.O := by
    intro a b
    rw [← z₂]
    exact (Z₂.Z a b).2
  have hT : t₁.T ∈ 𝒪[F] := hyp.1.1.2.1.2.2.2.1
  have hT' : t₁.T' ∈ 𝒪[F] := hyp.1.1.2.2.1.2.2.2.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hyp.1.1.2.1.2.1, hyp.1.1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hyp.1.1.2.2.1.2.1, hyp.1.1.2.2.1.2.2.1⟩
  have hG1 := unit_gramC H _ _ _ _ hF₁ hF₁' hU1 hD
  have hG2 := unit_gramC H _ _ _ _ hyp.2.1 hyp.2.2.1 hU2 hD2
  have hh1 : ((Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [z₁, ← dl_eq_det]; exact hD
  have hh2 : ((Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [z₂, ← dl_eq_det]; exact hD2
  rw [← z₁] at hG1
  rw [← z₂] at hG2
  rw [h1 F E ⟨L, none, mu⟩ hOK hs r n V H hn t₁ f₂ f₂' φ φ' hyp hD hU2 hint, ← z₁, ← z₂]
  exact h2 E L.O (L.cj : E →+* E) (fun x => L.cj_cj x) (fun x hx => cj_mem_O L hx)
    r _ _ (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O L ⟨t₁.T, hT⟩) (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O L ⟨t₁.T', hT'⟩)
    (AlgEquiv.commutes _ _) (AlgEquiv.commutes _ _) Z₁.Z Z₂.Z Z₁.unit Z₂.unit hh1 hh2 hG1 hG2

end Deriv

end Formalism.L2.SG.LocalCountModules.LocCntCommon
