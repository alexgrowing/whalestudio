import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpM

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section comp

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def dcomp (T0 : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) : B.DiffOp k r Wp Wq :=
  Θ.map fun T =>
    { coef := fun x => (T0.coef x).comp (T.coef x)
      coefAdj := fun x => (T.coefAdj x).comp (T0.coefAdj x)
      word := T.word
      word_lie := T.word_lie
      adj_id := fun x A B => by
        simp only [ContinuousLinearMap.comp_apply]
        rw [T0.adj_id, T.adj_id] }

theorem opApply_dcomp (T0 : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.opApply (dcomp T0 Θ) F g = T0.coef g (B.opApply Θ F g) := by
  unfold B.opApply dcomp
  rw [map_list_sum, List.map_map, List.map_map]
  rfl

def Good0 (D : B.RealPlaceData k r Wp Wq) (T0 : B.DTerm k r Wp Wq) : Prop :=
  T0.word = [] ∧ B.CkOn ⊤ (B.GPos D) T0.coef ∧ B.CkOn ⊤ (B.GPos D) T0.coefAdj ∧
    (∀ p, D.inSS p → ∀ g ∈ B.GPos D, ∀ A : Wq →L[ℂ] Wp,
      T0.coef g ((D.π (Matrix.of p.1.1)).comp (A.comp (D.π' (Matrix.of p.2.1)⁻¹))) =
        (D.π (Matrix.of p.1.1)).comp ((T0.coef (B.sgs p g) A).comp (D.π' (Matrix.of p.2.1)⁻¹))) ∧
    ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ C d : ℝ, 0 ≤ d ∧ ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) →
      (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m → ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g →
        ‖B.dLR u v T0.coef g‖ ≤ C * B.gN g ^ d ∧ ‖B.dLR u v T0.coefAdj g‖ ≤ C * B.gN g ^ d

end comp

def RDSOpRGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (D : B.RealPlaceData k r Wp Wq)
    (Y σ : ℂ), ∃ Θ : B.DiffOp k r Wp Wq, OpProp1 D Θ ∧
      ∀ J : B.Mat k r → (Wq →L[ℂ] Wp), J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') →
        ∀ x ∈ DomR k r D.z D.z', resG k r (Fin.last r) (B.opApply Θ J) x.1 x.2 =
          σ • CutMP.rhGrp k r D.z D.z' Y (resG k r (Fin.last r) J) x.1 x.2

def RDSOpRvGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (D : B.RealPlaceData k r Wp Wq)
    (Y σ : ℂ), ∃ Θ : B.DiffOp k r Wp Wq, OpProp1 D Θ ∧
      ∀ J : B.Mat k r → (Wq →L[ℂ] Wp), J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') →
        ∀ x ∈ DomR k r D.z D.z', resG k r (Fin.last r) (B.opApply Θ J) x.1 x.2 =
          σ • CutMP.rhvGrp k r D.z D.z' Y (resG k r (Fin.last r) J) x.1 x.2

def RDSOpX : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ Y : ℂ, Y ∈ st.inv → ∃ T0 : B.DTerm P.k P.r Wp Wq, Good0 D T0 ∧
      ∀ (Ψ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z',
        (((GiR L * st.xi Y).1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          T0.coef (wCell P.k P.r (Fin.last P.r) x.1 * x.2) ((Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)

def RDSRhR : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → 0 < P.r →
    ∀ Y : ℂ, star Y = Y → ∃ σ : ℂ, ∀ J : B.Mat P.k P.r → (Wq →L[ℂ] Wp), J ∈ Q.FFl P.k P.r z z' π π' 0 (JF.Om P.k P.r z z') →
      ∀ Φ : RadSp P.k P.r z z' π π',
        (∀ x ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) J x.1 x.2) →
        ∀ x ∈ DomR P.k P.r z z',
          (((RhR L st Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
            σ • CutMP.rhGrp P.k P.r z z' Y (resG P.k P.r (Fin.last P.r) J) x.1 x.2

def RDSRhvR : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → 0 < P.r →
    ∀ Y : ℂ, star Y = Y → ∃ σ : ℂ, ∀ J : B.Mat P.k P.r → (Wq →L[ℂ] Wp), J ∈ Q.FFl P.k P.r z z' π π' 0 (JF.Om P.k P.r z z') →
      ∀ Φ : RadSp P.k P.r z z' π π',
        (∀ x ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) J x.1 x.2) →
        ∀ x ∈ DomR P.k P.r z z',
          (((RhvR L st Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
            σ • CutMP.rhvGrp P.k P.r z z' Y (resG P.k P.r (Fin.last P.r) J) x.1 x.2

def RDSComp0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (D : B.RealPlaceData k r Wp Wq)
    (T0 : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq), Good0 D T0 → OpProp1 D Θ → OpProp1 D (dcomp T0 Θ)

theorem rDSOpR_of_parts (hG : RDSOpRGrp) (hX : RDSOpX) (hR : RDSRhR) (hC : RDSComp0) : RDSOpR := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hY _ hY0 _
  obtain ⟨σ, hσ⟩ := hR Wp Wq P z z' π π' X μ L st l0 hD hl1 hl2 hr Y hY
  obtain ⟨T0, hT0, hT0e⟩ := hX Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hY0
  subst hz hz' hπ hπ'
  obtain ⟨Θ, hΘ, hΘe⟩ := hG Wp Wq P.k P.r D Y σ
  refine ⟨dcomp T0 Θ, hC Wp Wq P.k P.r D T0 Θ hT0 hΘ, ?_⟩
  intro J hJ Φ hΦ x hx
  have e1 : (((GiR L * st.xi Y * RhR L st Y).1 Φ : RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp))
      x.1 x.2 = (((GiR L * st.xi Y).1 ((RhR L st Y).1 Φ) : RadSp P.k P.r D.z D.z' D.π D.π') :
        Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := rfl
  rw [e1, hT0e _ x hx, hσ J hJ Φ hΦ x hx, ← hΘe J hJ x hx]
  simp only [resG, opApply_dcomp, map_smul]

theorem rDSOpRv_of_parts (hG : RDSOpRvGrp) (hX : RDSOpX) (hR : RDSRhvR) (hC : RDSComp0) : RDSOpRv := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hY _ _ hY1
  have hY' : star (Y + 1) = Y + 1 := by rw [star_add, hY, star_one]
  obtain ⟨σ, hσ⟩ := hR Wp Wq P z z' π π' X μ L st l0 hD hl1 hl2 hr (Y + 1) hY'
  obtain ⟨T0, hT0, hT0e⟩ := hX Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr (Y + 1) hY1
  subst hz hz' hπ hπ'
  obtain ⟨Θ, hΘ, hΘe⟩ := hG Wp Wq P.k P.r D (Y + 1) σ
  refine ⟨dcomp T0 Θ, hC Wp Wq P.k P.r D T0 Θ hT0 hΘ, ?_⟩
  intro J hJ Φ hΦ x hx
  have e1 : (((GiR L * st.xi (Y + 1) * RhvR L st (Y + 1)).1 Φ : RadSp P.k P.r D.z D.z' D.π D.π') :
      Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = (((GiR L * st.xi (Y + 1)).1 ((RhvR L st (Y + 1)).1 Φ) :
        RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := rfl
  rw [e1, hT0e _ x hx, hσ J hJ Φ hΦ x hx, ← hΘe J hJ x hx]
  simp only [resG, opApply_dcomp, map_smul]

end Formalism.FourierDecayAlt.P.CutSE
