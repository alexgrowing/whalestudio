import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.Equivar

theorem rmulM_emb {k r : ℕ} {t : Mat k r} (ht : IsUnit t.det) :
    MeasurableEmbedding (rmulM t : Mt k r → Mt k r) := by
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := rmulM t
      invFun := rmulM t⁻¹
      left_inv := fun x => Matrix.mul_nonsing_inv_cancel_right t (Matrix.of x) ht
      right_inv := fun x => Matrix.nonsing_inv_mul_cancel_right t (Matrix.of x) ht
      continuous_toFun := continuous_rmulM t
      continuous_invFun := continuous_rmulM t⁻¹ }
  exact e.measurableEmbedding

theorem integral_comp_both {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A A' : E →L[ℂ] E) (B B' : F →L[ℂ] F) (h1 : A.comp A' = 1) (h2 : A'.comp A = 1)
    (h3 : B.comp B' = 1) (h4 : B'.comp B = 1) (φ : X → (F →L[ℂ] E)) :
    ∫ x, A.comp ((φ x).comp B) ∂μ = A.comp ((∫ x, φ x ∂μ).comp B) := by
  have a1 : ∀ v, A (A' v) = v := fun v => congrArg (fun f : E →L[ℂ] E => f v) h1
  have a2 : ∀ v, A' (A v) = v := fun v => congrArg (fun f : E →L[ℂ] E => f v) h2
  have a3 : ∀ v, B (B' v) = v := fun v => congrArg (fun f : F →L[ℂ] F => f v) h3
  have a4 : ∀ v, B' (B v) = v := fun v => congrArg (fun f : F →L[ℂ] F => f v) h4
  let L : (F →L[ℂ] E) ≃L[ℂ] (F →L[ℂ] E) := ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.compL ℂ F E E A).comp ((ContinuousLinearMap.compL ℂ F F E).flip B))
    ((ContinuousLinearMap.compL ℂ F E E A').comp ((ContinuousLinearMap.compL ℂ F F E).flip B'))
    (fun f => by ext v; simp [a2, a3]) (fun f => by ext v; simp [a1, a4])
  exact L.integral_comp_comm φ

theorem Iint_equivariant : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ (x y : H) (ξ : Wp) (ξ' : Wq) (Om Om' : Set (Mt k r)), MeasurableSet Om → MeasurableSet Om' → ∀ γ ∈ GG k r, ∀ t ∈ Sset k r z, ∀ t' ∈ Sset k r z', Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict Om) (μS'.restrict Om') σ x y ξ ξ' (t * γ * t'⁻¹) = (PiS (psiGen k r z c) π t).comp ((Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict (rmulM t '' Om)) (μS'.restrict (rmulM t' '' Om')) σ x y ξ ξ' γ).comp (PiS (psiGen k r z' c') π' t'⁻¹)) := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' _ hs hs' x y ξ ξ' Om Om' _ _
    γ _ t ht t' ht'
  obtain ⟨hz, hT, hπ, hμ, -⟩ := hs
  obtain ⟨hz', hT', hπ', hμ', -⟩ := hs'
  have hS := isClosedSub_Sset hz hT
  have hS' := isClosedSub_Sset hz' hT'
  obtain ⟨-, ⟨⟨p1, pm⟩, -⟩, -⟩ := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ
  obtain ⟨-, ⟨⟨q1, qm⟩, -⟩, qa, -⟩ := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z' c' π' hz' hT' hπ'
  have u := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hμ).1 t ht
  have u' := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z' hz' hT' μS').1 hμ').1 t' ht'
  have dt := isUnit_det_of_mem_GG (hS.1 ht)
  have dt' := isUnit_det_of_mem_GG (hS'.1 ht')
  have hti := hS.2.2.2.2 t ht
  have hti' := hS'.2.2.2.2 t' ht'
  have := hμ.1
  have := hμ'.1
  have e := rmulM_emb dt
  have e' := rmulM_emb dt'
  have m : MeasurePreserving (rmulM t) μS μS := ⟨e.measurable, u⟩
  have m' : MeasurePreserving (rmulM t') μS' μS' := ⟨e'.measurable, u'⟩
  have mp := (m.restrict_image_emb e Om).prod (m'.restrict_image_emb e' Om')
  unfold Iint
  rw [← integral_comp_both _ _ (PiS (psiGen k r z c) π t⁻¹) _ (PiS (psiGen k r z' c') π' t')
    (by rw [← pm t ht _ hti, Matrix.mul_nonsing_inv _ dt, p1])
    (by rw [← pm _ hti t ht, Matrix.nonsing_inv_mul _ dt, p1])
    (by rw [← qm _ hti' _ ht', Matrix.nonsing_inv_mul _ dt', q1])
    (by rw [← qm _ ht' _ hti', Matrix.mul_nonsing_inv _ dt', q1]),
    ← mp.integral_comp (e.prodMap e')]
  have c1 : ∀ᵐ s ∂(μS.restrict Om), Matrix.of s ∈ Sset k r z := ae_restrict_of_ae hμ.2.2.1
  have c2 : ∀ᵐ s ∂(μS'.restrict Om'), Matrix.of s ∈ Sset k r z' := ae_restrict_of_ae hμ'.2.2.1
  refine integral_congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae c1, Measure.quasiMeasurePreserving_snd.ae c2]
    with p h1 h2
  have k1 : PiS (psiGen k r z c) π (Matrix.of p.1)⁻¹ =
      (PiS (psiGen k r z c) π t).comp (PiS (psiGen k r z c) π (Matrix.of p.1 * t)⁻¹) := by
    rw [← pm t ht _ (hS.2.2.2.2 _ (hS.2.2.2.1 _ h1 _ ht)), Matrix.mul_inv_rev,
      Matrix.mul_nonsing_inv_cancel_left _ _ dt]
  have k2 : PiS (psiGen k r z' c') π' (Matrix.of p.2)⁻¹ =
      (PiS (psiGen k r z' c') π' t').comp (PiS (psiGen k r z' c') π' (Matrix.of p.2 * t')⁻¹) := by
    rw [← qm t' ht' _ (hS'.2.2.2.2 _ (hS'.2.2.2.1 _ h2 _ ht')), Matrix.mul_inv_rev,
      Matrix.mul_nonsing_inv_cancel_left _ _ dt']
  have k3 : act2 (t * γ * t'⁻¹) p = act2 γ (Prod.map (rmulM t) (rmulM t') p) := by
    show Matrix.of p.1 * (t * γ * t'⁻¹) * (Matrix.of p.2)⁻¹ =
      (Matrix.of p.1 * t) * γ * (Matrix.of p.2 * t')⁻¹
    rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
  rw [k1, k2, k3]
  ext η
  rw [← (qa t' ht').2]
  simp only [Prod.map_fst, Prod.map_snd, of_rmulM, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, rankOneInnerOperator_apply, map_smul, ContinuousLinearMap.adjoint_inner_right]

end GlobalTheory.SgInf.Equivar
