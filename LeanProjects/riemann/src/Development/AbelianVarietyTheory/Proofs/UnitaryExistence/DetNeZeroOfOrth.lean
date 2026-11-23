import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LintegralUnfoldArithmeticQuotientDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameRealUnitaryOrbitGramRigidStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDiscreteArithGroupImageRealUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMeasurePreservingFrameChangeProportionalHeStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeterssonCompare

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf (lact_mul lact_one lact_rmul lact_inv)
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem det_ne_zero_of_orth (X : Data E r) {y : Frame X.Ψ r} (hy : y ∈ OrthFr X) (τ : X.Ψ) : (mat y τ).det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det (hy τ)
  rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul, sgnMat,
    Matrix.det_diagonal] at h1
  refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h1.symm
  unfold sgn
  split_ifs <;> simp

theorem exists_real_of_orth (X : Data E r) {y z : Frame X.Ψ r} (hy : y ∈ OrthFr X) (hz : z ∈ OrthFr X) :
    ∃ s : RealGrp X, ∀ τ, mat z τ = mat y τ * ((s τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
  have key : ∀ τ : X.Ψ, ∃ u : Upq r X.p0, mat z τ = mat y τ * ((u : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
    intro τ
    have hb := det_ne_zero_of_orth X hy τ
    have hd : ((mat y τ)⁻¹ * mat z τ).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero (inv_ne_zero hb) (det_ne_zero_of_orth X hz τ)
    have e : mat z τ = mat y τ * ((mat y τ)⁻¹ * mat z τ) := (Matrix.mul_nonsing_inv_cancel_left _ _ hb.isUnit).symm
    refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩, e⟩
    have h1 := hz τ
    rw [e, FrameDegreeData.gram_mul, hy τ] at h1
    exact h1
  choose s hs using key
  exact ⟨s, hs⟩

theorem exists_hom_real (X : Data E r) {y : Frame X.Ψ r} (hy : y ∈ OrthFr X) {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (ar : X.Ψ → G →* Matrix (Fin r) (Fin r) ℂ)
    (hc : ∀ τ, Continuous (ar τ))
    (ha : ∀ τ g, (ar τ g)ᵀ * X.Gm.map τ.1 * (ar τ g).map (starRingEnd ℂ) = X.Gm.map τ.1) :
    ∃ ψ : G →* RealGrp X, Continuous ψ ∧
      ∀ g τ, mat y τ * ((ψ g τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = ar τ g * mat y τ := by
  let Y : X.Ψ → GL (Fin r) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_ne_zero_of_orth X hy τ)
  let φ : X.Ψ → G →* GL (Fin r) ℂ := fun τ => (MulAut.conj (Y τ)⁻¹).toMonoidHom.comp (ar τ).toHomUnits
  have hφ : ∀ g τ, mat y τ * ((φ τ g : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = ar τ g * mat y τ := by
    intro g τ
    have : Y τ * φ τ g = (ar τ).toHomUnits g * Y τ := by simp [φ, mul_assoc]
    exact congrArg Units.val this
  have hm : ∀ τ g, φ τ g ∈ Upq r X.p0 := by
    intro τ g
    have h1 : gram τ.1 X.Gm (ar τ g * mat y τ) = sgnMat r X.p0 := by
      rw [← hy τ, FrameDegreeData.gram_eq, FrameDegreeData.gram_eq, Matrix.transpose_mul, Matrix.map_mul]
      conv_rhs => rw [← ha τ g]
      simp only [Matrix.mul_assoc]
    rw [← hφ, FrameDegreeData.gram_mul, hy τ] at h1
    exact h1
  refine ⟨MonoidHom.pi fun τ => (φ τ).codRestrict _ (hm τ), continuous_pi fun τ => Continuous.subtype_mk ?_ _, hφ⟩
  have : Continuous (ar τ).toHomUnits :=
    Units.continuous_iff.2 ⟨hc τ, ((hc τ).comp continuous_inv).congr fun g => by simp [← map_inv]⟩
  exact (continuous_const.mul this).mul continuous_const

section Rel

variable {Comp : Type} (X : Comp → Data E r)

def SameOrb (p q : Σ k, Frame (X k).Ψ r) : Prop := ∃ γ ∈ (X p.1).Γ, q = ⟨p.1, lact γ p.2⟩

theorem sameOrb_equivalence : Equivalence (SameOrb X) := by
  refine ⟨fun p => ⟨1, one_mem _, by rw [lact_one]⟩, ?_, ?_⟩
  · rintro ⟨k, x⟩ _ ⟨γ, hγ, rfl⟩
    exact ⟨γ⁻¹, inv_mem hγ, by simp only [lact_inv]⟩
  · rintro ⟨k, x⟩ _ _ ⟨γ, hγ, rfl⟩ ⟨δ, hδ, rfl⟩
    exact ⟨δ * γ, mul_mem hδ hγ, by simp only [lact_mul]⟩

theorem sameOrb_mk {k : Comp} {x x' : Frame (X k).Ψ r} :
    SameOrb X ⟨k, x⟩ ⟨k, x'⟩ ↔ ∃ γ ∈ (X k).Γ, x' = lact γ x :=
  exists_congr fun _ => and_congr_right fun _ => by simp

end Rel

theorem rmul_cancel {Ψ : Finset (E →+* ℂ)} {x x' b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (h : rmul x b = rmul x' b) :
    x = x' := by
  funext τ
  have h1 : mat x τ * mat b τ = mat x' τ * mat b τ := congrFun h τ
  exact ((Matrix.isUnit_iff_isUnit_det _).2 (hb τ).1.isUnit).mul_right_cancel h1

theorem lintegral_dict {Comp : Type} [Fintype Comp] (X : Comp → Data E r) {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] (Γ Gi Kf H : Subgroup G) [Countable Γ] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (h0 : μ 𝓕 ≠ 0) (h1 : μ 𝓕 ≠ ⊤) (hH : MeasurableSet (H : Set G))
    (hmem : ∀ h, h ∈ H ↔ ∃ a ∈ Gi, ∃ z ∈ Kf, h = a * z)
    (dict : G → Σ k, Frame (X k).Ψ r) (ar : (E →+* ℂ) → G →* Matrix (Fin r) (Fin r) ℂ)
    (J : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x0 : ∀ k, Frame (X k).Ψ r)
    (hΨ : ∀ k k', (X k).Ψ = (X k').Ψ ∧ (X k).p0 = (X k').p0)
    (hJ : ∀ τ, (J τ).IsHermitian ∧ (J τ).det ≠ 0)
    (hc : ∀ k (τ : (X k).Ψ), Continuous (ar τ.1))
    (hu : ∀ k (τ : (X k).Ψ) g, (ar τ.1 g)ᵀ * J τ.1 * (ar τ.1 g).map (starRingEnd ℂ) = J τ.1)
    (hs : ∀ k (u : (X k).Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ, (u τ)ᵀ * J τ.1 * (u τ).map (starRingEnd ℂ) = J τ.1) →
      ∃ h ∈ Gi, ∀ τ : (X k).Ψ, ar τ.1 h = u τ)
    (hK : ∀ k (τ : (X k).Ψ), ∀ z ∈ Kf, ar τ.1 z = 1)
    (hΓ : ∀ k, ∀ γ ∈ Γ, (∀ τ : (X k).Ψ, ar τ.1 γ = 1) → γ = 1)
    (dL : ∀ γ ∈ Γ, ∀ g, SameOrb X (dict g) (dict (γ * g)))
    (dR : ∀ z ∈ Kf, ∀ g, SameOrb X (dict g) (dict (g * z)))
    (d0 : ∀ k, x0 k ∈ (X k).dom ∧ ∃ g, dict g = ⟨k, x0 k⟩)
    (dI : ∀ g, ∀ h ∈ Gi, ∃ γ ∈ (X (dict g).1).Γ, dict (g * h) = ⟨(dict g).1, lact γ (rmul (dict g).2 fun τ =>
      ((mat (x0 (dict g).1) τ)⁻¹ * ar τ.1 h * mat (x0 (dict g).1) τ : Matrix (Fin r) (Fin r) ℂ))⟩)
    (dD : ∀ g, (dict g).2 ∈ (X (dict g).1).dom)
    (dF : ∀ g g', SameOrb X (dict g) (dict g') → ∃ γ ∈ Γ, ∃ z ∈ Kf, g' = γ * g * z)
    (dU : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : ∀ k, Frame (X k).Ψ r → ℝ≥0∞, (∀ k, Measurable (F k)) →
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, F k (lact γ x) = F k x) →
      (∀ k, ∀ b ∈ Bor (X k).Ψ r, ∀ x ∈ (X k).dom, F k (rmul x b) = F k x) →
      Measurable (fun g => F (dict g).1 (dict g).2) ∧
        ∫⁻ g in 𝓕, F (dict g).1 (dict g).2 ∂μ = κ * ∑ k, quotInt (X k) (F k) := by
  obtain ⟨hG, hgr⟩ := GlobalTheory.T.unitFrame_real_unitary_orbit_gram_rigid E r Comp X G Gi dict (fun k g τ => ar τ.1 g) (fun k τ => J τ.1) x0
    (fun k τ => hJ τ.1) hs d0 dI dD dU
  choose t ht0 ht using hG
  choose y hy b hb hxb using fun k => ReciprocityTheory.ChartRestriction.G.AR.Up.ortho_holds r (X k) (x0 k) (d0 k).1
  replace hy : ∀ k, y k ∈ OrthFr (X k) := hy
  have hyu : ∀ k τ, IsUnit (mat (y k) τ).det := fun k τ => (det_ne_zero_of_orth _ (hy k) τ).isUnit
  have hJG : ∀ k (τ : (X k).Ψ) (u : Matrix (Fin r) (Fin r) ℂ), uᵀ * J τ.1 * u.map (starRingEnd ℂ) = J τ.1 ↔
      uᵀ * (X k).Gm.map τ.1 * u.map (starRingEnd ℂ) = (X k).Gm.map τ.1 := by
    intro k τ u
    rw [ht, Matrix.mul_smul, Matrix.smul_mul]
    exact (smul_right_injective _ (Complex.ofReal_ne_zero.2 (ht0 k τ))).eq_iff.symm
  choose ψ hψc hψ using fun k => exists_hom_real (X k) (hy k) (fun τ => ar τ.1) (hc k)
    fun τ g => (hJG k τ _).1 (hu k τ g)
  choose s hsy using fun k => exists_real_of_orth (X k) (baseFr_mem (X k)) (hy k)
  choose g hg using fun k => (d0 k).2
  choose Λ hΛ hΛd using fun k => GlobalTheory.T.exists_discrete_arithGroupImage_realUnitary E r (X k)
  have hfr : ∀ k h τ, mat (frameOf (X k) (s k * ψ k h)) τ = ar τ.1 h * mat (y k) τ := by
    intro k h τ
    rw [← hψ, hsy, mat_frameOf, Matrix.mul_assoc]
    rfl
  have hψ' : ∀ k h τ, mat (y k) τ * ((ψ k h τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat (y k) τ)⁻¹ =
      ar τ.1 h := fun k h τ => by rw [hψ, Matrix.mul_nonsing_inv_cancel_right _ _ (hyu k τ)]
  have hinj : ∀ k (a a' : RealGrp (X k)), (∀ τ, mat (y k) τ * ((a τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (mat (y k) τ)⁻¹ = mat (y k) τ * ((a' τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat (y k) τ)⁻¹) →
      a = a' := by
    intro k a a' h
    funext τ
    have h2 := congrArg (· * mat (y k) τ) (h τ)
    simp only [Matrix.nonsing_inv_mul_cancel_right _ _ (hyu k τ)] at h2
    exact Subtype.ext (Units.ext (((Matrix.isUnit_iff_isUnit_det _).2 (hyu k τ)).mul_left_cancel h2))
  haveI : ∀ k, (haarR (X k)).IsHaarMeasure := fun k => by unfold haarR; infer_instance
  refine Exists.elim (GlobalTheory.T.lintegral_unfold_arithmetic_quotient_doubleCosets G μ Γ H Kf 𝓕 h𝓕 h0 h1 hH
    (fun z hz => (hmem z).2 ⟨1, one_mem _, z, hz, (one_mul _).symm⟩) Comp (fun k => RealGrp (X k))
    (fun k => haarR (X k)) ψ Λ s g _ (SameOrb X) dict (fun k a => ⟨k, rmul (frameOf (X k) a) (b k)⟩)
    (fun k => (hψc k).measurable) ?_ ?_ ?_ ?_ hΛd (sameOrb_equivalence X) ?_ ?_ ?_ ?_ ?_) ?_
  rotate_right
  · rintro κ ⟨D, hκ0, hκ1, hD, hI⟩
    refine ⟨κ, hκ0, hκ1, fun F hF hFΓ hFB => ?_⟩
    have e : ∀ k a, F k (rmul (frameOf (X k) a) (b k)) = F k (frameOf (X k) a) :=
      fun k a => hFB k _ (hb k) _ (frameOf_mem_dom _ a)
    obtain ⟨h2, h3⟩ := hI (fun p => F p.1 p.2) (by rintro x _ ⟨γ, hγ, rfl⟩; exact hFΓ _ γ hγ _ (dD x))
      (fun k => by simp only [e]; exact (hF k).comp (measurable_frameOf _))
    refine ⟨h2, h3.trans ?_⟩
    simp only [e]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    haveI := (hD k).1
    rw [quotInt_eq _ (hΛ k) (hD k).2 (hFΓ k)]
  · intro k a
    obtain ⟨h, hh, e⟩ := hs k (fun τ => mat (y k) τ * ((a τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (mat (y k) τ)⁻¹) fun τ => (hJG k τ _).2 (by
        have h2 : gram τ.1 (X k).Gm (mat (y k) τ * ((a τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) =
            gram τ.1 (X k).Gm (mat (y k) τ) := by
          rw [FrameDegreeData.gram_mul, hy k τ]
          exact (a τ).2
        rw [← FrameDegreeData.gram_eq, FrameDegreeData.gram_mul, h2, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv _ (hyu k τ),
          FrameDegreeData.gram_eq]
        simp)
    exact ⟨h, (hmem h).2 ⟨h, hh, 1, one_mem _, (mul_one _).symm⟩, hinj k _ _ fun τ => (hψ' k h τ).trans (e τ)⟩
  · intro k z hz
    refine hinj k _ _ fun τ => ?_
    rw [hψ', hK k τ z hz]
    simp [Matrix.mul_nonsing_inv _ (hyu k τ)]
  · intro k γ hγ h
    refine hΓ k γ hγ fun τ => ?_
    rw [← hψ' k, h]
    simp [Matrix.mul_nonsing_inv _ (hyu k τ)]
  · intro k k'
    obtain ⟨e, α, u, he, hα, hαα, h⟩ := GlobalTheory.T.exists_measurePreserving_frameChange_proportional_hermitian E r (X k) (X k') (y k) (y k') (hΨ k k').1 (hΨ k k').2 (hy k)
      (hy k') fun τ => by
        have hτ : τ.1 ∈ (X k').Ψ := (hΨ k k').1 ▸ τ.2
        refine ⟨t k' ⟨τ.1, hτ⟩ / t k τ, div_ne_zero (ht0 _ _) (ht0 _ _), ?_⟩
        rw [ht k' ⟨τ.1, hτ⟩, ht k τ, smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ (ht0 _ _)]
    refine ⟨e, α, u, he, hα, fun x => hinj k' _ _ fun τ' => ?_, hαα⟩
    have hτ : τ'.1 ∈ (X k).Ψ := (hΨ k' k).1 ▸ τ'.2
    rw [h _ ⟨τ'.1, hτ⟩ τ' rfl, hψ', hψ']
  · refine fun x x' => ⟨dF x x', ?_⟩
    rintro ⟨γ, hγ, z, hz, rfl⟩
    exact (sameOrb_equivalence X).trans (dL γ hγ x) (dR z hz _)
  · intro k h hh
    obtain ⟨a, ha, z, hz, rfl⟩ := (hmem h).1 hh
    rw [← mul_assoc]
    refine (sameOrb_equivalence X).trans ((sameOrb_equivalence X).symm (dR z hz _)) ((sameOrb_equivalence X).symm ?_)
    have h2 := dI (g k) a ha
    rw [hg k] at h2
    obtain ⟨γ, hγ, h2⟩ := h2
    refine ⟨γ, hγ, h2.trans ?_⟩
    congr 2
    funext τ
    show mat (x0 k) τ * ((mat (x0 k) τ)⁻¹ * ar τ.1 a * mat (x0 k) τ) =
      mat (frameOf (X k) (s k * ψ k (a * z))) τ * mat (b k) τ
    rw [hfr, map_mul, hK k τ z hz, mul_one, Matrix.mul_assoc (mat (x0 k) τ)⁻¹,
      Matrix.mul_nonsing_inv_cancel_left _ _ ((d0 k).1 τ).1.isUnit, Matrix.mul_assoc, hxb k]
    rfl
  · intro x
    have h2 := hgr x
    generalize dict x = p at h2
    obtain ⟨k, z⟩ := p
    have hbu : ∀ τ, IsUnit (mat (b k) τ).det := fun τ => (hb k τ).1.isUnit
    obtain ⟨a, ha⟩ := exists_real_of_orth (X k) (baseFr_mem (X k))
      (z := fun τ => (mat z τ * (mat (b k) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)) fun τ => by
        show gram τ.1 (X k).Gm (mat z τ * (mat (b k) τ)⁻¹) = _
        have h3 : mat (x0 k) τ = mat (y k) τ * mat (b k) τ := congrFun (hxb k) τ
        rw [FrameDegreeData.gram_mul, h2 τ, ← FrameDegreeData.gram_mul, h3, Matrix.mul_nonsing_inv_cancel_right _ _ (hbu τ), hy k τ]
    refine ⟨k, a, ?_⟩
    have : rmul (frameOf (X k) a) (b k) = z := by
      funext τ
      show mat (frameOf (X k) a) τ * mat (b k) τ = mat z τ
      rw [mat_frameOf, ← ha τ]
      exact Matrix.nonsing_inv_mul_cancel_right _ _ (hbu τ)
    rw [this]
    exact (sameOrb_equivalence X).refl _
  · rintro k k' a a' ⟨γ, -, h⟩
    exact (congrArg Sigma.fst h).symm
  · intro k a a'
    rw [sameOrb_mk]
    constructor
    · rintro ⟨γ, hγ, h⟩
      obtain ⟨w, hw⟩ := exists_translation (X k) hγ
      rw [lact_rmul, lact_frameOf _ hw] at h
      exact ⟨w, (hΛ k w).2 ⟨γ, hγ, hw⟩, frameOf_injective _ (rmul_cancel (hb k) h)⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨γ, hγ, e⟩ := (hΛ k w).1 hw
      exact ⟨γ, hγ, by rw [lact_rmul, lact_frameOf _ e]⟩

end GlobalTheory.PeterssonCompare
