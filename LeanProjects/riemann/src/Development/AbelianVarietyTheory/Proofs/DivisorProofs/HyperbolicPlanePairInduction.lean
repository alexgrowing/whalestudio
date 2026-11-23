import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqNormLeOfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleHyperbolicPlaneSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantFunctionalsLagrangian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneDecompositionOfPair

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.MixedPtDecay

theorem eq_smul_of_laws : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ e' : Fn F n d →ₗ[ℂ] Fn F d₂ d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = M₁.co.rho B.ψ z (e' Φ)) →
      (∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ u Φ) = e' Φ) →
      (∃ Φ ∈ schA F (Fin n × Fin d), e' Φ 0 ≠ 0) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e Φ = c • e' Φ := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ H hHyp X₁ M₁ e hgram hM₁ he e' hheis hinv hne
  have hstd : IsStd B.ψ := hP.base.std
  let δ : Fn F n₁ d →ₗ[ℂ] ℂ := LinearMap.proj 0
  have hρ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ u Φ ∈ schA F (Fin n × Fin d) :=
    fun u Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd u Φ hΦ
  have hδe : ∀ (f : Fn F n₁ d) x, f x = δ (M₁.co.rho B.ψ (M₁.co.e.symm (x, 0)) f) := fun f x => by
    simp [δ, Darboux.rho, schr]
  have hfix : ∀ z, (M₁.co.e z).1 = 0 → ∀ f : Fn F n₁ d, δ (M₁.co.rho B.ψ z f) = δ f := fun z hz f => by
    simp [δ, Darboux.rho, schr, hz]
  obtain ⟨L, hLiso, hLrank, hL⟩ := GlobalTheory.MixedLagrXPlain.mixed_lagrangian_plane F E σ B n d X W M χX χW om r s r' s' hP n₁ H hHyp
    X₁ M₁ hgram hM₁
  have hinvL : ∀ l : Fn F n d →ₗ[ℂ] ℂ, (∀ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) z},
      ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho B.ψ u Φ) = l Φ) →
      (∀ z : Matrix (Fin n₁) (Fin d) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
        l (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = l Φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F (Fin n × Fin d),
        l (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ := by
    intro l h1 h2 t w hw φ hφ
    obtain ⟨u, hu, z, hz, heq⟩ := hL t w hw
    rw [heq φ, h1 u hu _ (hρ _ φ hφ), h2 z hz φ hφ]
  obtain ⟨c, hc⟩ := GlobalTheory.SvNLinear.main hK.base F B.ψ hstd (Fin n × Fin d) L hLiso hLrank (δ ∘ₗ e) (δ ∘ₗ e')
    (hinvL _ (fun u hu Φ hΦ => by simp only [LinearMap.comp_apply]; rw [he.inv u hu Φ hΦ])
      (fun z hz Φ hΦ => by simp only [LinearMap.comp_apply]; rw [he.Heisenberg₂ z Φ hΦ, hfix z hz]))
    (hinvL _ (fun u hu Φ hΦ => by simp only [LinearMap.comp_apply]; rw [hinv u hu Φ hΦ])
      (fun z hz Φ hΦ => by simp only [LinearMap.comp_apply]; rw [hheis z Φ hΦ, hfix z hz]))
    hne
  refine ⟨c, fun Φ hΦ => funext fun x => ?_⟩
  have h1 := hc _ (hρ (incM F H.ι * M₁.co.e.symm (x, 0) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ hΦ)
  simp only [LinearMap.comp_apply] at h1
  rw [hheis _ Φ hΦ, he.Heisenberg₂ _ Φ hΦ, ← hδe, ← hδe] at h1
  simpa using h1

theorem extend_single_dot {α β R : Type} [Fintype β] [DecidableEq α] {j : α → β} (hj : Function.Injective j) [CommRing R]
    (k : α) (q : β → R) : Function.extend j (Pi.single k 1) 0 ⬝ᵥ q = q (j k) := by
  have : Function.extend j (Pi.single k (1 : R)) 0 = Pi.single (j k) 1 := by
    funext b
    by_cases h : ∃ x, j x = b
    · obtain ⟨x, rfl⟩ := h
      simp [hj.extend_apply, Pi.single_apply, hj.eq_iff]
    · rw [Function.extend_apply' _ _ _ h, Pi.single_eq_of_ne (fun hb => h ⟨k, hb.symm⟩)]; rfl
  rw [this, single_dotProduct, one_mul]

theorem exists_mixed : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∃ (M' : Model σ X W) (om' : Rep σ X W) (T : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℝ) (j : Fin d₂ × Fin d → Fin n × Fin d)
        (a : (Fin d → E) →ₗ[F] (Fin n × Fin d → F)), IsPair B M' χX χW om' r s r' s' ∧ 0 ≤ c ∧ Function.Injective j ∧
        Function.Injective a ∧ (∀ w k, a w (j k) = 0) ∧ ∀ Ψ ∈ schA F (Fin n × Fin d), T Ψ ∈ schA F (Fin n × Fin d) ∧
          (∀ x, T (om x Ψ) = om' x (T Ψ)) ∧ ∀ (w : Fin d → E) (y : Fin d₂ × Fin d → AF F),
            ‖e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Ψ) y‖ =
              c * ‖T Ψ (Function.extend j y 0 + fun k => algebraMap F (AF F) (a w k))‖ := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₂ H hHyp V₁ M₁ e hgram hM₁ he
  obtain ⟨hrk, hxx, hyy, hxy, horth, hιinj⟩ := id hHyp
  subst hrk
  have hB := hP.base
  have hV := hP.herm
  have hW := hP.skew
  have hstd : IsStd B.ψ := hB.std
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb v).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hV' : X.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hV.cartan v)
    have := ((B.emb v).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hW' : W.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hW.cartan v)
    have := ((B.emb v).1 : E →+* ℂ).map_det W.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  have hJ₁ := GlobalTheory.PlaneEvX.det_compl_ne_zero σ d₂ X.J H.x H.y H.ι hσ hV.herm hV' hxx hyy hxy horth hιinj
  rw [← hgram] at hJ₁
  obtain ⟨j, co, hj, hrat, hι, hx, hI⟩ := GlobalTheory.PlaneEvX.exists_plane_darboux σ d₂ d X.J V₁.J W.J H.x H.y H.ι hσ hB.cm.2.2.1
    hV.herm hW.skew hJ₁ hW' hxx hyy hxy horth hgram.symm M₁.co hM₁.rat
  obtain ⟨T, ei, ev, hei, hmaps, hheis, hSB, hvac, hstdv, hpure, hbij⟩ :=
    GlobalTheory.SympChangeBij.change_of_coordinates_bij F E σ B _ d X W M r s r' s' hB hV hW hP.good co hrat
  let M' : Model σ X W := ⟨co, fun v => ev v (M.vac v), M.μ, M.dom⟩
  have hM' : M'.IsGood B.ψ := ⟨hrat, hvac, hstdv, hP.good.haar, hP.good.dom⟩
  obtain ⟨φ₀, hφ₀, hφ₀0⟩ : ∃ φ ∈ schA F (Fin (d₂ + 2) × Fin d), φ 0 ≠ 0 := by
    obtain ⟨φ, hφ, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin (d₂ + 2) × Fin d)
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hθ (by simp [thetaSum, h])
    exact ⟨schr B.ψ (x, 0) φ, GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ φ hφ, by simpa [schr] using hx⟩
  have hne : ∃ f : SInf F (Fin (d₂ + 2) × Fin d), f ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hle : schA F (Fin (d₂ + 2) × Fin d) ≤ ⊥ := by
      refine Submodule.span_le.2 ?_
      rintro Φ ⟨f, g, -, rfl⟩
      rw [hall f]
      show pureA F 0 g = 0
      funext x
      simp [pureA]
    have h0 : φ₀ = 0 := (Submodule.mem_bot ℂ).1 (hle hφ₀)
    exact hφ₀0 (by rw [h0]; rfl)
  have h1d : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hev : IsEv B M M' 1 1 ∅ T := by
    refine ⟨hmaps, fun z Φ hΦ => ?_, fun u hu => hu.elim, ei, ev, ?_, fun v => ⟨rfl, hSB v⟩, hpure⟩
    · have h1 : incM F (1 : Matrix (Fin (d₂ + 2)) (Fin (d₂ + 2)) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      rw [h1, h1d, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
      exact hheis z Φ hΦ
    · obtain ⟨f, hf⟩ := hne
      obtain ⟨g, rfl⟩ := hei f
      intro h
      exact hf (by rw [h]; rfl)
  obtain ⟨om', hW₁, hint⟩ := GlobalTheory.T.weil_eigen_bijective_schwartz F E σ B _ d X W M χX χW om r s r' s' hP M' hM' T hev hbij
  obtain ⟨c, hc⟩ := eq_smul_of_laws hK F E σ B _ d X W M χX χW om r s r' s' hP d₂ H hHyp V₁ M₁ e hgram hM₁ he
    (LinearMap.funLeft ℂ ℂ (fun y : Fin d₂ × Fin d → AF F => Function.extend j y 0) ∘ₗ T)
    (by
      intro z Φ hΦ
      rw [h1d, Matrix.transpose_one, Matrix.mul_one]
      funext y
      simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
      rw [hheis _ Φ hΦ]
      simp only [Darboux.rho, schr, hι, GlobalTheory.ThKMixXEx.extend_dot hj, ← GlobalTheory.ThKMixXEx.extend_add hj, LinearMap.funLeft_apply])
    (by
      rintro u ⟨z, rfl⟩ Φ hΦ
      funext y
      simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
      rw [hheis _ Φ hΦ]
      obtain ⟨h1, h2⟩ := hx z
      simp only [Darboux.rho, schr, h1, GlobalTheory.ThKMixXEx.extend_dot_zero _ _ h2, zero_dotProduct, mul_zero, add_zero,
        AddChar.map_zero_eq_one, one_mul])
    (by
      obtain ⟨Φ, hΦ, hΦ'⟩ := hbij.surjOn hφ₀
      refine ⟨Φ, hΦ, ?_⟩
      simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
      rw [hΦ', GlobalTheory.ThKMixXEx.extend_zero' hj]
      exact hφ₀0)
  obtain ⟨φ, hφ⟩ := GlobalTheory.MixXEvUniq.exists_ratCoord M' hB.cm.2.2.1 hrat
  let L : (Fin d → E) →ₗ[F] Matrix (Fin (d₂ + 2)) (Fin d) E :=
    { toFun := fun w => Matrix.vecMulVec H.y w
      map_add' := fun z z' => Matrix.vecMulVec_add _ _ _
      map_smul' := fun t z => by ext i k; simp [Matrix.vecMulVec_apply] }
  let a : (Fin d → E) →ₗ[F] (Fin (d₂ + 2) × Fin d → F) := LinearMap.fst F _ _ ∘ₗ φ.toLinearMap ∘ₗ L
  have ha : ∀ w, (co.e (Matrix.vecMulVec (incV F H.y) (incV F w))).1 = fun k => algebraMap F (AF F) (a w k) := fun w => by
    rw [← GlobalTheory.MixXEvUniq.incM_vmv]
    exact congrArg Prod.fst (hφ _)
  have hperp : ∀ (z : Fin d → AE F E) k, (co.e (Matrix.vecMulVec (incV F H.y) z)).1 (j k) = 0 ∧
      (co.e (Matrix.vecMulVec (incV F H.y) z)).2 (j k) = 0 := fun z k => by
    have h := fun p => (co.form _ _).symm.trans
      (GlobalTheory.MixXEvUniq.sp_ix (X := X) (W := W) (fun u => (horth u).2) (M₁.co.e.symm p) z)
    have h1 := h (Pi.single k 1, 0)
    have h2 := h (0, Pi.single k 1)
    simp only [hι, LinearEquiv.apply_symm_apply, GlobalTheory.ThKMixXEx.extend_zero' hj, dotProduct_zero, zero_dotProduct,
      sub_zero, zero_sub, neg_eq_zero] at h1 h2
    rw [extend_single_dot hj] at h1
    rw [dotProduct_comm, extend_single_dot hj] at h2
    exact ⟨h2, h1⟩
  refine ⟨M', om', T, ‖c‖, j, a, ⟨hB, hV, hW, hM', hP.hX, hP.hW, hP.resX, hP.resW, hW₁⟩, norm_nonneg _, hj, ?_, ?_,
    fun Ψ hΨ => ⟨hmaps Ψ hΨ, fun x => hint x Ψ hΨ, fun w y => ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨z, hz⟩ := hI (Matrix.vecMulVec (incV F H.y) (incV F w)) (by rw [ha, hw]; funext k; simp)
      (fun k => (hperp _ k).2)
    have hyx : form σ X.J H.y H.x = 1 := by
      have hsym : form σ X.J H.y H.x = σ (form σ X.J H.x H.y) := by
        simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hV.herm, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      rw [hsym, hxy, map_one]
    funext l
    apply GlobalTheory.MixXEvUniq.inclR_inj (F := F)
    have key : ∀ (p : Fin (d₂ + 2) → E) (q : Fin d → AE F E),
        ∑ i, Matrix.vecMulVec (incV F p) q i l * inclR (F := F) (AF F) ((X.J *ᵥ fun i => σ (H.x i)) i) =
          inclR (F := F) (AF F) (form σ X.J p H.x) * q l := fun p q => by
      rw [form, dotProduct, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, Matrix.vecMulVec_apply, incV]
      ring
    have h1 := key H.y (incV F w)
    rw [hz, key, hxx, hyx, map_zero, zero_mul, map_one, one_mul] at h1
    rw [Pi.zero_apply, map_zero]
    exact h1.symm
  · intro w k
    apply GlobalTheory.MixXEvUniq.alg_inj
    rw [map_zero, ← (hperp (incV F w) k).1, ha]
  · rw [hc _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ Ψ hΨ)]
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, smul_eq_mul]
    rw [hheis _ Ψ hΨ]
    simp only [Darboux.rho, schr, norm_mul, GlobalTheory.StdCharWeilDatum.norm_psi hstd, one_mul, ha]

theorem size_le {F E κ : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Fintype κ] {d : ℕ}
    (a : (Fin d → E) →ₗ[F] (κ → F)) (ha : Function.Injective a) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w : Fin d → E) (t : ℝ), 0 ≤ t → (∀ k, ‖evI F (algebraMap F (AF F) (a w k))‖ ≤ t) →
      ∑ i, ∑ v : InfinitePlace E, v (w i) ≤ A * t := by
  obtain ⟨b, hb⟩ := a.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 ha)
  obtain ⟨c, hc⟩ := GlobalTheory.ThetaDecay.sum_places_le (F := F)
  refine ⟨∑ i, ∑ v : InfinitePlace E, ∑ k, v (b (Pi.single k 1) i) * |c|, by positivity, fun w t ht h => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun v _ => ?_
  have hw : w i = ∑ k, algebraMap F E (a w k) * b (Pi.single k 1) i := by
    have h1 : w = b (a w) := (LinearMap.congr_fun hb w).symm
    have h2 : a w = ∑ k, a w k • (Pi.single k 1 : κ → F) := by
      funext l; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [h1, h2, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
    simp only [Algebra.smul_def]
  rw [hw, Finset.sum_mul]
  refine (AbsoluteValue.sum_le v.1 _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  change v (_ * _) ≤ _
  rw [map_mul v, mul_comm, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← InfinitePlace.comap_apply]
  calc _ ≤ ∑ u : InfinitePlace F, u (a w k) :=
        Finset.single_le_sum (f := fun u : InfinitePlace F => u (a w k)) (fun _ _ => by positivity) (Finset.mem_univ _)
    _ ≤ c * ‖evI F (algebraMap F (AF F) (a w k))‖ := hc _
    _ ≤ |c| * t := mul_le_mul (le_abs_self c) (h k) (norm_nonneg _) (abs_nonneg c)

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g : UA σ X.J, ∀ K : Set (UA σ X.J), IsCompact K → K ⊆ unip σ X H →
      ∀ N₀ K' : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ u ∈ K, ∀ h : UA σ W.J, ∀ N : ℕ, 1 ≤ N → ∀ w : Fin d → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
        ∀ ξ : Fin d₂ × Fin d → F,
          ‖e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))) (fun i => algebraMap F (AF F) (ξ i))‖ *
            (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ * (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K' ≤ C * ((N : ℝ) * ht h) ^ k := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₂ H hHyp V₁ M₁ e hgram hM₁ he Φ hΦ g K hKc _ N₀ K'
  obtain ⟨M', om', T, c, j, a, hP', hc, hj, ha, haj, hT⟩ :=
    exists_mixed hK F E σ B n d X W M χX χW om r s r' s' hP d₂ H hHyp V₁ M₁ e hgram hM₁ he
  obtain ⟨A, hA, hsize⟩ := size_le a ha
  obtain ⟨C, k, hC⟩ := GlobalTheory.ArchDecay.om_bound_arch F E σ B n d X W M' χX χW om' r s r' s' hP' (T Φ) (hT Φ hΦ).1 (N₀ + K')
  have hcont : Continuous fun x : UA σ X.J => (ht x : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL (F := F) (E := E) (n := Fin n)).comp continuous_subtype_val)
  obtain ⟨R, hR⟩ := hKc.bddAbove_image hcont.continuousOn
  have hS := IsUWeilPair.isUSplitting hP.weil
  refine ⟨c * (1 + A) ^ K' * (|C| * (|R| * ht g) ^ k), k, fun u hu h N hN w _ ξ => ?_⟩
  have hmul : om (u, 1) (om (g, h) Φ) = om (u * g, h) Φ := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  rw [hmul, (hT _ (hS.pres _ Φ hΦ)).2.2, (hT Φ hΦ).2.1]
  set x : Fin n × Fin d → AF F := Function.extend j (fun i => algebraMap F (AF F) (ξ i)) 0 +
    fun k => algebraMap F (AF F) (a w k) with hx
  have hb := hC (u * g) h x
  set t : ℝ := ‖fun i => evI F (x i)‖ with ht'
  have ht0 : 0 ≤ t := norm_nonneg _
  have hco : ∀ i, ‖evI F (x i)‖ ≤ t := fun i => norm_le_pi_norm (fun i => evI F (x i)) i
  have h1 : ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤ t := by
    refine (pi_norm_le_iff_of_nonneg ht0).2 fun i => ?_
    have := hco (j i)
    simpa only [hx, Pi.add_apply, hj.extend_apply, haj, map_zero, add_zero] using this
  have h2 : ∑ i, ∑ v : InfinitePlace E, v (w i) ≤ A * t := by
    refine hsize w t ht0 fun l => ?_
    by_cases hl : ∃ i, j i = l
    · obtain ⟨i, rfl⟩ := hl
      rw [haj, map_zero, show evI F 0 = 0 from by unfold evI; exact map_zero _, norm_zero]
      exact ht0
    · have := hco l
      simpa only [hx, Pi.add_apply, Function.extend_apply' _ _ _ hl, Pi.zero_apply, zero_add] using this
  have h3 : 1 + ∑ i, ∑ v : InfinitePlace E, v (w i) ≤ (1 + A) * (1 + t) := by nlinarith
  have hug : (ht (u * g) : ℝ) ≤ |R| * ht g := by
    have h4 : (ht (u * g) : ℝ) ≤ ht u * ht g := by
      have := GlobalTheory.AdelicU.heightGL_mul_le (F := F) (u : GL (Fin n) (AE F E)) (g : GL (Fin n) (AE F E))
      exact_mod_cast this
    exact h4.trans (mul_le_mul_of_nonneg_right ((hR ⟨u, hu, rfl⟩).trans (le_abs_self R)) (NNReal.coe_nonneg _))
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h5 : ((ht (u * g) : ℝ) * ht h) ^ k ≤ (|R| * ht g) ^ k * ((N : ℝ) * ht h) ^ k := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) (mul_le_mul hug ?_ (by positivity) (by positivity)) k
    exact le_mul_of_one_le_left (NNReal.coe_nonneg _) hN'
  calc c * ‖om' (u * g, h) (T Φ) x‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ *
        (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K'
      ≤ c * ‖om' (u * g, h) (T Φ) x‖ * (1 + t) ^ N₀ * ((1 + A) * (1 + t)) ^ K' := by gcongr
    _ = c * (1 + A) ^ K' * (‖om' (u * g, h) (T Φ) x‖ * (1 + t) ^ (N₀ + K')) := by rw [mul_pow, pow_add]; ring
    _ ≤ c * (1 + A) ^ K' * (|C| * ((|R| * ht g) ^ k * ((N : ℝ) * ht h) ^ k)) := by
        refine mul_le_mul_of_nonneg_left (hb.trans ?_) (by positivity)
        exact mul_le_mul (le_abs_self C) h5 (by positivity) (abs_nonneg C)
    _ = _ := by ring

end GlobalTheory.MixedPtDecay
