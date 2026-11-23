import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFixLeRatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEtaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleEvaluationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBIntermediateModelEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLeviTorusEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinateHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensVmvLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicLeviUnipotentSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLeviClosureMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundamentalDomainParabolicIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviLiftOfAdaptedPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingIntegralCountable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.ConeBack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem evLaw_left (hK : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H')
    {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)} (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W}
    (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁')
    {t : (AE F E)ˣ} {g₀ : UA σ G₁.V'.J} {m : UA σ G.V'.J} (hm : IsLevi H t g₀ m) {u : UA σ G.V'.J} (hu : u ∈ unip σ G.V' H)
    {Ψ : Fn F (b + 2) (a + (b + 2))} (hΨ : Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2)))) :
    e' (om' (u * m, 1) Ψ) = (((X.α / X.β) t : ℂ) * (((absE F E t : ℝ) ^ (((a + (b + 2) : ℕ) : ℝ) / 2) : ℝ) : ℂ)) •
      om₁' (g₀, 1) (e' Ψ) := by
  have pV' := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have p1 := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2
  obtain ⟨Mm, hMm⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B pV'.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ p1.herm pV'.skew
  obtain ⟨omm, hom⟩ := GlobalTheory.T.hecke_characters_restriction_eta hK F E σ B pV'.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ p1.herm pV'.skew Mm hMm
    X.α (X.α / X.β) pV'.hX pV'.hW p1.resX pV'.resW
  have pm : IsPair B Mm X.α (X.α / X.β) omm _ _ _ _ :=
    ⟨pV'.base, p1.herm, pV'.skew, hMm, pV'.hX, pV'.hW, p1.resX, pV'.resW, hom⟩
  obtain ⟨⟨e₁, he₁⟩, law₁⟩ := GlobalTheory.T.adapted_plane_first_variable hK F E σ B _ _ G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ pV' b G₁.V' H 0 (b + 1)
    Mm omm _ _ hC.hH pm
  obtain ⟨e₂, he₂⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hK).1 F E σ B _ _ G₁.V' G.W Mm X.α (X.α / X.β) omm _ _ _ _ pm (a + b) G₁.V' G₁.W H'
    a (a + b + 1) G₁.M' rfl hC.hH' hT₁.geo.hM').1
  have pres : ∀ (p : UA σ G.V'.J × UA σ G.W.J), ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      om' p Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) :=
    fun p Φ hΦ => (IsUWeilPair.isUSplitting hT.weil').pres p Φ hΦ
  have hlaw : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e₂ (e₁ (om' (u * m, 1) Φ)) =
      (((X.α / X.β) t : ℂ) * (((absE F E t : ℝ) ^ (((a + (b + 2) : ℕ) : ℝ) / 2) : ℝ) : ℂ)) • om₁' (g₀, 1) (e₂ (e₁ Φ)) := by
    intro Φ hΦ
    have k1 := law₁ e₁ he₁ 1 t g₀ m hm u hu Φ hΦ
    have k2 := GlobalTheory.T.adapted_plane_second_variable hK F E σ B _ _ G₁.V' G.W Mm X.α (X.α / X.β) omm _ _ _ _ pm (a + b) G₁.W H' a (a + b + 1) G₁.M' om₁'
      _ _ hC.hH' p1 e₂ he₂ g₀ 1 1 1 (GlobalTheory.ThK.Check.isLevi_one H') 1 (one_mem _) (e₁ Φ) (he₁.maps Φ hΦ)
    simp only [mul_one, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at k2
    rw [k1, map_smul, k2]
  have one : incM F (1 : Matrix (Fin b) (Fin b) E) = 1 := GlobalTheory.ThK.Check.incM_one
  have one' : incM F (1 : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) E) = 1 := GlobalTheory.ThK.Check.incM_one
  have hmaps : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), (e₂ ∘ₗ e₁) Φ ∈ schA F (Fin b × Fin (a + b)) :=
    fun Φ hΦ => he₂.maps _ (he₁.maps Φ hΦ)
  have hheis : ∀ z, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M'.co.rho B.ψ z ((e₂ ∘ₗ e₁) Φ) := by
    intro z Φ hΦ
    have k1 := he₁.Heisenberg₂ (z * (incM F H'.ι)ᵀ) Φ hΦ
    rw [one', Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc] at k1
    have k2 := he₂.Heisenberg₂ z (e₁ Φ) (he₁.maps Φ hΦ)
    rw [one, Matrix.one_mul] at k2
    simp only [LinearMap.comp_apply]
    rw [k1, k2]
  have hinv : ∀ u ∈ isoB H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ u Φ) = (e₂ ∘ₗ e₁) Φ := by
    intro u hu Φ hΦ
    simp only [LinearMap.comp_apply]
    rcases hu with ⟨z, rfl⟩ | ⟨y, rfl⟩
    · rw [he₁.inv _ ⟨z, rfl⟩ Φ hΦ]
    · have k1 := he₁.Heisenberg₂ (Matrix.vecMulVec y (incV F H'.x)) Φ hΦ
      rw [one', Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec] at k1
      rw [k1, he₂.inv _ ⟨y, rfl⟩ _ (he₁.maps Φ hΦ)]
  have hloc : ∃ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
      (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
        (e₂ ∘ₗ e₁) (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
    obtain ⟨ei₁, ev₁, -, hv₁, hl₁⟩ := he₁.loc
    obtain ⟨ei₂, ev₂, -, hv₂, hl₂⟩ := he₂.loc
    refine ⟨ei₂.comp ei₁, fun v => (ev₂ v).comp (ev₁ v), fun v => ⟨?_, ?_⟩, fun f φ hφ hc => ?_⟩
    · simp [(hv₁ v).1, (hv₂ v).1]
    · rw [Submodule.map_comp, (hv₁ v).2, (hv₂ v).2]
    · have hφ' : ∀ v, ev₁ v (φ v) ∈ SB _ := fun v => by
        rw [← (hv₁ v).2]; exact Submodule.mem_map_of_mem (hφ v)
      have hc' : ∀ᶠ v in cofinite, ev₁ v (φ v) = Mm.vac v := by
        filter_upwards [hc] with v hv; rw [hv, (hv₁ v).1]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      rw [hl₁ f φ hφ hc, hl₂ _ _ hφ' hc']
  obtain ⟨c, hc⟩ := GlobalTheory.T.config_b_triple_evaluation_compatible hK F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ e' he' (e₂ ∘ₗ e₁) hmaps hheis hinv hloc
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.config_b_intermediate_model_evaluation hK F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ Mm hMm e₁ he₁ e₂ he₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    have := hc Φ₀ hΦ₀
    simpa using this
  have he'E : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e' Φ = c⁻¹ • e₂ (e₁ Φ) := by
    intro Φ hΦ
    have := hc Φ hΦ
    simp only [LinearMap.comp_apply] at this
    rw [this, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [he'E _ (pres _ Ψ hΨ), hlaw Ψ hΨ, he'E Ψ hΨ, map_smul, smul_comm]

private theorem symp_right_zero {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (x : Fin d → E) (hx : form σ JW x x = 0) (p q : Fin n → AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) (Matrix.vecMulVec p (incV F x))
      (Matrix.vecMulVec q (incV F x)) = 0 := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have h0 : (∑ j, incV F x j * ∑ l, incM F JW j l * cA σ (incV F x l)) = 0 := by
    have : (∑ j, incV F x j * ∑ l, incM F JW j l * cA σ (incV F x l)) = inclR (F := F) (AF F) (form σ JW x x) := by
      simp only [incV, incM, Matrix.map_apply, hc, form, dotProduct, Matrix.mulVec, map_sum, map_mul]
    rw [this, hx, map_zero]
  have h1 : hTens (cA σ) (incM F JX) (incM F JW) (Matrix.vecMulVec p (incV F x)) (Matrix.vecMulVec q (incV F x)) = 0 := by
    rw [GlobalTheory.ArchSchB.TensForm.hTens_vmv_right]
    refine Finset.sum_eq_zero fun i _ => ?_
    calc _ = (p i * ∑ k, incM F JX i k * cA σ (q k)) * ∑ j, incV F x j * ∑ l, incM F JW j l * cA σ (incV F x l) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.vecMulVec_apply]
          ring
      _ = 0 := by rw [h0, mul_zero]
  rw [symp, h1, mul_zero, map_zero]

private theorem thetaSum_smul' {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

private theorem om_mul {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (g g' : UA σ X.J) (h h' : UA σ W.J) (Φ : Fn F n d) :
    om (g * g', h * h') Φ = om (g, h) (om (g', h') Φ) := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

private theorem actAB_left {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (m : UA σ X.J) (v : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) ((m, 1) : UA σ X.J × UA σ W.J) v = mat m * v := by
  simp [actAB, mat]

private theorem actAB_right {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (m : UA σ W.J) (v : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) ((1, m) : UA σ X.J × UA σ W.J) v = v * (mat m)ᵀ := by
  simp [actAB, mat]

private def wTerm (B : Base F E) {n n₁ d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (H : Plane E n n₁)
    (H' : Plane E d d₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (om : Rep σ X W) (Φ : Fn F n d) (g : UA σ X.J) (h : UA σ W.J) : ℂ :=
  thetaSum F (e (M.co.rho B.ψ (shiftB σ H H' 1) (om (g, h) Φ)))

section Laws

variable (hK : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H')
    {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)} (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W}
    (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁')
    {Φ : Fn F (b + 2) (a + (b + 2))} (hΦ : Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))))

include he' hT hT₁ hΦ in

private theorem continuous_wTerm (h : UA σ G.W.J) : Continuous fun g => wTerm B G.M' H H' e' om' Φ g h := by
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin b × Fin (a + b))
  have hl₁ := GlobalTheory.T.eigen_intertwiner_good_models F E σ B _ _ _ _ G.V' G.W G₁.V' G₁.W G.M' G₁.M' H.ι H'.ι _ e' hT.geo.hM' hT₁.geo.hM' he' l₀ hl₀
  have hl₂ := GlobalTheory.ConeTermCont.schrLin_comp_mem_adm B.ψ hT.base.std (G.M'.co.e (shiftB σ H H' 1)) _ hl₁
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' := hT.weil'
  have hc := (hw.2.2 _ hl₂ Φ hΦ).comp
    (continuous_id.prodMk continuous_const : Continuous fun g : UA σ G.V'.J => (g, h))
  refine hc.congr fun g => ?_
  have h1 := hw.isUSplitting.pres (g, h) Φ hΦ
  have h2 := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std (shiftB σ H H' 1) _ h1
  rw [wTerm, ← hl₀eq _ (he'.maps _ h2)]
  rfl

include hK hC he' hT hT₁ hΦ in

private theorem wTerm_levi {l : (AE F E)ˣ} {g₀ : UA σ G₁.V'.J} {m : UA σ G.V'.J} (hm : IsLevi H l g₀ m) (k : UA σ G.V'.J)
    (h : UA σ G.W.J) : wTerm B G.M' H H' e' om' Φ (m * k) h =
      (((X.α / X.β) l : ℂ) * (((absE F E l : ℝ) ^ (((a + (b + 2) : ℕ) : ℝ) / 2) : ℝ) : ℂ)) *
        theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k, h) Φ))) g₀ 1 := by
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hΨ := hS.pres (k, h) Φ hΦ
  have hΨ' := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std (shiftB σ H H' l) _ hΨ
  have hsh : mat m * shiftB σ H H' l = shiftB σ H H' 1 := by
    rw [shiftB, shiftB, Matrix.mul_smul, Matrix.mul_vecMulVec, hm.2.1, Matrix.smul_vecMulVec, smul_smul, ← map_mul,
      Units.mul_inv, Units.val_one]
  have h1 : om' (m * k, h) Φ = om' (m, 1) (om' (k, h) Φ) := by rw [← om_mul, one_mul]
  have h2 := evLaw_left hK hC he' hT hT₁ hm (one_mem _) hΨ'
  rw [one_mul] at h2
  rw [wTerm, h1, ← hsh, ← actAB_left (W := G.W), ← hS.impl (m, 1) _ _ hΨ, h2, thetaSum_smul', theta]

include hK hC he' hT hT₁ hΦ in

private theorem wTerm_unip {u : UA σ G.V'.J} (hu : u ∈ unip σ G.V' H) (g : UA σ G.V'.J) (h : UA σ G.W.J) :
    wTerm B G.M' H H' e' om' Φ (u * g) h = wTerm B G.M' H H' e' om' Φ g h := by
  have hP' := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have hP₁' := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2
  have hB := hP'.base
  have hS := IsUWeilPair.isUSplitting hT.weil'
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet₁ : G₁.V'.J.det ≠ 0 := by
    have h := GlobalTheory.LeviElem.det_ne_of_sig _ (hP₁'.herm.sig w)
    intro h0
    apply h
    have : (G₁.V'.J.map (B.emb w).1).det = (B.emb w).1 G₁.V'.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  obtain ⟨hspan, hdet⟩ := GlobalTheory.UnipChart.span_det σ hσ B hP'.herm.herm hC.hH hdet₁
  have hyp : GlobalTheory.UnipChart.Hyp σ G.V'.J G₁.V'.J H :=
    ⟨hσ, hP'.herm.herm, hC.hH.xx, hC.hH.yy, hC.hH.xy, hC.hH.orth, hC.hH.gram⟩
  obtain ⟨β, c, hy⟩ : ∃ (β : Fin b → AE F E) (c : AE F E),
      mat u⁻¹ *ᵥ incV F H.y = incV F H.y + (incM F H.ι *ᵥ β + c • incV F H.x) :=
    ⟨_, _, hyp.unip_y hspan hdet hP₁'.herm.herm (isUnit_iff_ne_zero.mpr hdet₁) (inv_mem hu)⟩
  have hΨ := hS.pres (g, h) Φ hΦ
  have rs := fun v Ψ hΨ => GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std v Ψ hΨ
  have hs : shiftB σ H H' 1 = Matrix.vecMulVec (incV F H.y) (incV F H'.x) := by
    rw [shiftB, Units.val_one, map_one, one_smul]
  have hw : mat u⁻¹ * shiftB σ H H' 1 = Matrix.vecMulVec (c • incV F H.x) (incV F H'.x) +
      (Matrix.vecMulVec (incM F H.ι *ᵥ β) (incV F H'.x) + Matrix.vecMulVec (incV F H.y) (incV F H'.x)) := by
    rw [hs, Matrix.mul_vecMulVec, hy, ← Matrix.add_vecMulVec, ← Matrix.add_vecMulVec]
    congr 1
    abel
  have hsh : mat u * (mat u⁻¹ * shiftB σ H H' 1) = shiftB σ H H' 1 := by
    rw [← Matrix.mul_assoc, GlobalTheory.LeviDecomp.mat_mul_inv', Matrix.one_mul]
  have h1 : om' (u * g, h) Φ = om' (u, 1) (om' (g, h) Φ) := by rw [← om_mul, one_mul]
  have h2 := evLaw_left hK hC he' hT hT₁ (GlobalTheory.ThK.Check.isLevi_one H) hu (rs (mat u⁻¹ * shiftB σ H H' 1) _ hΨ)
  simp only [mul_one, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul,
    Prod.mk_one_one, Module.End.one_apply] at h2
  have hi1 : Matrix.vecMulVec (c • incV F H.x) (incV F H'.x) ∈ isoB H H' := by
    refine Or.inl ⟨c • incV F H'.x, ?_⟩
    rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]
  have hi2 : Matrix.vecMulVec (incM F H.ι *ᵥ β) (incV F H'.x) ∈ isoB H H' := Or.inr ⟨β, rfl⟩
  have key : e' (G.M'.co.rho B.ψ (shiftB σ H H' 1) (om' (u, 1) (om' (g, h) Φ))) =
      e' (G.M'.co.rho B.ψ (shiftB σ H H' 1) (om' (g, h) Φ)) := by
    conv_lhs => rw [← hsh, ← actAB_left (W := G.W), ← hS.impl (u, 1) _ _ hΨ, h2, hw]
    rw [← GlobalTheory.MixW.UnipHeis.rho_rho G.M'.co B.ψ _ _
        (by rw [← Matrix.add_vecMulVec]; exact symp_right_zero _ _ _ hC.hH'.xx _ _),
      he'.inv _ hi1 _ (rs _ _ hΨ),
      ← GlobalTheory.MixW.UnipHeis.rho_rho G.M'.co B.ψ _ _ (symp_right_zero _ _ _ hC.hH'.xx _ _),
      he'.inv _ hi2 _ (rs _ _ hΨ), hs]
  rw [wTerm, wTerm, h1, key]

end Laws

section Right

private theorem rat_fix_decomp {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {r s i₀ i₁ : ℕ}
    (hcm : IsCMExt F E σ) (hW : W.IsSkew σ B r s) (hH : H'.IsAdapted σ B W W₁ i₀ i₁) {δ : UA σ W.J} (hδ : δ ∈ ratU σ W.J)
    (hx : mat δ *ᵥ incV F H'.x = incV F H'.x) :
    ∃ n ∈ unip σ W H', ∃ h₁ ∈ ratU σ W₁.J, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' 1 h₁ m ∧ δ = n * m := by
  obtain ⟨n, hn, m₁, hm₁, h₁, m₂, hm₂, hδe⟩ := GlobalTheory.StabLineLevi.stab_line_eq_unip_mul_levi F E σ B W W₁ H' r s i₀ i₁ hcm hW hH
    δ 1 (by rw [hx, Units.val_one, one_smul])
  have hm := GlobalTheory.FoldLine.levi_mul H' hm₁ hm₂
  rw [one_mul, one_mul] at hm
  refine ⟨n, hn, h₁, ?_, m₁ * m₂, hm, by rw [hδe, mul_assoc]⟩
  obtain ⟨π, hπι, hD, -⟩ := GlobalTheory.PlaneFrame.frame_dual_gram F E σ B d W r s d₁ W₁ H' i₀ i₁ hcm hW hH
  have hπx : π *ᵥ H'.x = 0 := GlobalTheory.StabLineLevi.proj_x (c := σ.toRingHom) hD hπι hH.xx hH.xy
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hfi : Function.Injective f := Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  have hπιa : incM F π * incM F H'.ι = 1 := by
    rw [← GlobalTheory.LeviUnitary.incM_mul, hπι, GlobalTheory.StabLineLevi.incM_one]
  have hπxa : incM F π *ᵥ incV F H'.x = 0 := by
    rw [GlobalTheory.LeviUnitary.incM_mulVec, hπx, GlobalTheory.StabLineLevi.incV_zero]
  have hπn : incM F π * mat n * incM F H'.ι = 1 := by
    have hz : ∀ z, (incM F π * mat n * incM F H'.ι) *ᵥ z = z := by
      intro z
      obtain ⟨c, hc⟩ := (GlobalTheory.LeviDecomp.prop_of_mem_unip H' hn).2 z
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_add, Matrix.mulVec_smul, hπxa, smul_zero,
        add_zero, Matrix.mulVec_mulVec, hπιa, Matrix.one_mulVec]
    ext i j
    have := congrFun (hz (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
  obtain ⟨g, hg⟩ := (Subgroup.mem_subgroupOf).1 hδ
  have hmq : mat δ = incM F (g : Matrix (Fin d) (Fin d) E) := by
    show ((δ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = _
    rw [← hg]; rfl
  have hh₁ : mat h₁ = incM F (π * (g : Matrix (Fin d) (Fin d) E) * H'.ι) := by
    rw [GlobalTheory.LeviUnitary.incM_mul, GlobalTheory.LeviUnitary.incM_mul, ← hmq, hδe, mul_assoc, GlobalTheory.LeviDecomp.mat_mul' n,
      ← Matrix.mul_assoc, Matrix.mul_assoc _ (mat (m₁ * m₂)), hm.2.2, ← Matrix.mul_assoc, hπn, Matrix.one_mul]
  have hdet : (π * (g : Matrix (Fin d) (Fin d) E) * H'.ι).det ≠ 0 := by
    intro h0
    have h1 : (mat h₁).det = 0 := by
      rw [hh₁, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    have h2 := congrArg Matrix.det (GlobalTheory.LeviDecomp.mat_mul_inv' h₁)
    rw [Matrix.det_mul, h1, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one (hfi (by rw [map_zero, map_one]; exact h2))
  exact Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, Units.ext hh₁.symm⟩

variable (hK : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H')
    {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)} (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W}
    (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁')
    {Φ : Fn F (b + 2) (a + (b + 2))} (hΦ : Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))))

include hK hT₁ in

private theorem theta_rat {Ξ : Fn F b (a + b)} (hΞ : Ξ ∈ schA F (Fin b × Fin (a + b))) {γ : UA σ G₁.V'.J} (hγ : γ ∈ ratU σ G₁.V'.J)
    {δ : UA σ G₁.W.J} (hδ : δ ∈ ratU σ G₁.W.J) : theta om₁' Ξ γ δ = thetaSum F Ξ := by
  have p1 := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2
  have h := ((GlobalTheory.T.theta_basic_properties hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p1).1 Ξ hΞ).2.1 γ hγ δ hδ 1 1
  rw [mul_one, mul_one] at h
  rw [h, theta, Prod.mk_one_one, map_one, Module.End.one_apply]

include hK hC he' hT hT₁ hΦ in

private theorem wTerm_right {δ : UA σ G.W.J} (hδ : δ ∈ ratU σ G.W.J) (hx : mat δ *ᵥ incV F H'.x = incV F H'.x)
    (g : UA σ G.V'.J) (h : UA σ G.W.J) : wTerm B G.M' H H' e' om' Φ g (δ * h) = wTerm B G.M' H H' e' om' Φ g h := by
  obtain ⟨n, hn, h₁, hh₁, m, hm, hδe⟩ := rat_fix_decomp hT.base.cm hT.geo.hW hC.hH' hδ hx
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hΨ := hS.pres (g, h) Φ hΦ
  have hΨ' := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std (shiftB σ H H' 1) _ hΨ
  have hsh : shiftB σ H H' 1 * (mat δ)ᵀ = shiftB σ H H' 1 := by
    rw [shiftB, Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hx]
  have h1 : om' (g, δ * h) Φ = om' (1, δ) (om' (g, h) Φ) := by rw [← om_mul, one_mul]
  have h2 := GlobalTheory.T.config_b_levi_torus_evaluation hK F E σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ 1 h₁ m hm n hn _ hΨ'
  simp only [mul_one, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at h2
  rw [← hδe] at h2
  have h3 := theta_rat hK hT₁ (he'.maps _ hΨ') (one_mem _) hh₁
  rw [wTerm, wTerm, h1, ← h3, theta, ← h2, hS.impl (1, δ) _ _ hΨ, actAB_right, hsh]

include hK hC he' hT hT₁ hΦ in

private theorem wTerm_levi_rat {γ : UA σ G₁.V'.J} (hγ : γ ∈ ratU σ G₁.V'.J) {m : UA σ G.V'.J} (hm : IsLevi H 1 γ m)
    (g : UA σ G.V'.J) (h : UA σ G.W.J) : wTerm B G.M' H H' e' om' Φ (m * g) h = wTerm B G.M' H H' e' om' Φ g h := by
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hΨ := hS.pres (g, h) Φ hΦ
  have hΨ' := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std (shiftB σ H H' 1) _ hΨ
  rw [wTerm_levi hK hC he' hT hT₁ hΦ hm, theta_rat hK hT₁ (he'.maps _ hΨ') hγ (one_mem _), wTerm]
  simp

end Right

private theorem absE_pos (l : (AE F E)ˣ) : 0 < (absE F E l : ℝ) := by
  have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h1))

private theorem lintegral_fd_eq_iwasawa (B : Base F E) {n n₁ : ℕ} (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) {r s i₀ i₁ : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁)
    (μX : Measure (UA σ X.J)) (μ₁ : Measure (UA σ X₁.J)) (D₁ : Set (UA σ X₁.J)) (hμX : μX.IsHaarMeasure)
    (hμ₁ : μ₁.IsHaarMeasure) (hD₁ : IsFundamentalDomain (ratU σ X₁.J) D₁ μ₁) (K : Subgroup (UA σ X.J)) (μK : Measure K)
    (μ : Measure (AE F E)ˣ) (hK : IsStab (X := X) B K) (hμK : μK.IsHaarMeasure) (hμ : μ.IsHaarMeasure)
    (m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J) (hm : ∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀)) (Q : Subgroup (UA σ X.J))
    (hQ : ∀ q, q ∈ Q ↔ q ∈ ratU σ X.J ∧ mat q *ᵥ incV F H.x = incV F H.x) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ 𝓓 : Set (UA σ X.J), IsFundamentalDomain Q 𝓓 μX → ∀ f : UA σ X.J → ℝ≥0∞, Measurable f →
      (∀ q ∈ Q, ∀ g, f (q * g) = f g) → (∀ u ∈ unip σ X H, ∀ g, f (u * g) = f g) →
      ∫⁻ g in 𝓓, f g ∂μX = C * ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in D₁,
        f (m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ∂μ₁ ∂μ ∂μK := by
  have hXY : (reS X X).IsHerm σ B r s := hX
  have hH' : H.IsAdapted σ B (reS X X) X₁ i₀ i₁ := hH
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  obtain ⟨hTG₁, hLC₁, hSC₁, hT2₁⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n₁ X₁.J
  obtain ⟨hTGi, hLCi, hSCi⟩ := GlobalTheory.FoldLine.units_lcsc F E
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ X₁.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI := hμX
  haveI := hμ₁
  haveI := hμ
  haveI : SFinite μ₁ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ₁)
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ)
  haveI : Countable (ratU σ X.J) := GlobalTheory.QDom.countable_ratU σ X.J
  haveI : Countable (ratU σ X₁.J) := GlobalTheory.QDom.countable_ratU σ X₁.J
  obtain ⟨μN, c, hμN, hc0, hcT, hform⟩ := GlobalTheory.T.levi_haar_stabilizer_measure F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hXY hH' μX μ₁ hμX hμ₁ K μK μ hK hμK hμ m hm
  haveI := hμN
  have hx0 : H.x ≠ 0 := fun h0 => by
    have h1 := hH.xy
    rw [h0] at h1
    simp [form] at h1
  have hcl := GlobalTheory.UnipClosed.isClosed_unip F E σ n n₁ X H hx0
  haveI : SecondCountableTopology (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  obtain ⟨𝓕, h𝓕, h𝓕0, h𝓕top⟩ := GlobalTheory.T.exists_unip_fundamentalDomain_finite_pos_measure F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hXY hH' μN hμN
  have hQr : Q ≤ ratU σ X.J := fun q hq => ((hQ q).1 hq).1
  have hQc : Countable Q := (Subgroup.inclusion_injective hQr).countable
  have hsub : Q.subgroupOf (unip σ X H) = (ratU σ X.J).subgroupOf (unip σ X H) := by
    ext u
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => hQr h, fun h => (hQ _).2 ⟨h, GlobalTheory.FoldLine.unip_fix X H _ u.2⟩⟩
  have h𝓕' : IsFundamentalDomain (Q.subgroupOf (unip σ X H)) 𝓕 μN := by rw [hsub]; exact h𝓕
  have hmulm : ∀ l g₀, ∀ γ ∈ ratU σ X₁.J, m l (γ * g₀) = m 1 γ * m l g₀ := by
    intro l g₀ γ _
    refine GlobalTheory.T.levi_element_unique_bis F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hXY hH' l (γ * g₀) _ _ (hm l (γ * g₀)) ?_
    simpa only [one_mul] using GlobalTheory.FoldLine.levi_mul H (hm 1 γ) (hm l g₀)
  have hιQ : ∀ γ ∈ ratU σ X₁.J, m 1 γ ∈ Q := by
    intro γ hγ
    refine (hQ _).2 ⟨GlobalTheory.T.levi_map_preserves_rational_points F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hXY hH' m hm γ hγ, ?_⟩
    rw [(hm 1 γ).1, Units.val_one, one_smul]
  have huniq : ∀ q ∈ Q, ∃! γ : ratU σ X₁.J, (m 1 γ)⁻¹ * q ∈ unip σ X H := fun q hq =>
    GlobalTheory.T.levi_rational_point_vector_action F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hXY hH' m hm q ((hQ q).1 hq).1 ((hQ q).1 hq).2
  have hcont := GlobalTheory.FoldLine.levi_cont B X X X₁ H hXY hH' m hm
  have hjoint : Measurable (fun p : unip σ X H × UA σ X₁.J × (AE F E)ˣ × K => p.1.1 * m p.2.2.1 p.2.1 * p.2.2.2.1) := by
    apply Continuous.measurable
    exact ((continuous_subtype_val.comp continuous_fst).mul
      (hcont.comp ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk (continuous_fst.comp continuous_snd)))).mul
      (continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  have hw : Measurable fun l : (AE F E)ˣ => ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) :=
    ENNReal.measurable_ofReal.comp ((NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).measurable.pow_const _)
  have hw0 : ∀ l : (AE F E)ˣ, ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ≠ 0 := fun l =>
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (absE_pos l) _)).ne'
  refine ⟨c * μN 𝓕, mul_ne_zero hc0 h𝓕0, ENNReal.mul_ne_top hcT h𝓕top, ?_⟩
  intro 𝓓 h𝓓 f hf hfQ hfN
  exact GlobalTheory.UnfoldSemidirect.lintegral_fundamentalDomain_eq μX μ₁ μ μK (unip σ X H) Q (ratU σ X₁.J) μN (fun k : K => k.1) m
    (fun γ => m 1 γ) (fun l => ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ)))) c D₁ 𝓕
    hQc inferInstance inferInstance inferInstance (fun g => (continuous_mul_left g).measurable)
    (fun g => (continuous_mul_left g).measurable) (fun g => (continuous_mul_right g).measurable) hjoint hw hw0
    (fun _ => ENNReal.ofReal_ne_top) inferInstance hform hc0 hcT hmulm hιQ huniq
    (fun γ _ f hf => GlobalTheory.T.unipotent_haar_levi_decomposition F E σ B n n₁ X X X₁ H r s i₀ i₁ hB hX hXY hH' m hm μN hμN γ f hf)
    inferInstance h𝓕' h𝓕0 h𝓕top hD₁ inferInstance 𝓓 h𝓓 f hf hfQ hfN

private theorem exists_isoV {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : Fin n → E} (hx0 : x ≠ 0) (hxx : form σ J x x = 0)
    {γ : UA σ J} (hγ : γ ∈ ratU σ J) : ∃ w : IsoV σ J, incV F w.1 = mat γ *ᵥ incV F x := by
  obtain ⟨g, hg⟩ := (Subgroup.mem_subgroupOf).1 hγ
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hfi : Function.Injective f := Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  have hcf : ∀ e, cA σ (f e) = f (σ e) := fun e => rfl
  set A : Matrix (Fin n) (Fin n) E := (g : Matrix (Fin n) (Fin n) E) with hA
  have hmq : mat γ = A.map f := by
    show ((γ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = _
    rw [← hg]; rfl
  have hmapσ : (A.map f).map (cA σ) = (A.map σ).map f := by
    ext i j; simp [hcf]
  have hgu : Aᵀ * J * A.map σ = J := by
    have h2 : (mat γ)ᵀ * incM F J * (mat γ).map (cA σ) = incM F J := γ.2
    rw [hmq, hmapσ] at h2
    have h3 : (Aᵀ * J * A.map σ).map f = J.map f := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]; exact h2
    exact Matrix.map_injective hfi h3
  refine ⟨⟨A *ᵥ x, fun h0 => hx0 ?_, ?_⟩, ?_⟩
  · have h1 : ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ (A *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hA, Units.inv_mul, Matrix.one_mulVec]
    rw [← h1, h0, Matrix.mulVec_zero]
  · have h1 : (fun i => σ ((A *ᵥ x) i)) = A.map σ *ᵥ fun i => σ (x i) :=
      (GlobalTheory.StabLineLevi.map_mulVec_conj σ.toRingHom A x).symm
    rw [form, h1, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, hgu]
    exact hxx
  · rw [hmq]
    exact (GlobalTheory.LeviUnitary.incM_mulVec A x).symm

private theorem iwaHt_fix {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {K : Subgroup (UA σ J)} {x : Fin n → E} {hf : UA σ J → ℝ}
    (hiw : GlobalTheory.ConeSmall.IsIwaHt K x hf)
    (hdec : ∀ g, ∃ (p k : UA σ J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F x = l.1 • incV F x ∧ g = p * k)
    {q : UA σ J} (hq : mat q *ᵥ incV F x = incV F x) (g : UA σ J) : hf (q * g) = hf g := by
  obtain ⟨p, k, l, hk, hl, rfl⟩ := hdec g
  rw [hiw p k l hk hl, ← mul_assoc]
  refine hiw _ k l hk ?_
  rw [GlobalTheory.LeviDecomp.mat_mul', ← Matrix.mulVec_mulVec, hl, Matrix.mulVec_smul, hq]

theorem _root_.GlobalTheory.T.seesaw_evaluation_haar_convergence : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ γ, IsWitt (σ := σ) (J := G.W.J) H'.x γ →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    ∀ hf : UA σ G.V'.J → ℝ, GlobalTheory.ConeSmall.IsIwaHt K H.x hf → (∀ g, ∃ (p k : UA σ G.V'.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k) →
    ∀ (s : ℂ) (T : Set (UA σ G.W.J)), GlobalTheory.ConeSmallCT.IsReps T H'.x →
    ∃ 𝓓₁ : Set (UA σ G.V'.J), IsFundamentalDomain (GlobalTheory.ConeSmallClaim.ratFix σ G.V'.J H.x) 𝓓₁ G.M'.μ ∧ ∃ C : ENNReal, C ≠ ⊤ ∧
      ∃ φ : T → IsoV σ G.W.J, (∀ (t t' : T) (ξ : Eˣ), (φ t).1 = (ξ : E) • (φ t').1 → t = t') ∧
        ∀ (t : T) (h : UA σ G.W.J),
          ENNReal.ofReal ‖GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) (t.1 * h)‖ ≤
            C * ∫⁻ g in 𝓓₁, ENNReal.ofReal (‖termW B G.M' H H' e' om' Φ' γ (φ t) g h‖ * hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2)) ∂G.M'.μ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ γ hγ X om om' om₁ om₁' hT hT₁ Φ' hΦ' hf hiw hdec s T hR
  have hP := hKP.base
  have hΦ : Φ' ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) := GlobalTheory.ConeTermCont.polData_le B G.M' hT.geo.hM' hΦ'.1
  have hB := hT.base
  have hV := hT.geo.hV'
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  choose m hm using GlobalTheory.LeviFrameH.exists_levi_herm F E σ B _ _ G.V' G₁.V' H _ _ _ _ hB hV hC.hH
  obtain ⟨C, hC0, hCt, hCf⟩ := lintegral_fd_eq_iwasawa B G.V' G₁.V' H hB hV hC.hH G.M'.μ G₁.M'.μ G₁.M'.dom hT.geo.hM'.haar
    hT₁.geo.hM'.haar hT₁.geo.hM'.dom K μK μ hK hμK hμ m hm (GlobalTheory.ConeSmallClaim.ratFix σ G.V'.J H.x) (fun _ => Iff.rfl)

  obtain ⟨𝓓, h𝓓⟩ : ∃ 𝓓 : Set (UA σ G.V'.J), IsFundamentalDomain (GlobalTheory.ConeSmallClaim.ratFix σ G.V'.J H.x) 𝓓 G.M'.μ := by
    haveI := GlobalTheory.QDom.countable_ratU σ G.V'.J
    haveI := hT.geo.hM'.haar
    have h := GlobalTheory.QDom.isFundamentalDomain_inf (GlobalTheory.QDom.measurable_mul_left σ G.V'.J)
      (fun g => map_mul_left_eq_self G.M'.μ g) hT.geo.hM'.dom (GlobalTheory.ConeSmallClaim.ratFix σ G.V'.J H.x)
    have hle : GlobalTheory.ConeSmallClaim.ratFix σ G.V'.J H.x ≤ ratU σ G.V'.J := fun q hq => hq.1
    rwa [inf_eq_right.2 hle] at h

  have hx0 : H'.x ≠ 0 := fun h0 => by
    have h1 := hC.hH'.xy
    rw [h0] at h1
    simp [form] at h1
  have hφ : ∀ t : T, ∃ w : IsoV σ G.W.J, incV F w.1 = mat (t.1)⁻¹ *ᵥ incV F H'.x := fun t =>
    exists_isoV hx0 hC.hH'.xx (inv_mem (hR.1 t.2))
  choose φ hφ using hφ
  refine ⟨𝓓, h𝓓, C⁻¹, ENNReal.inv_ne_top.2 hC0, φ, ?_, ?_⟩
  · intro t t' ξ hξ
    obtain ⟨t₀, -, huniq⟩ := hR.2 t.1 (hR.1 t.2)
    have h1 : t.1 = t₀ := huniq _ ⟨t.2, 1, by
      rw [mul_inv_cancel, GlobalTheory.LeviDecomp.mat_one', Matrix.one_mulVec, Units.val_one, one_smul]⟩
    let l : (AE F E)ˣ := Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom ξ
    have h3 : incV F (φ t).1 = l.1 • incV F (φ t').1 := by
      rw [hξ]
      funext i
      exact map_mul (inclR (F := F) (E := E) (AF F)) _ _
    have h4 : incV F (φ t').1 = (l⁻¹).1 • incV F (φ t).1 := by
      rw [h3, smul_smul, Units.inv_mul, one_smul]
    have h2 : t'.1 = t₀ := huniq _ ⟨t'.2, l⁻¹, by
      rw [GlobalTheory.LeviDecomp.mat_mul', ← Matrix.mulVec_mulVec, ← hφ t', h4, Matrix.mulVec_smul, hφ t, Matrix.mulVec_mulVec,
        GlobalTheory.LeviDecomp.mat_mul_inv', Matrix.one_mulVec]⟩
    exact Subtype.ext (h1.trans h2.symm)
  intro t h
  have hterm : ∀ g, termW B G.M' H H' e' om' Φ' γ (φ t) g h = wTerm B G.M' H H' e' om' Φ' g (t.1 * h) := by
    intro g
    have hδ : γ (φ t) * (t.1)⁻¹ ∈ ratU σ G.W.J := mul_mem (hγ _).1 (inv_mem (hR.1 t.2))
    have hδx : mat (γ (φ t) * (t.1)⁻¹) *ᵥ incV F H'.x = incV F H'.x := by
      rw [GlobalTheory.LeviDecomp.mat_mul', ← Matrix.mulVec_mulVec, ← hφ t, (hγ _).2]
    rw [← wTerm_right hP hC he' hT hT₁ hΦ hδ hδx g (t.1 * h), mul_assoc, inv_mul_cancel_left]
    rfl
  simp only [hterm]
  set r : ℝ := s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2 with hr
  set f : UA σ G.V'.J → ℝ≥0∞ := fun g => ENNReal.ofReal (‖wTerm B G.M' H H' e' om' Φ' g (t.1 * h)‖ * hf g ^ r) with hfdef
  have hcont : Continuous hf := by
    obtain ⟨K', -, -, hK'stab, hK'cpt, -, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B _ G.V' _ _ hB hV
    have hKK : K = K' := Subgroup.ext fun g => (hK g).trans (hK'stab g).symm
    exact GlobalTheory.ConeSmallMeas.continuous_ht K (hKK ▸ hK'cpt) H.x hf hiw hdec
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp ((continuous_wTerm he' hT hT₁ hΦ (t.1 * h)).norm.measurable.mul
      (hcont.measurable.pow_const r))
  have hfN : ∀ u ∈ unip σ G.V' H, ∀ g, f (u * g) = f g := by
    intro u hu g
    simp only [hfdef]
    rw [wTerm_unip hP hC he' hT hT₁ hΦ hu, iwaHt_fix hiw hdec (GlobalTheory.FoldLine.unip_fix G.V' H u hu)]
  have hfQ : ∀ q ∈ GlobalTheory.ConeSmallClaim.ratFix σ G.V'.J H.x, ∀ g, f (q * g) = f g := by
    intro q hq g
    obtain ⟨γ₀, hγ₀, -⟩ := GlobalTheory.T.levi_rational_point_vector_action F E σ B _ _ G.V' G.V' G₁.V' H _ _ _ _ hB hV hV hC.hH m hm q hq.1 hq.2
    simp only [hfdef]
    rw [iwaHt_fix hiw hdec hq.2, show q * g = m 1 γ₀.1 * (((m 1 γ₀.1)⁻¹ * q) * g) by group,
      wTerm_levi_rat hP hC he' hT hT₁ hΦ γ₀.2 (hm 1 γ₀.1), wTerm_unip hP hC he' hT hT₁ hΦ hγ₀]
  rw [hCf 𝓓 h𝓓 f hfm hfQ hfN, ← mul_assoc, ENNReal.inv_mul_cancel hC0 hCt, one_mul, ofReal_norm_eq_enorm,
    GlobalTheory.ConeSmall.coneI]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun k => ?_)
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun l => ?_)
  have hl := absE_pos l
  have hpt : ∀ g₀, f (m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) =
      ‖theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, t.1 * h) Φ'))) g₀ 1‖ₑ *
        ENNReal.ofReal ((absE F E l : ℝ) ^ (s + ((a : ℂ) + 1) / 2).re) := by
    intro g₀
    simp only [hfdef]
    rw [wTerm_levi hP hC he' hT hT₁ hΦ (hm l g₀), hiw _ _ l k.2 (hm l g₀).1, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (norm_nonneg _), norm_mul, norm_mul, Circle.norm_coe,
      one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    congr 1
    have he : (s + ((a : ℂ) + 1) / 2).re = (((a + (b + 2) : ℕ) : ℝ) / 2) + r + (1 - ((b + 2 : ℕ) : ℝ)) := by
      have : ((a : ℂ) + 1) / 2 = ((((a : ℝ) + 1) / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.add_re, Complex.ofReal_re, hr]
      push_cast
      ring
    rw [he, Real.rpow_add hl (_ + r), Real.rpow_add hl _ r]
    ring
  simp only [hpt]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, enorm_mul, enorm_mul, ← ofReal_norm_eq_enorm (X.ν l : ℂ),
    Circle.norm_coe, ENNReal.ofReal_one, mul_one, ← ofReal_norm_eq_enorm (_ ^ _), Complex.norm_cpow_eq_rpow_re_of_pos hl]
  exact mul_le_mul_left (enorm_integral_le_lintegral_enorm _) _

end GlobalTheory.ConeBack

end
