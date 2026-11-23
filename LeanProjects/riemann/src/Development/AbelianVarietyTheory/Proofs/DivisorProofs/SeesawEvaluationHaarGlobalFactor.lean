import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFixLeRatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
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
import Development.AutomorphicArithmetic.DivisorFrames.SkewWittCompactDecomposition
import Development.AutomorphicArithmetic.DivisorFrames.UnipotentRationalHeightBound
import Development.AutomorphicArithmetic.DivisorFrames.CompactIntegralVectorHeight
import Development.AutomorphicArithmetic.DivisorFrames.IntegralVectorsHeightSummable
import Development.AutomorphicArithmetic.DivisorFrames.LocalThetaGeometryTriple
import Development.AutomorphicArithmetic.DivisorFrames.ThetaGeometryTripleIntegral
import Development.AutomorphicArithmetic.DivisorFrames.SymplecticDualDecayBound
import Development.AutomorphicArithmetic.DivisorFrames.ThetaGeometryTripleSchwartz
import Development.AutomorphicArithmetic.DivisorFrames.ThetaSchwartzBruhatBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenIntegralHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace UpperTheory.Dv.ConeEst

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
  obtain ⟨g1, g2⟩ := GlobalTheory.ThK.EvLawBLeft.globalLaw hK F E σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁
  have h1 : om' (u * m, 1) Ψ = om' (u, 1) (om' (m, 1) Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  rw [h1, g1 u hu _ ((IsUWeilPair.isUSplitting hT.weil').pres _ _ hΨ), g2 t g₀ m hm Ψ hΨ]
  rfl

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

private theorem iwaHt_fix {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {K : Subgroup (UA σ J)} {x : Fin n → E} {hf : UA σ J → ℝ}
    (hiw : GlobalTheory.ConeSmall.IsIwaHt K x hf)
    (hdec : ∀ g, ∃ (p k : UA σ J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F x = l.1 • incV F x ∧ g = p * k)
    {q : UA σ J} (hq : mat q *ᵥ incV F x = incV F x) (g : UA σ J) : hf (q * g) = hf g := by
  obtain ⟨p, k, l, hk, hl, rfl⟩ := hdec g
  rw [hiw p k l hk hl, ← mul_assoc]
  refine hiw _ k l hk ?_
  rw [GlobalTheory.LeviDecomp.mat_mul', ← Matrix.mulVec_mulVec, hl, Matrix.mulVec_smul, hq]

section RightLaw

variable (hK : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H')
    {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)} (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W}
    (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁')
    {Φ : Fn F (b + 2) (a + (b + 2))} (hΦ : Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))))

include hK hC he' hT hT₁ hΦ in

private theorem norm_theta_right {t : (AE F E)ˣ} {h₁ : UA σ G₁.W.J} {m : UA σ G.W.J} (hm : IsLevi H' t h₁ m)
    {u : UA σ G.W.J} (hu : u ∈ unip σ G.W H') {δ : UA σ G₁.W.J} (hδ : δ ∈ ratU σ G₁.W.J) (k : UA σ G.V'.J)
    (κ : UA σ G.W.J) (l : (AE F E)ˣ) (g₀ : UA σ G₁.V'.J) :
    ‖theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k, u * m * κ) Φ))) g₀ 1‖ =
      (absE F E t : ℝ) ^ ((b : ℝ) / 2) * ‖theta om₁' (e' (G.M'.co.rho B.ψ
        (shiftB σ H H' (l * (Units.map (cA σ).toMonoidHom t)⁻¹)) (om' (k, κ) Φ))) g₀ (δ * h₁)‖ := by
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hΨ := hS.pres (k, κ) Φ hΦ
  have hΨ' := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std
    (shiftB σ H H' (l * (Units.map (cA σ).toMonoidHom t)⁻¹)) _ hΨ
  have hx : mat (u * m) *ᵥ incV F H'.x = t.1 • incV F H'.x := by
    rw [GlobalTheory.LeviDecomp.mat_mul', ← Matrix.mulVec_mulVec, hm.1, Matrix.mulVec_smul, GlobalTheory.FoldLine.unip_fix G.W H' u hu]
  have hsh : shiftB σ H H' (l * (Units.map (cA σ).toMonoidHom t)⁻¹) * (mat (u * m))ᵀ = shiftB σ H H' l := by
    rw [shiftB, shiftB, Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hx, Matrix.vecMulVec_smul, smul_smul]
    congr 1
    have e1 : (t : AE F E) = cA σ ((Units.map (cA σ).toMonoidHom t : (AE F E)ˣ) : AE F E) := by
      simp [GlobalTheory.ConeSmallLaw.cA_cA hT.base.cm]
    rw [Units.val_mul, map_mul, mul_assoc, e1, ← map_mul, Units.inv_mul, map_one, mul_one]
  have h1 : om' (k, u * m * κ) Φ = om' (1, u * m) (om' (k, κ) Φ) := by rw [← om_mul, one_mul]
  have h2 := GlobalTheory.T.config_b_levi_torus_evaluation hK F E σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ t h₁ m hm u hu _ hΨ'
  have p1 := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2
  have h3 := ((GlobalTheory.T.theta_basic_properties hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p1).1 _ (he'.maps _ hΨ')).2.1 1 (one_mem _) δ hδ g₀ h₁
  rw [one_mul] at h3
  rw [h3, h1, ← hsh, ← actAB_right (X := G.V'), ← hS.impl (1, u * m) _ _ hΨ, h2, theta, theta, map_smul, thetaSum_smul',
    ← om_mul, mul_one, one_mul, norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

end RightLaw

private theorem num_bound {T y c c' j β : ℝ} {M M' : ℕ} (hT : 0 < T) (hy : 0 ≤ y) (hc : 0 ≤ c) (hj : 0 ≤ j)
    (h : y * T ^ M' ≤ c') : T ^ β * (c * j * y ^ M) ≤ c * max c' 0 ^ M * T ^ (β - ((M' * M : ℕ) : ℝ)) * j := by
  have h1 : y ^ M * T ^ (M' * M) ≤ max c' 0 ^ M := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (h.trans (le_max_left _ _)) M
  have h2 : T ^ β = T ^ (M' * M) * T ^ (β - ((M' * M : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hT]; congr 1; ring
  have h3 : 0 ≤ T ^ (β - ((M' * M : ℕ) : ℝ)) := by positivity
  rw [h2]
  calc _ = c * (y ^ M * T ^ (M' * M)) * T ^ (β - ((M' * M : ℕ) : ℝ)) * j := by ring
    _ ≤ _ := by gcongr

private theorem lineSum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (N : ℝ), (d : ℝ) < N → ∀ C : Set (Fin d → AE F E), IsCompact C → ∃ A : (Fin d → E) → ENNReal,
    (∀ R : Set (Fin d → E), (∀ w ∈ R, ∀ w' ∈ R, ∀ ξ : Eˣ, w = (ξ : E) • w' → w = w') → ∑' w : R, A w ≠ ⊤) ∧
    ∀ (w : Fin d → E) (t : (AE F E)ˣ), w ≠ 0 → t.1 • incV F w ∈ C → ENNReal.ofReal ((absE F E t : ℝ) ^ N) ≤ A w := by
  intro F E _ _ _ _ _ d N hN C hC
  classical
  obtain ⟨m, c, hm, hl⟩ := UpperTheory.compact_integral_vector_height F E d C hC
  set n := Module.finrank ℚ E with hn
  have hn0 : 0 < n := Module.finrank_pos
  have hN0 : 0 < N := lt_of_le_of_lt (Nat.cast_nonneg d) hN
  have hs := UpperTheory.integral_vectors_height_summable E d (n * N) (by
    rw [Nat.cast_mul, mul_comm]; exact mul_lt_mul_of_pos_left hN (by exact_mod_cast hn0))
  let sz : (Fin d → E) → ℝ := fun v => ∑ i, ∑ φ : E →+* ℂ, ‖φ (v i)‖
  have hsz0 : ∀ v, 0 ≤ sz v := fun v => by positivity
  let bb : {v : Fin d → E // ∀ i, IsIntegral ℤ (v i)} → ℝ≥0∞ := fun v =>
    ENNReal.ofReal ((max c 0 * (m : ℝ) ^ n) ^ N * sz v.1 ^ (-(n * N)))
  have hbb : ∑' v, bb v ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun v => mul_nonneg (by positivity) (Real.rpow_nonneg (hsz0 _) _)) (hs.mul_left _)]
    exact ENNReal.ofReal_ne_top
  refine ⟨fun w => ∑' v : {v : Fin d → E // ∀ i, IsIntegral ℤ (v i)}, if ∃ ξ : Eˣ, v.1 = (ξ : E) • w then bb v else 0,
    fun R hR => ?_, fun w t hw ht => ?_⟩
  · rw [ENNReal.tsum_comm]
    refine ne_top_of_le_ne_top hbb (ENNReal.tsum_le_tsum fun v => ?_)
    by_cases h : ∃ w : R, ∃ ξ : Eˣ, v.1 = (ξ : E) • w.1
    · obtain ⟨w₀, ξ₀, h₀⟩ := h
      rw [tsum_eq_single w₀ fun w hw => if_neg ?_]
      · split_ifs
        · exact le_rfl
        · exact zero_le
      · rintro ⟨ξ, hξ⟩
        refine hw (Subtype.ext (hR _ w.2 _ w₀.2 (ξ⁻¹ * ξ₀) ?_))
        rw [Units.val_mul, mul_smul, ← h₀, hξ, smul_smul, Units.inv_mul, one_smul]
    · rw [ENNReal.tsum_eq_zero.2 fun w => if_neg fun h' => h ⟨w, h'⟩]
      exact zero_le
  · obtain ⟨ξ, hint, hb⟩ := hl w t ht
    have hmE : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
    let v : {v : Fin d → E // ∀ i, IsIntegral ℤ (v i)} := ⟨fun i => (m : E) * ((ξ : E) * w i), hint⟩
    refine le_trans ?_ (ENNReal.le_tsum v)
    rw [if_pos ⟨Units.mk0 _ hmE * ξ, funext fun i => by simp [v, mul_assoc]⟩]
    apply ENNReal.ofReal_le_ofReal
    have e1 : sz v.1 = m * ∑ i, ∑ φ : E →+* ℂ, ‖φ ((ξ : E) * w i)‖ := by
      simp only [sz, v, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun φ _ => ?_
      rw [map_mul φ (m : E), norm_mul, map_natCast, Complex.norm_natCast]
    have hpos : 0 < sz v.1 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h1 : 0 < ‖φ (v.1 i)‖ := norm_pos_iff.2 ((map_ne_zero φ).2 (mul_ne_zero hmE (mul_ne_zero ξ.ne_zero hi)))
      refine h1.trans_le ((Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ (v.1 i)‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ φ)).trans ?_)
      exact Finset.single_le_sum (f := fun i => ∑ φ : E →+* ℂ, ‖φ (v.1 i)‖) (fun _ _ => by positivity) (Finset.mem_univ i)
    have h2 : (absE F E t : ℝ) * sz v.1 ^ n ≤ max c 0 * (m : ℝ) ^ n := by
      rw [e1, mul_pow, mul_left_comm, mul_comm (max c 0)]
      exact mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _)) (by positivity)
    have h3 := Real.rpow_le_rpow (by positivity) h2 hN0.le
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (by positivity), ← Real.rpow_natCast (sz v.1), ← Real.rpow_mul hpos.le] at h3
    rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hpos _)]
    exact h3

private theorem coneBound : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ G.M'.So B.ψ B.τ₁, ∀ C : Set (UA σ G.V'.J × UA σ G.W.J), IsCompact C →
    ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧ ∃ M : ℕ, ∀ N : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ p ∈ C, ∀ (l : (AE F E)ˣ) g₀ h₁,
      ‖theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' p Ψ))) g₀ h₁‖ ≤ c * (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal * (ht h₁ : ℝ) ^ M := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ Ψ hΨ C hCc
  have hS : Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) := by
    refine Submodule.span_le.mpr ?_ hΨ
    rintro _ ⟨f, φ, hφ, hv, -, rfl⟩
    refine GlobalTheory.TensUniq.pure_mem_schA f φ hφ ?_
    filter_upwards [hv, hT.geo.hM'.std] with v h1 h2
    rw [h1, h2]
  obtain ⟨U, hU, hUz⟩ := UpperTheory.local_theta_geometry_triple F E σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ Ψ hS C hCc
  obtain ⟨m, c, φ, hφ, hdec⟩ := UpperTheory.theta_geometry_triple_integral F E σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ Ψ hS C hCc
  obtain ⟨C₀, k, hC₀, hb⟩ := UpperTheory.theta_schwartz_bruhat_bound hKP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2 m φ hφ
  refine ⟨U, hU, k, fun N => ?_⟩
  choose D hD using fun j =>
    UpperTheory.theta_geometry_triple_vanishing F E σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ Ψ hS C hCc U hU (c j) N k
  refine ⟨C₀ * ∑ j, |D j|, by positivity, fun p hp l g₀ h₁ => ?_⟩
  by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U
  · set P : ℝ := (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) with hP
    have hP0 : 0 ≤ P := by positivity
    have hmaj : (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal = P := by
      rw [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem hl, ENNReal.toReal_ofReal hP0]
    choose f hf1 hf2 using fun j => hD j p hp l hl
    have e : e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' p Ψ)) = ∑ j, pureA F (f j) (φ j) := by
      funext x
      rw [hdec p hp l x, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [pureA, hf1, RingEquiv.symm_apply_apply]
    have hSo := UpperTheory.theta_geometry_triple_schwartz F E σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ _
      (GlobalTheory.T.weil_representation_preserves_space hKP.base F E σ B a (b + 2) G X om om' hT p Ψ hΨ) l
    rw [e] at hSo
    rw [e, hmaj]
    refine (hb f hSo g₀ h₁).trans ?_
    rw [mul_assoc C₀ _ P, Finset.sum_mul]
    gcongr with j
    exact (hf2 j).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hP0)
  · rw [hUz p hp l hl]
    simp only [theta, map_zero, thetaSum, Pi.zero_apply, tsum_zero, norm_zero]
    positivity

end UpperTheory.Dv.ConeEst

open UpperTheory.Dv.ConeEst in
theorem _root_.GlobalTheory.T.seesaw_evaluation_haar_global_factor : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ γ, IsWitt (σ := σ) (J := G.W.J) H'.x γ →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    ∀ hf : UA σ G.V'.J → ℝ, GlobalTheory.ConeSmall.IsIwaHt K H.x hf → (∀ g, ∃ (p k : UA σ G.V'.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k) →
    ∃ s₁ : ℝ, ∀ r : ℝ, s₁ < r → ∀ S : Set (UA σ G.W.J), IsCompact S → ∃ A : IsoV σ G.W.J → ENNReal,
    (∀ R : Set (IsoV σ G.W.J), GlobalTheory.ConeSmallClaim.NonProp R → ∑' w : R, A w ≠ ⊤) ∧
    ∀ 𝓓₁ : Set (UA σ G.V'.J), IsFundamentalDomain (GlobalTheory.ConeSmallClaim.ratFix σ G.V'.J H.x) 𝓓₁ G.M'.μ → ∀ w, ∀ h ∈ S,
      ∫⁻ g in 𝓓₁, ENNReal.ofReal (‖termW B G.M' H H' e' om' Φ' γ w g h‖ * hf g ^ (r + (((b + 2 : ℕ) : ℝ) - 1) / 2)) ∂G.M'.μ ≤ A w := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ γ hγ X om om' om₁ om₁' hT hT₁ Φ' hΦ' hf hiw hdec
  have hP := hKP.base
  have hΦ : Φ' ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) := GlobalTheory.ConeTermCont.polData_le B G.M' hT.geo.hM' hΦ'.1
  have hB := hT.base
  have hV := hT.geo.hV'
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨hTG, -, -, -⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (a + (b + 2)) G.W.J
  obtain ⟨hTGi, hLCi, hSCi⟩ := GlobalTheory.FoldLine.units_lcsc F E
  choose m hm using GlobalTheory.LeviFrameH.exists_levi_herm F E σ B _ _ G.V' G₁.V' H _ _ _ _ hB hV hC.hH
  obtain ⟨C, hC0, hCt, hCf⟩ := lintegral_fd_eq_iwasawa B G.V' G₁.V' H hB hV hC.hH G.M'.μ G₁.M'.μ G₁.M'.dom hT.geo.hM'.haar
    hT₁.geo.hM'.haar hT₁.geo.hM'.dom K μK μ hK hμK hμ m hm (GlobalTheory.ConeSmallClaim.ratFix σ G.V'.J H.x) (fun _ => Iff.rfl)
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) := by
    obtain ⟨K', -, -, hK'stab, hK'cpt, -, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B _ G.V' _ _ hB hV
    have hKK : K = K' := Subgroup.ext fun g => (hK g).trans (hK'stab g).symm
    exact hKK ▸ hK'cpt
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hμKt : μK Set.univ ≠ ⊤ := isCompact_univ.measure_lt_top.ne
  have hdom : G₁.M'.μ G₁.M'.dom ≠ ⊤ :=
    (GlobalTheory.ThKContSmall.measure_dom_lt_top hKP.siegelSetUnitary hT₁.base hT₁.geo.hV' hT₁.geo.hM').ne
  have hcont : Continuous hf := GlobalTheory.ConeSmallMeas.continuous_ht K hKc H.x hf hiw hdec
  have hx0 : H'.x ≠ 0 := fun h0 => by
    have h1 := hC.hH'.xy
    rw [h0] at h1
    simp [form] at h1
  obtain ⟨CW, hCW, hIW⟩ := UpperTheory.skew_witt_compact_decomposition hKP.siegelSetUnitary F E σ B _ G.W _ _ hB hT.geo.hW H'.x hx0 hC.hH'.xx γ hγ
  obtain ⟨U, hU, M, hM⟩ := coneBound hKP F E σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ Φ' hΦ'.2 _ (hKc.prod hCW)
  obtain ⟨M', hM'⟩ := UpperTheory.unipotent_rational_height_bound hKP.siegelSetUnitary F E σ B _ _ G.W G₁.W H' _ _ _ _ _ _ hB hT.geo.hW hT₁.geo.hW hC.hH'
  refine ⟨1 + ((a + (b + 2) : ℕ) : ℝ) + ((M' * M : ℕ) : ℝ), fun r hr S hS => ?_⟩
  set z : ℝ := r + ((a : ℝ) + 1) / 2 with hz
  set β : ℝ := (b : ℝ) / 2 - ((M' * M : ℕ) : ℝ) with hβ
  have hz1 : 1 < z := by
    have : (0 : ℝ) ≤ ((a + (b + 2) : ℕ) : ℝ) := by positivity
    have : (0 : ℝ) ≤ ((M' * M : ℕ) : ℝ) := by positivity
    have : (0 : ℝ) ≤ ((a : ℝ) + 1) / 2 := by positivity
    linarith
  have hN : ((a + (b + 2) : ℕ) : ℝ) < β + z := by
    have : (0 : ℝ) ≤ ((a : ℝ) + 1) / 2 := by positivity
    have : (0 : ℝ) ≤ (b : ℝ) / 2 := by positivity
    linarith
  have hCs : IsCompact ((fun p : UA σ G.W.J × UA σ G.W.J => p.1 * p.2⁻¹) '' (CW ×ˢ S)) :=
    (hCW.prod hS).image (continuous_fst.mul continuous_snd.inv)
  obtain ⟨c', hc'⟩ := hM' _ hCs
  have hmc : Continuous fun g : UA σ G.W.J => mat g⁻¹ *ᵥ incV F H'.x :=
    ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_mulVec continuous_const
  obtain ⟨A₀, hA₀, hA₀b⟩ := lineSum F E _ _ hN _ (hCs.image hmc)
  obtain ⟨N₀, k₀, L, C₁, hk₀, hb⟩ := GlobalTheory.TateConv.bound F E hz1 hU
  have hTz : ∫⁻ l, GlobalTheory.XTermMaj.maj F E N₀ U (l : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ z) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono hb) (GlobalTheory.TateConv.lintegral_bound_lt_top F E μ hz1 hk₀ L C₁)).ne
  set Tz := ∫⁻ l, GlobalTheory.XTermMaj.maj F E N₀ U (l : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ z) ∂μ with hTzd
  obtain ⟨c, hc0, hc⟩ := hM N₀
  set D : ℝ≥0∞ := C * (ENNReal.ofReal (c * max c' 0 ^ M) * G₁.M'.μ G₁.M'.dom * Tz * μK Set.univ) with hD
  have hDt : D ≠ ⊤ := ENNReal.mul_ne_top hCt
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdom) hTz) hμKt)
  refine ⟨fun w => D * A₀ w.1, fun R hR => ?_, fun 𝓓 h𝓓 w h hh => ?_⟩
  · rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_ne_top hDt (ne_top_of_le_ne_top (hA₀ (Subtype.val '' R) ?_) ?_)
    · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩ ξ e
      rw [hR w hw w' hw' ξ e]
    · exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun w : R => (⟨w.1.1, w.1, w.2, rfl⟩ : Subtype.val '' R))
        (fun w w' e => Subtype.ext (Subtype.ext (congrArg (fun v : Subtype.val '' R => v.1) e))) (fun v => A₀ v.1)
  obtain ⟨p, κ, t, hκ, hp, hpe⟩ := hIW (γ w * h)
  obtain ⟨u, hu, m₁, hm₁, h₁, m₂, hm₂, rfl⟩ := GlobalTheory.StabLineLevi.stab_line_eq_unip_mul_levi F E σ B G.W G₁.W H' _ _ _ _ hB.cm
    hT.geo.hW hC.hH' p t hp
  have hmm := GlobalTheory.FoldLine.levi_mul H' hm₁ hm₂
  rw [mul_one, one_mul] at hmm
  rw [mul_assoc u] at hp hpe
  have hκh : κ * h⁻¹ ∈ (fun p : UA σ G.W.J × UA σ G.W.J => p.1 * p.2⁻¹) '' (CW ×ˢ S) := ⟨(κ, h), ⟨hκ, hh⟩, rfl⟩
  have hγe : γ w = u * (m₁ * m₂) * (κ * h⁻¹) := by rw [← mul_assoc, ← hpe, mul_inv_cancel_right]
  obtain ⟨δ, hδ, hht⟩ := hc' (γ w) (hγ w).1 u hu t h₁ _ hmm _ hκh hγe
  have hAw : ENNReal.ofReal ((absE F E t : ℝ) ^ (β + z)) ≤ A₀ w.1 := by
    refine hA₀b w.1 t w.2.1 ⟨_, hκh, ?_⟩
    have e1 : incV F w.1 = mat (γ w)⁻¹ *ᵥ incV F H'.x := by
      rw [← (hγ w).2, Matrix.mulVec_mulVec, ← GlobalTheory.LeviDecomp.mat_mul', inv_mul_cancel, GlobalTheory.LeviDecomp.mat_one',
        Matrix.one_mulVec]
    show mat (κ * h⁻¹)⁻¹ *ᵥ incV F H'.x = _
    rw [e1, ← Matrix.mulVec_smul, ← hp, Matrix.mulVec_mulVec, ← GlobalTheory.LeviDecomp.mat_mul', hγe]
    congr 2
    group
  set ρ : ℝ := r + (((b + 2 : ℕ) : ℝ) - 1) / 2 with hρ
  set f : UA σ G.V'.J → ℝ≥0∞ := fun g => ENNReal.ofReal (‖wTerm B G.M' H H' e' om' Φ' g (γ w * h)‖ * hf g ^ ρ) with hfdef
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp ((continuous_wTerm he' hT hT₁ hΦ (γ w * h)).norm.measurable.mul
      (hcont.measurable.pow_const ρ))
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
  set v : (AE F E)ˣ := (Units.map (cA σ).toMonoidHom t)⁻¹ with hv
  have ht := absE_pos (F := F) t
  set Y : ℝ≥0∞ := ENNReal.ofReal (c * max c' 0 ^ M) * ENNReal.ofReal ((absE F E t : ℝ) ^ (β + z)) with hY
  have hpt : ∀ (k : K) l g₀, f (m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ≤
      Y * (GlobalTheory.XTermMaj.maj F E N₀ U ((l * v : (AE F E)ˣ) : AE F E) * ENNReal.ofReal ((absE F E (l * v) : ℝ) ^ z)) := by
    intro k l g₀
    have hl := absE_pos (F := F) l
    have hlv : (absE F E l : ℝ) = absE F E t * absE F E (l * v) := by
      rw [map_mul, hv, map_inv, GlobalTheory.ConeSmallLaw.absE_cA, NNReal.coe_mul, NNReal.coe_inv]
      field_simp
    have hlv0 := absE_pos (F := F) (l * v)
    set j := (GlobalTheory.XTermMaj.maj F E N₀ U ((l * v : (AE F E)ˣ) : AE F E)).toReal with hj
    have hj0 : 0 ≤ j := ENNReal.toReal_nonneg
    have h1 := num_bound (β := (b : ℝ) / 2) (M := M) ht (NNReal.coe_nonneg _) hc0 hj0 hht
    have h2 := mul_le_mul_of_nonneg_left (hc (k.1, κ) ⟨k.2, hκ⟩ (l * v) g₀ (δ * h₁))
      (Real.rpow_nonneg ht.le ((b : ℝ) / 2))
    have h3 := h2.trans h1
    rw [← norm_theta_right hP hC he' hT hT₁ hΦ hmm hu hδ, ← hpe] at h3
    have h4 : ENNReal.ofReal j ≤ GlobalTheory.XTermMaj.maj F E N₀ U ((l * v : (AE F E)ˣ) : AE F E) := ENNReal.ofReal_toReal_le
    refine le_trans ?_ (mul_le_mul_right (mul_le_mul_left h4 _) _)
    simp only [hfdef]
    rw [wTerm_levi hP hC he' hT hT₁ hΦ (hm l g₀), hiw _ _ l k.2 (hm l g₀).1, hY,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hj0,
      ← ENNReal.ofReal_mul (by positivity), norm_mul, norm_mul, Circle.norm_coe,
      one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have he : z = (((a + (b + 2) : ℕ) : ℝ) / 2) + ρ + (1 - ((b + 2 : ℕ) : ℝ)) := by
      rw [hz, hρ]
      push_cast
      ring
    have e1 : (absE F E l : ℝ) ^ z = (absE F E l : ℝ) ^ (((a + (b + 2) : ℕ) : ℝ) / 2) * (absE F E l : ℝ) ^ ρ *
        (absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ)) := by
      rw [he, Real.rpow_add hl, Real.rpow_add hl]
    have e2 : (absE F E l : ℝ) ^ z = (absE F E t : ℝ) ^ z * (absE F E (l * v) : ℝ) ^ z := by
      rw [hlv, Real.mul_rpow ht.le hlv0.le]
    calc _ = ‖theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, γ w * h) Φ'))) g₀ 1‖ * (absE F E l : ℝ) ^ z := by
          rw [e1]; ring
      _ ≤ (c * max c' 0 ^ M * (absE F E t : ℝ) ^ β * j) * (absE F E l : ℝ) ^ z :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = _ := by rw [e2, Real.rpow_add ht β z]; ring
  have hYt : Y ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  calc ∫⁻ g in 𝓓, f g ∂G.M'.μ = _ := hCf 𝓓 h𝓓 f hfm hfQ hfN
    _ ≤ C * ∫⁻ _k : K, ∫⁻ l, ∫⁻ _g₀ in G₁.M'.dom, Y * (GlobalTheory.XTermMaj.maj F E N₀ U ((l * v : (AE F E)ˣ) : AE F E) *
          ENNReal.ofReal ((absE F E (l * v) : ℝ) ^ z)) ∂G₁.M'.μ ∂μ ∂μK :=
        mul_le_mul_right (lintegral_mono fun k => lintegral_mono fun l => lintegral_mono fun g₀ => hpt k l g₀) _
    _ = C * (Y * Tz * G₁.M'.μ G₁.M'.dom * μK Set.univ) := by
        simp only [setLIntegral_const]
        rw [lintegral_mul_const' _ _ hdom, lintegral_const_mul' _ _ hYt, lintegral_const,
          lintegral_mul_right_eq_self (fun l : (AE F E)ˣ => GlobalTheory.XTermMaj.maj F E N₀ U (l : AE F E) *
            ENNReal.ofReal ((absE F E l : ℝ) ^ z)) v]
    _ = D * ENNReal.ofReal ((absE F E t : ℝ) ^ (β + z)) := by rw [hD, hY]; ring
    _ ≤ D * A₀ w.1 := mul_le_mul_right hAw _

end
