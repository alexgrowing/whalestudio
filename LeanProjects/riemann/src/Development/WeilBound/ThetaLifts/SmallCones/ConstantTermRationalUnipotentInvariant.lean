import Development.WeilBound.ThetaLifts.SmallCones.KerPol
import Development.WeilBound.ThetaLifts.SmallCones.KerUni
import Development.WeilBound.ThetaLifts.TowerModels.PlaneForm

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open GlobalTheory.Doubling (absE)
open Matrix (vecMulVec)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
variable {H : Plane E n n₁} {H' : Plane E d d₁} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

def tm (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (H' : Plane E d d₁) {n₂ d₂ : ℕ} (e : Fn F n d →ₗ[ℂ] Fn F n₂ d₂)
    (U : Matrix (Fin n) (Fin d) E) (Φ : Fn F n d) (u : unip σ W H') : ℂ :=
  thetaSum F (e (M.co.rho B.ψ (incM F U) (om (1, u.1) Φ)))

section Gen

variable {n₂ d₂ : ℕ} {X₂ : Spc F E n₂} {W₂ : Spc F E d₂} {M₂ : Model σ X₂ W₂} {e : Fn F n d →ₗ[ℂ] Fn F n₂ d₂}
  {ι : Matrix (Fin n) (Fin n₂) E} {ι' : Matrix (Fin d) (Fin d₂) E} {I : Set (Ten F E n d)}

theorem tm_cont (hA : EvAdm) (hp : IsPair B M χX χW om r s r' s') (hM₂ : M₂.IsGood B.ψ) (he : IsEv B M M₂ ι ι' I e) (U) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : Continuous (tm B M om H' e U Φ) := by
  obtain ⟨⟨l, hl, hθ⟩, -, h⟩ := hA F E σ B n d n₂ d₂ X W X₂ W₂ M M₂ hp.base hp.good hM₂
  obtain ⟨l', hl', h'⟩ := h ι ι' I e he (incM F U) l hl
  have hc := ((IsUWeilPair.isUSplitting hp.weil).cont l' hl' Φ hΦ).comp
    (f := fun u : unip σ W H' => ((1 : UA σ X.J), u.1)) (continuous_const.prodMk continuous_subtype_val)
  refine hc.congr fun u => ?_
  rw [Function.comp_apply, h' _ (om_mem hp _ hΦ), hθ _ (he.maps _ (rho_mem M hp.base.std _ (om_mem hp _ hΦ)))]
  rfl

theorem tm_eq (hp : IsPair B M χX χW om r s r' s') (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, u) Φ) = e Φ)
    (U) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) (u : unip σ W H') :
    tm B M om H' e U Φ u = thetaSum F (e (M.co.rho B.ψ (incM F U * (mat u.1⁻¹)ᵀ) Φ)) := by
  rw [tm, rho_om hp _ _ hΦ, hi _ u.2 _ (rho_mem M hp.base.std _ hΦ)]

theorem tm_mul (U) (Φ) (u v : unip σ W H') : tm B M om H' e U Φ (u * v) = tm B M om H' e U (om (1, v.1) Φ) u := by
  rw [tm, tm, om_om]
  simp

theorem tm_one (U) (Φ) : tm B M om H' e U Φ 1 = thetaSum F (e (M.co.rho B.ψ (incM F U) Φ)) := by
  rw [tm, show ((1 : UA σ X.J), (1 : unip σ W H').1) = 1 from rfl, map_one]
  rfl

end Gen

variable (σ W H') in

structure MeanOK (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')) : Prop where
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  dom : IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ
  one : μ 𝓕 = 1
  cnt : Countable (ratU σ W.J)

variable {μ : Measure (unip σ W H')} {𝓕 : Set (unip σ W H')}

theorem MeanOK.zero (h : MeanOK σ W H' μ 𝓕) {f : unip σ W H' → ℂ} (hl : ∀ γ : unip σ W H', γ.1 ∈ ratU σ W.J → ∀ x, f (γ * x) = f x)
    {g} {c : ℂ} (hc : c ≠ 1) (hr : ∀ x, f (x * g) = c * f x) : ∫ x in 𝓕, f x ∂μ = 0 := by
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have := h.haar
  have := h.right
  have := h.cnt
  have : Countable ((ratU σ W.J).subgroupOf (unip σ W H')) :=
    Function.Injective.countable (f := fun x => (⟨x.1.1, x.2⟩ : ratU σ W.J)) fun a b e =>
      Subtype.ext (Subtype.ext (congrArg (fun y : ratU σ W.J => y.1) e))
  exact mean_zero _ μ h.dom hl hc hr

theorem MeanOK.sum (h : MeanOK σ W H' μ 𝓕) {ι : Type} [Countable ι] {f : ι → unip σ W H' → ℂ} (hf : ∀ i, Continuous (f i))
    {b : ι → ℝ} (hb : Summable b) (hfb : ∀ i x, ‖f i x‖ ≤ b i) {s : unip σ W H' → ℂ} (hs : ∀ x, HasSum (fun i => f i x) (s x)) :
    HasSum (fun i => ∫ x in 𝓕, f i x ∂μ) (∫ x in 𝓕, s x ∂μ) := by
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have hb' : BorelSpace (unip σ W H') := Subtype.borelSpace _
  exact @mean_hasSum (unip σ W H') _ _ hb' _ _ μ _ h.one _ hf _ hb hfb _ hs

theorem MeanOK.const (h : MeanOK σ W H' μ 𝓕) (c : ℂ) : ∫ _x in 𝓕, c ∂μ = c := by
  rw [setIntegral_const, Measure.real, h.one, ENNReal.toReal_one, one_smul]

theorem exists_psi {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) : ∃ a, ψ a ≠ 1 := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 (std_ne_one h)
  exact ⟨a, by simpa using ha⟩

theorem bf0 {R : Type} [CommRing R] {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} (u) : bf c J u 0 = 0 := by
  simpa using bf_smul_r (c := c) (J := J) 0 u 0

theorem mid_vv (a : Fin n → AE F E) (z : Fin d₁ → AE F E) : vecMulVec a (incM F H'.ι *ᵥ z) =
    incM F (1 : Matrix (Fin n) (Fin n) E) * vecMulVec a z * (incM F H'.ι)ᵀ := by
  rw [incM_one, Matrix.one_mul, vv_mul_r]

section Zero

variable {M₁ : Model σ X W₁} {e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁}

theorem constant_term_norm_eq_theta (hp : IsPair B M χX χW om r s r' s') (h' : PG σ W W₁ H' (-1)) (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀)
    (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e₀ (om (1, u) Φ) = e₀ Φ) (x : Fin n → E) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) (u : unip σ W H') : ∃ w, ‖tm B M om H' e₀ (vecMulVec x H'.y) Φ u‖ =
      ‖thetaSum F (M₁.co.rho B.ψ w (e₀ (M.co.rho B.ψ (incM F (vecMulVec x H'.y)) Φ)))‖ := by
  obtain ⟨a, z, e⟩ := unip_y h' (inv_mem u.2)
  have h := hp.base.std
  refine ⟨vecMulVec (incV F x) z, ?_⟩
  rw [tm_eq hp hi _ hΦ, incM_vv, vv_mul_r, e, Matrix.vecMulVec_add, Matrix.vecMulVec_add, add_assoc,
    ev_I h he ⟨a • incV F x, by rw [Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]⟩ _ hΦ, mid_vv, ev_mid h he _ _ hΦ,
    theta_smul, theta_smul, norm_mul, norm_mul, std_norm h, std_norm h, one_mul, one_mul]

theorem constant_term_rational_unipotent_invariant (hp : IsPair B M χX χW om r s r' s') (h' : PG σ W W₁ H' (-1)) (hM₁ : M₁.IsGood B.ψ)
    (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀)
    (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e₀ (om (1, u) Φ) = e₀ Φ) (x : Fin n → E) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) (γ : unip σ W H') (hγ : γ.1 ∈ ratU σ W.J) (u : unip σ W H') :
    tm B M om H' e₀ (vecMulVec x H'.y) Φ (γ * u) = tm B M om H' e₀ (vecMulVec x H'.y) Φ u := by
  obtain ⟨a, z, e⟩ := unip_y_rat h' (inv_mem γ.2) (inv_mem hγ)
  have h := hp.base.std
  have hΨ := om_mem hp (1, u.1) hΦ
  have e1 : vecMulVec (incV F x) (incV F (H'.ι *ᵥ z)) =
      incM F (1 : Matrix (Fin n) (Fin n) E) * incM F (vecMulVec x z) * (incM F H'.ι)ᵀ := by rw [← inc_mulVec, mid_vv, incM_vv]
  rw [tm_mul, tm_eq hp hi _ hΨ, incM_vv, vv_mul_r, e, Matrix.vecMulVec_add, Matrix.vecMulVec_add, add_assoc,
    ev_I h he ⟨inclR (F := F) (AF F) a • incV F x, by rw [incV_smul, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]⟩ _ hΨ,
    ← incM_vv, ← incM_vv, ← incM_vv, ← incM_add, psi_rat h, one_smul, incM_add, incM_vv x (H'.ι *ᵥ z), e1, ev_mid h he _ _ hΨ, ← e1,
    ← incM_vv, psi_rat h, one_smul, theta_rho_rat h hM₁]
  rfl

theorem constant_term_anisotropic_integral_zero (hm : MeanOK σ W H' μ 𝓕) (hp : IsPair B M χX χW om r s r' s') (h' : PG σ W W₁ H' (-1)) (hM₁ : M₁.IsGood B.ψ)
    (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀)
    (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e₀ (om (1, u) Φ) = e₀ Φ) {x : Fin n → E} (hx : form σ X.J x x ≠ 0) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : ∫ u in 𝓕, tm B M om H' e₀ (vecMulVec x H'.y) Φ u ∂μ = 0 := by
  have h := hp.base.std
  obtain ⟨a, ha⟩ := exists_psi h
  have hq : σ (form σ X.J x x) = form σ X.J x x := by
    rw [PositivityTheory.ThKG.Tow.Pln.form_swap hp.base.cm (ε := 1) (fun i j => by rw [hp.herm.herm, one_mul]), one_mul]
  set c : AE F E := algebraMap (AF F) (AE F E) a * inclR (F := F) (AF F) (form σ X.J x x)⁻¹ with hc
  obtain ⟨g, hg⟩ := exists_eich h' 0 c (by
    rw [hc, map_mul, AlgHom.commutes, cA_inc, map_inv₀ σ, hq, Matrix.mulVec_zero, bf0]
    push_cast
    ring)
  refine hm.zero (constant_term_rational_unipotent_invariant hp h' hM₁ he hi x hΦ) (g := g) ha fun u => ?_
  obtain ⟨b, z, e⟩ := unip_y h' (inv_mem u.2)
  have e2 : mat (u * g).1⁻¹ *ᵥ incV F H'.y = c • incV F H'.x + mat u.1⁻¹ *ᵥ incV F H'.y := by
    rw [Subgroup.coe_mul, mul_inv_rev, Fr.mat_mul, ← Matrix.mulVec_mulVec, hg, eich_apply, e]
    simp only [Matrix.mulVec_zero, bf_add_l, bf_smul_l, h'.ad.xx, h'.ad.ix, h'.ad.yx, mul_zero, zero_add, h'.ad.ee, one_smul, bf0,
      neg_zero, zero_smul, add_zero]
    exact add_comm _ _
  rw [tm_eq hp hi _ hΦ, tm_eq hp hi _ hΦ, incM_vv, vv_mul_r, vv_mul_r, e2, Matrix.vecMulVec_add,
    ev_I h he ⟨c • incV F x, by rw [Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]⟩ _ hΦ, theta_smul, half_sy hp.base (a := a)]
  rw [hT_vv, e, bf_inc]
  simp only [bf_add_r, bf_smul_l, bf_smul_r, h'.ad.xx, h'.ad.xi, h'.ad.xy, mul_zero, zero_add, mul_one]
  rw [hc, mul_left_comm, ← map_mul, mul_inv_cancel₀ hx, map_one, mul_one]

end Zero

section Cone

variable {M₂ : Model σ X₁ W₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}

theorem tA_eig (hp : IsPair B M χX χW om r s r' s') (h' : PG σ W W₁ H' (-1)) (he : IsEv B M M₂ H.ι H'.ι (sumA H H') e)
    (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, u) Φ) = e Φ) (w : Fin d₁ → E) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) (u : unip σ W H') : tm B M om H' e (vA H.y H'.y H'.ι (H.x, w)) Φ u =
      B.ψ (-(⅟(2 : AF F) * sy σ X W (incM F (vA H.y H'.y H'.ι (H.x, w)) * (mat u.1⁻¹)ᵀ - incM F (vA H.y H'.y H'.ι (H.x, w)))
        (incM F (vA H.y H'.y H'.ι (H.x, w))))) * tm B M om H' e (vA H.y H'.y H'.ι (H.x, w)) Φ 1 := by
  obtain ⟨a, z, e1⟩ := unip_y h' (inv_mem u.2)
  obtain ⟨b, e2⟩ := (Fr.mem_unip.1 (inv_mem u.2)).2 (incV F w)
  rw [tm_eq hp hi _ hΦ, tm_one, ← theta_smul, ← ev_I hp.base.std he ?_ _ hΦ, sub_add_cancel]
  refine ⟨a • incV F H.x + b • incV F H.y, z, ?_⟩
  rw [vA_apply, incM_add, incM_vv, incM_vv, Matrix.add_mul, vv_mul_r, vv_mul_r, ← inc_mulVec, e1, e2]
  simp only [Matrix.vecMulVec_add, Matrix.add_vecMulVec, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]
  abel

theorem tA_zero (hm : MeanOK σ W H' μ 𝓕) (hp : IsPair B M χX χW om r s r' s') (h : PG σ X X₁ H 1) (h' : PG σ W W₁ H' (-1))
    (he : IsEv B M M₂ H.ι H'.ι (sumA H H') e)
    (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, u) Φ) = e Φ) {w : Fin d₁ → E} (hw : w ≠ 0) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : ∫ u in 𝓕, tm B M om H' e (vA H.y H'.y H'.ι (H.x, w)) Φ u ∂μ = 0 := by
  have hψ := hp.base.std
  obtain ⟨a, ha⟩ := exists_psi hψ
  obtain ⟨z₀, hz₀⟩ : ∃ z, bf σ.toRingHom W.J (H'.ι *ᵥ z) (H'.ι *ᵥ w) ≠ 0 := by
    by_contra h0
    push Not at h0
    exact hw (h'.nd_low w h0)
  set i2 : AE F E := algebraMap (AF F) (AE F E) (⅟2) with hi2
  have h2 : i2 * 2 = 1 := by rw [hi2, ← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one]
  have hc2 : cA σ i2 = i2 := AlgHom.commutes _ _
  set z : Fin d₁ → AE F E := (i2 * algebraMap (AF F) (AE F E) a) • incV F ((bf σ.toRingHom W.J (H'.ι *ᵥ z₀) (H'.ι *ᵥ w))⁻¹ • z₀) with hz
  have hb : bf (cA σ).toRingHom (incM F W.J) (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ incV F w) = i2 * algebraMap (AF F) (AE F E) a := by
    rw [hz, Matrix.mulVec_smul, bf_smul_l, inc_mulVec, inc_mulVec, bf_inc, Matrix.mulVec_smul]
    rw [show form σ W.J _ _ = 1 from (bf_smul_l (c := σ.toRingHom) _ _ _).trans (inv_mul_cancel₀ hz₀), map_one, mul_one]
  have hb' : bf (cA σ).toRingHom (incM F W.J) (incM F H'.ι *ᵥ incV F w) (incM F H'.ι *ᵥ z) = -(i2 * algebraMap (AF F) (AE F E) a) := by
    rw [h'.ad.symm, hb, map_mul]
    change _ * (cA σ _ * cA σ _) = _
    rw [hc2, AlgHom.commutes]
    push_cast
    ring
  clear_value z
  obtain ⟨g, hg⟩ := exists_eich h' z (-(i2 * bf (cA σ).toRingHom (incM F W.J) (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ z))) (by
    have := h'.ad.symm (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ z)
    rw [map_neg, map_mul, hc2]
    change _ = _ * cA σ _ at this
    linear_combination i2 * this - bf (cA σ).toRingHom (incM F W.J) (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ z) * h2)
  have hgc : tm B M om H' e (vA H.y H'.y H'.ι (H.x, w)) Φ g = B.ψ a * tm B M om H' e (vA H.y H'.y H'.ι (H.x, w)) Φ 1 := by
    rw [tA_eig hp h' he hi w hΦ g, half_sy hp.base (a := a)]
    rw [vA_apply, incM_add, incM_vv, incM_vv, Matrix.add_mul, vv_mul_r, vv_mul_r, ← inc_mulVec, hg, eich_y h'.ad, eich_i h'.ad, hb',
      sub_eq_add_neg, ← neg_one_smul (AE F E) (vecMulVec _ _ + vecMulVec _ _)]
    simp only [hT_add_l, hT_add_r, hT_smul_l, hT_vv, bf_add_l, bf_smul_l, h.ad.xx, h.ad.xy, h.ad.yx, h.ad.yy, h'.ad.xi, h'.ad.yi,
      h'.ad.xy, h'.ad.yy, h'.ad.iy, hb]
    push_cast
    linear_combination algebraMap (AF F) (AE F E) a * h2
  refine hm.zero (fun γ hγ u => ?_) (g := g) ha fun u => ?_
  · obtain ⟨D, hD⟩ := Fr.mem_ratU.1 (inv_mem hγ)
    rw [tm_mul, tA_eig hp h' he hi w (om_mem hp _ hΦ), hD,
      show ∀ U : Matrix (Fin n) (Fin d) E, incM F U * (incM F D)ᵀ - incM F U = incM F (U * Dᵀ - U) from fun U => by
        simp only [incM, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.transpose_map],
      psi_rat hψ, one_mul, ← tm_mul, one_mul]
  · rw [tm_mul, tA_eig hp h' he hi w (om_mem hp _ hΦ), ← tm_mul, one_mul, hgc, tA_eig hp h' he hi w hΦ u]
    ring

end Cone

end PositivityTheory.ThKCT.Ker

end
