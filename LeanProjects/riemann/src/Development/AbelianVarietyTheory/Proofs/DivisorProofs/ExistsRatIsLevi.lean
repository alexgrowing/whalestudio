import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegralBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneRestrictedSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.CTLawRat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Form

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem form_add_left (u v w : Fin n → E) : form σ J (u + v) w = form σ J u w + form σ J v w := by
  simp only [form, add_dotProduct]

theorem form_smul_left (c : E) (v w : Fin n → E) : form σ J (c • v) w = c * form σ J v w := by
  simp only [form, smul_dotProduct, smul_eq_mul]

theorem form_add_right (v u w : Fin n → E) : form σ J v (u + w) = form σ J v u + form σ J v w := by
  simp only [form]
  have e : (fun i => σ ((u + w) i)) = (fun i => σ (u i)) + fun i => σ (w i) := by
    funext i; simp
  rw [e, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right (c : E) (v w : Fin n → E) : form σ J v (c • w) = σ c * form σ J v w := by
  simp only [form]
  have e : (fun i => σ ((c • w) i)) = σ c • fun i => σ (w i) := by
    funext i; simp
  rw [e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_swap (hσ : ∀ x, σ (σ x) = x) (hsk : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → E) :
    form σ J w v = -σ (form σ J v w) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hsk, Finset.mul_sum, mul_neg, neg_mul,
    Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_single (i j : Fin n) : form σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have e : (fun k => σ ((Pi.single j 1 : Fin n → E) k)) = Pi.single j 1 := by
    funext k; by_cases h : k = j
    · subst h; simp
    · simp [h]
  rw [form, e, Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply, Matrix.col]

def leviVec (x y : Fin n → E) (t : E) (v : Fin n → E) : Fin n → E :=
  v + ((t - 1) * form σ J v y) • x + (((σ t)⁻¹ - 1) * -form σ J v x) • y

def leviLin (x y : Fin n → E) (t : E) : (Fin n → E) →ₗ[E] (Fin n → E) where
  toFun := leviVec σ J x y t
  map_add' u v := by
    simp only [leviVec, form_add_left, mul_add, neg_add, add_smul]
    abel
  map_smul' c v := by
    simp only [leviVec, form_smul_left, smul_add, smul_smul, RingHom.id_apply]
    rw [mul_left_comm (t - 1) c, show ((σ t)⁻¹ - 1) * -(c * form σ J v x) = c * (((σ t)⁻¹ - 1) * -form σ J v x) by ring]

end Form

end GlobalTheory.CTLawRat

namespace GlobalTheory.CTLawRat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Levi

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E)

theorem leviVec_form (hσ : ∀ a, σ (σ a) = a) (hsk : ∀ i j, σ (J j i) = -J i j)
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1) {t : E} (ht : t ≠ 0)
    (v w : Fin n → E) : form σ J (leviVec σ J x y t v) (leviVec σ J x y t w) = form σ J v w := by
  have hyx : form σ J y x = -1 := by rw [form_swap σ J hσ hsk x y, hxy, map_one]
  have e1 := form_swap σ J hσ hsk w x
  have e2 := form_swap σ J hσ hsk w y
  simp only [leviVec, form_add_left, form_add_right, form_smul_left, form_smul_right, hxx, hyy, hxy, hyx, e1, e2]
  simp only [map_mul, map_sub, map_neg, map_one, map_inv₀, hσ]
  have h₁ : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  have h₂ : (σ t)⁻¹ * σ t = 1 := inv_mul_cancel₀ ((map_ne_zero σ).2 ht)
  linear_combination (-(form σ J v y) * σ (form σ J w x)) * h₁ + (form σ J v x * σ (form σ J w y)) * h₂

theorem leviVec_apply_x_eq_smul (hxx : form σ J x x = 0) (hxy : form σ J x y = 1) (t : E) :
    leviVec σ J x y t x = t • x := by
  simp only [leviVec, hxx, hxy, mul_one, neg_zero, mul_zero, zero_smul, add_zero, sub_smul, one_smul]
  abel

theorem leviVec_y (hσ : ∀ a, σ (σ a) = a) (hsk : ∀ i j, σ (J j i) = -J i j) (hyy : form σ J y y = 0)
    (hxy : form σ J x y = 1) (t : E) : leviVec σ J x y t y = (σ t)⁻¹ • y := by
  have hyx : form σ J y x = -1 := by rw [form_swap σ J hσ hsk x y, hxy, map_one]
  simp only [leviVec, hyy, hyx, mul_zero, zero_smul, add_zero, neg_neg, mul_one, sub_smul, one_smul]
  abel

theorem leviVec_orth (t : E) (v : Fin n → E) (hvx : form σ J v x = 0) (hvy : form σ J v y = 0) :
    leviVec σ J x y t v = v := by
  simp [leviVec, hvx, hvy]

theorem exists_rat_isLevi (hσ : ∀ a, σ (σ a) = a) {n₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁)
    (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hxx : form σ W.J H.x H.x = 0) (hyy : form σ W.J H.y H.y = 0)
    (hxy : form σ W.J H.x H.y = 1) (horth : ∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0)
    (hdet : W.J.det ≠ 0) (t : Eˣ) :
    ∃ m ∈ ratU σ W.J, IsLevi (W₁ := W₁) H (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) 1 m := by
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  set L := leviLin σ W.J H.x H.y t.1 with hL
  set Mm := LinearMap.toMatrix' L with hMm
  have hMv : ∀ v, Mm *ᵥ v = leviVec σ W.J H.x H.y t.1 v := fun v => by
    rw [hMm, LinearMap.toMatrix'_mulVec]; rfl
  have hcol : ∀ i, (fun k => Mm k i) = leviVec σ W.J H.x H.y t.1 (Pi.single i 1) := fun i => by
    rw [← hMv, Matrix.mulVec_single_one]; rfl
  have hu : Mmᵀ * W.J * Mm.map σ = W.J := by
    ext i j
    rw [GlobalTheory.LeviElem.form_gram, hcol, hcol, leviVec_form σ W.J H.x H.y hσ hsk hxx hyy hxy t.ne_zero, form_single]
  have hdetM : Mm.det ≠ 0 := by
    intro h0
    apply hdet
    have e := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at e
    exact e.symm
  let m₀ : GL (Fin n) E := Matrix.nonsingInvUnit Mm (isUnit_iff_ne_zero.2 hdetM)
  have hm₀ : (m₀ : Matrix (Fin n) (Fin n) E) = Mm := rfl
  have hu' : (m₀ : Matrix (Fin n) (Fin n) E)ᵀ * W.J * (m₀ : Matrix (Fin n) (Fin n) E).map σ = W.J := by rw [hm₀]; exact hu
  let h : UA σ W.J := ⟨Matrix.GeneralLinearGroup.map f m₀, GlobalTheory.LeviRatSkew.unitary_map' σ _ _ hu'⟩
  have hmat : mat h = Mm.map f := rfl
  have hmv : ∀ v : Fin n → E, mat h *ᵥ incV F v = incV F (Mm *ᵥ v) :=
    fun v => funext fun i => (RingHom.map_mulVec f _ _ i).symm
  have hcf : ∀ e, cA σ (f e) = f (σ e) := fun e => by simp [cA, hf, inclR]
  have hMι : Mm * H.ι = H.ι := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, hMv, leviVec_orth σ W.J H.x H.y _ _ (horth _).1 (horth _).2]
  refine ⟨h, Subgroup.mem_subgroupOf.2 ⟨m₀, rfl⟩, ?_, ?_, ?_⟩
  · rw [hmv, hMv, leviVec_apply_x_eq_smul σ W.J H.x H.y hxx hxy]
    ext i
    simp [incV, hf]
  · rw [hmv, hMv, leviVec_y σ W.J H.x H.y hσ hsk hyy hxy]
    ext i
    simp only [incV, Pi.smul_apply, smul_eq_mul, Units.coe_map_inv, MonoidHom.coe_coe, Units.val_inv_eq_inv_val]
    erw [hcf]
    rw [map_inv₀, ← map_mul]
  · rw [hmat, show mat (1 : UA σ W₁.J) = 1 from rfl, Matrix.mul_one, show incM F H.ι = H.ι.map f from rfl,
      ← Matrix.map_mul, hMι]

end Levi

end GlobalTheory.CTLawRat

namespace GlobalTheory.CTLawRat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem inv_mul_mul_mem_unip_of_stabilizes {d d₁ : ℕ} {W : Spc F E d} {H : Plane E d d₁} (s u : UA σ W.J) (t : (AE F E)ˣ)
    (hx : mat s *ᵥ incV F H.x = t.1 • incV F H.x)
    (hι : ∀ z, ∃ z', mat s *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z')
    (hu : u ∈ unip σ W H) : s⁻¹ * u * s ∈ unip σ W H := by
  rw [GlobalTheory.UnipCT.unip_eq] at hu ⊢
  obtain ⟨hu1, hu2⟩ := hu
  have hx' : mat s⁻¹ *ᵥ incV F H.x = (t⁻¹).1 • incV F H.x := by
    have := GlobalTheory.CTLevi.mat_inv_mulVec s ((t⁻¹).1 • incV F H.x)
    rw [Matrix.mulVec_smul, hx, smul_smul, Units.inv_mul, one_smul] at this
    exact this
  refine ⟨?_, fun z => ?_⟩
  · show mat (s⁻¹ * u * s) *ᵥ incV F H.x = incV F H.x
    rw [GlobalTheory.UnipCT.mat_mul', GlobalTheory.UnipCT.mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_smul, hu1, Matrix.mulVec_smul, hx', smul_smul, Units.mul_inv, one_smul]
  · obtain ⟨z', hz'⟩ := hι z
    obtain ⟨a, ha⟩ := hu2 z'
    refine ⟨a * (t⁻¹).1, ?_⟩
    show mat (s⁻¹ * u * s) *ᵥ (incM F H.ι *ᵥ z) = _
    rw [GlobalTheory.UnipCT.mat_mul', GlobalTheory.UnipCT.mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz', ha,
      Matrix.mulVec_add, Matrix.mulVec_smul, hx', ← hz', GlobalTheory.CTLevi.mat_inv_mulVec, smul_smul]

set_option synthInstance.maxHeartbeats 400000 in

theorem invariant_under_rational_levi_of_fundamentalDomain {n n₁ : ℕ} {Y : Spc F E n} (H : Plane E n n₁) (f c : UA σ Y.J → ℂ) : IsCT H f c →
    (∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x) →
    (∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1) →
    ∀ (t : (AE F E)ˣ) (r : UA σ Y.J), mat r *ᵥ incV F H.x = t.1 • incV F H.x →
      (∀ z, mat r *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) → r ∈ ratU σ Y.J → ∀ x, c (r * x) = c x := by
  intro hc hf ⟨μ, 𝓕, hμ, h𝓕, h1⟩ t r hx hι hr x
  obtain ⟨i1, -, -, -⟩ := GlobalTheory.UnipCT.topFacts (F := F) σ Y.J
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  have hx' : mat r⁻¹ *ᵥ incV F H.x = (t⁻¹).1 • incV F H.x := by
    have := GlobalTheory.CTLevi.mat_inv_mulVec r ((t⁻¹).1 • incV F H.x)
    rw [Matrix.mulVec_smul, hx, smul_smul, Units.inv_mul, one_smul] at this
    exact this
  have hι' : ∀ z, mat r⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := fun z => by
    have := GlobalTheory.CTLevi.mat_inv_mulVec r (incM F H.ι *ᵥ z)
    rwa [hι] at this
  have hA : ∀ u ∈ unip σ Y H, r⁻¹ * u * r ∈ unip σ Y H := fun u hu =>
    inv_mul_mul_mem_unip_of_stabilizes r u t hx (fun z => ⟨z, hι z⟩) hu
  have hB : ∀ u ∈ unip σ Y H, r * u * r⁻¹ ∈ unip σ Y H := fun u hu => by
    simpa using inv_mul_mul_mem_unip_of_stabilizes r⁻¹ u t⁻¹ hx' (fun z => ⟨z, hι' z⟩) hu
  let φ : unip σ Y H ≃* unip σ Y H :=
    { toFun := fun u => ⟨r⁻¹ * u.1 * r, hA u.1 u.2⟩
      invFun := fun u => ⟨r * u.1 * r⁻¹, hB u.1 u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by
        show r⁻¹ * (u * v).1 * r = (r⁻¹ * u.1 * r) * (r⁻¹ * v.1 * r)
        rw [Subgroup.coe_mul]; group) }
  have hφ : Continuous φ := by
    show Continuous fun u : unip σ Y H => (⟨r⁻¹ * u.1 * r, hA u.1 u.2⟩ : unip σ Y H)
    exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hφs : Continuous φ.symm := by
    show Continuous fun u : unip σ Y H => (⟨r * u.1 * r⁻¹, hB u.1 u.2⟩ : unip σ Y H)
    exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  let e : unip σ Y H ≃ᵐ unip σ Y H := (Homeomorph.mk φ.toEquiv hφ hφs).toMeasurableEquiv
  let μ' : Measure (unip σ Y H) := μ.map e
  haveI : μ'.IsHaarMeasure := φ.isHaarMeasure_map μ hφ hφs
  have hpres : MeasurePreserving e.symm μ' μ := by
    refine ⟨e.symm.measurable, ?_⟩
    simp only [μ', Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self, Measure.map_id]
  have hmemΓ : ∀ g : unip σ Y H, g ∈ (ratU σ Y.J).subgroupOf (unip σ Y H) ↔ g.1 ∈ ratU σ Y.J :=
    fun g => Subgroup.mem_subgroupOf
  let eg : (ratU σ Y.J).subgroupOf (unip σ Y H) → (ratU σ Y.J).subgroupOf (unip σ Y H) := fun g =>
    ⟨φ g.1, (hmemΓ _).2 (by
      show r⁻¹ * g.1.1 * r ∈ _
      exact mul_mem (mul_mem (inv_mem hr) ((hmemΓ _).1 g.2)) hr)⟩
  have heg : Function.Bijective eg := by
    refine ⟨fun a b h => Subtype.ext (φ.injective (congrArg Subtype.val h)),
      fun y => ⟨⟨φ.symm y.1, (hmemΓ _).2 ?_⟩, Subtype.ext (φ.apply_symm_apply _)⟩⟩
    show r * y.1.1 * r⁻¹ ∈ _
    exact mul_mem (mul_mem hr ((hmemΓ _).1 y.2)) (inv_mem hr)
  let 𝓕' : Set (unip σ Y H) := e.symm ⁻¹' 𝓕
  have h𝓕' : IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕' μ' := by
    refine h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving heg ?_
    intro g y
    show φ.symm (φ g.1 * y) = g.1 * φ.symm y
    rw [map_mul, MulEquiv.symm_apply_apply]
  have h1' : μ' 𝓕' = 1 := by
    simp only [μ', 𝓕', e.map_apply]
    rw [← Set.preimage_comp, e.symm_comp_self, Set.preimage_id]; exact h1
  have A := hc μ' 𝓕' inferInstance h𝓕' h1' x
  have B := hc μ 𝓕 hμ h𝓕 h1 (r * x)
  rw [B, A, e.measurableEmbedding.setIntegral_map]
  have h𝓕e : e ⁻¹' 𝓕' = 𝓕 := by
    simp only [𝓕']; rw [← Set.preimage_comp, e.symm_comp_self, Set.preimage_id]
  rw [h𝓕e]
  congr 1; funext u
  show f (u.1 * (r * x)) = f ((r⁻¹ * u.1 * r) * x)
  rw [← hf r⁻¹ (inv_mem hr) (u.1 * (r * x))]
  simp only [mul_assoc]

theorem law_trivial_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      (∃ (μ : Measure (unip σ W H)) (𝓕 : Set (unip σ W H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H)) 𝓕 μ ∧ μ 𝓕 = 1) →
      ∀ (χa : Chr F E) (za : ℝ) (f fa : UA σ W.J → ℂ), Continuous f → (∀ γ ∈ ratU σ W.J, ∀ x, f (γ * x) = f x) →
      IsCT H f fa → HasLaw W₁ H χa za fa → (∃ x, fa x ≠ 0) →
      ∀ t : Eˣ, χa (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) = 1 := by
  intro F E _ _ _ _ _ σ _ hσ n n₁ W W₁ H hsk _ hxx hyy hxy horth _ c₀ hc₀ _ hJ hdom χa za f fa _ hf hct hlaw hne t
  obtain ⟨x₀, hx₀⟩ := hne
  have hdet : W.J.det ≠ 0 := by
    intro h0
    apply hJ.2
    rw [Matrix.det_smul]
    have : (W.J.map σ).det = σ W.J.det := by
      rw [AlgHom.map_det]; rfl
    rw [this, h0, map_zero, mul_zero]
  obtain ⟨m, hm, hL⟩ := exists_rat_isLevi σ hσ W W₁ H hsk hxx hyy hxy horth hdet t
  have hι : ∀ z, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := fun z => by
    rw [Matrix.mulVec_mulVec, hL.2.2, show mat (1 : UA σ W₁.J) = 1 from rfl, Matrix.mul_one]
  have hinv := invariant_under_rational_levi_of_fundamentalDomain H f fa hct hf hdom _ m hL.1 hι hm x₀
  have hlx := hlaw _ m hL x₀
  rw [hinv, GlobalTheory.Doubling.absE_inclR] at hlx
  simp only [NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one] at hlx
  have hc : ((χa (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) : ℂ)) = 1 := by
    have := mul_right_cancel₀ hx₀ (hlx.symm.trans (one_mul (fa x₀)).symm)
    exact this
  exact Circle.ext (by rw [hc, Circle.coe_one])

end GlobalTheory.CTLawRat
