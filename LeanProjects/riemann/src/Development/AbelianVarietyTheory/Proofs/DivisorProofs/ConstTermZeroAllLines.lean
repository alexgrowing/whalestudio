import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleIsotropicTowerStepTen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormYXNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.ThKLiftCusp GlobalTheory.ThKOrthVInt

noncomputable section

namespace GlobalTheory.LineCuspAll

open GlobalTheory.ThKLineCusp

theorem transfer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃* G) (he : Continuous e) (hes : Continuous e.symm) (N N' Γ : Subgroup G) (hN : ∀ g, g ∈ N ↔ e g ∈ N')
    (hΓ : ∀ g, g ∈ Γ ↔ e g ∈ Γ) (φ : G → ℂ)
    (hφ : ∀ (μ' : Measure N') (𝓕' : Set N'), μ'.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N') 𝓕' μ' →
      μ' 𝓕' = 1 → ∫ u in 𝓕', φ u ∂μ' = 0)
    (μ : Measure N) (𝓕 : Set N) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) (h1 : μ 𝓕 = 1) :
    ∫ u in 𝓕, φ (e u) ∂μ = 0 := by
  let e' : N ≃* N' :=
    { toFun := fun x => ⟨e x, (hN x).1 x.2⟩
      invFun := fun y => ⟨e.symm y, (hN _).2 (by simpa using y.2)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_mul' := fun u v => Subtype.ext (map_mul e u.1 v.1) }
  have he' : Continuous e' := (he.comp continuous_subtype_val).subtype_mk _
  have hes' : Continuous e'.symm := (hes.comp continuous_subtype_val).subtype_mk _
  let t : N ≃ₜ N' := ⟨e'.toEquiv, he', hes'⟩
  let eM : N ≃ᵐ N' := t.toMeasurableEquiv
  have hH : (μ.map eM).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e' he' hes'
  let eΓ : Γ.subgroupOf N' → Γ.subgroupOf N := fun γ =>
    ⟨e'.symm γ, Subgroup.mem_subgroupOf.2 ((hΓ _).2 (by
      show e (e.symm γ.1.1) ∈ Γ
      rw [e.apply_symm_apply]
      exact Subgroup.mem_subgroupOf.1 γ.2))⟩
  let eΓi : Γ.subgroupOf N → Γ.subgroupOf N' := fun γ =>
    ⟨e' γ, Subgroup.mem_subgroupOf.2 ((hΓ _).1 (Subgroup.mem_subgroupOf.1 γ.2))⟩
  have hbij : Function.Bijective eΓi :=
    Function.bijective_iff_has_inverse.2 ⟨eΓ, fun γ => Subtype.ext (e'.symm_apply_apply γ.1),
      fun γ => Subtype.ext (e'.apply_symm_apply γ.1)⟩
  have hq : Measure.QuasiMeasurePreserving eM.symm (μ.map eM) μ :=
    ⟨eM.symm.measurable, by rw [MeasurableEquiv.map_symm_map]⟩
  have h𝓕' : IsFundamentalDomain (Γ.subgroupOf N') (eM.symm ⁻¹' 𝓕) (μ.map eM) :=
    h𝓕.preimage_of_equiv hq hbij fun γ y => by
      show e'.symm (e' γ.1 * y) = γ.1 * e'.symm y
      rw [map_mul, e'.symm_apply_apply]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓕) = 𝓕 := by
    ext x; simp
  have hmass : (μ.map eM) (eM.symm ⁻¹' 𝓕) = 1 := by rw [eM.map_apply, hpre, h1]
  have key := hφ (μ.map eM) (eM.symm ⁻¹' 𝓕) hH h𝓕' hmass
  rw [setIntegral_map_equiv, hpre] at key
  exact key

section Witt

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem form_add_left (v v' w : Fin n → E) : form σ J (v + v') w = form σ J v w + form σ J v' w := by
  simp [form, add_dotProduct]

theorem form_smul_left (a : E) (v w : Fin n → E) : form σ J (a • v) w = a * form σ J v w := by
  simp [form, smul_dotProduct]

theorem form_add_right (v w w' : Fin n → E) : form σ J v (w + w') = form σ J v w + form σ J v w' := by
  simp [form, dotProduct, Matrix.mulVec, mul_add, Finset.sum_add_distrib]

theorem form_smul_right (a : E) (v w : Fin n → E) : form σ J v (a • w) = σ a * form σ J v w := by
  simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem exists_isom_of_ne (hσ : ∀ x, σ (σ x) = x) (hsk : ∀ i j, σ (J j i) = -J i j) {x y : Fin n → E}
    (hx : form σ J x x = 0) (hy : form σ J y y = 0) (hxy : form σ J x y ≠ 0) :
    ∃ T : Matrix (Fin n) (Fin n) E, (∀ z w, form σ J (T *ᵥ z) (T *ᵥ w) = form σ J z w) ∧ T *ᵥ x = y := by
  have sk := GlobalTheory.LeviPlaneSection.form_skew hσ hsk
  set β := form σ J x y with hβ
  set u : Fin n → E := y + (-1 : E) • x with hu
  have hT : ∀ z, (1 + β⁻¹ • Matrix.vecMulVec u (J *ᵥ fun i => σ (u i))) *ᵥ z = z + (β⁻¹ * form σ J z u) • u := by
    intro z
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, dotProduct_comm]
    funext i
    simp [form, mul_comm, mul_left_comm, mul_assoc]
  have hσβ : σ β ≠ 0 := by simpa using hxy
  have huu : form σ J u u = σ β - β := by
    rw [hu, form_add_left, form_add_right, form_add_right, form_smul_left, form_smul_left, form_smul_right,
      form_smul_right, hx, hy, sk y x, ← hβ]
    simp only [map_neg, map_one]
    ring
  refine ⟨1 + β⁻¹ • Matrix.vecMulVec u (J *ᵥ fun i => σ (u i)), fun z w => ?_, ?_⟩
  · clear_value u
    rw [hT, hT, form_add_left, form_add_right, form_add_right, form_smul_left, form_smul_left, form_smul_right,
      form_smul_right, huu, sk u w, map_mul, map_inv₀]
    field_simp
    ring
  · have hxu : form σ J x u = β := by
      rw [hu, form_add_right, form_smul_right, hx, mul_zero, add_zero]
    rw [hT, hxu, inv_mul_cancel₀ hxy, one_smul, hu]
    simp

theorem exists_isom [CharZero E] (hσ : ∀ x, σ (σ x) = x) (hsk : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0)
    {x y : Fin n → E} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : form σ J x x = 0) (hy : form σ J y y = 0) :
    ∃ T : Matrix (Fin n) (Fin n) E, (∀ z w, form σ J (T *ᵥ z) (T *ᵥ w) = form σ J z w) ∧ T *ᵥ x = y := by
  have sk := GlobalTheory.LeviPlaneSection.form_skew hσ hsk
  by_cases hxy : form σ J x y = 0
  swap
  · exact exists_isom_of_ne hσ hsk hx hy hxy
  have nd : ∀ v : Fin n → E, v ≠ 0 → ∃ z, form σ J z v ≠ 0 := by
    intro v hv
    by_contra h
    push Not at h
    refine hd (Matrix.exists_mulVec_eq_zero_iff.1 ⟨fun i => σ (v i), fun h0 => hv (funext fun i => ?_), funext fun i => ?_⟩)
    · simpa using congrFun h0 i
    · simpa [form] using h (Pi.single i 1)
  obtain ⟨z, hzx, hzy⟩ : ∃ z, form σ J z x ≠ 0 ∧ form σ J z y ≠ 0 := by
    obtain ⟨a, ha⟩ := nd x hx0
    obtain ⟨b, hb⟩ := nd y hy0
    by_cases h1 : form σ J a y = 0
    · by_cases h2 : form σ J b x = 0
      · exact ⟨a + b, by rwa [form_add_left, h2, add_zero], by rwa [form_add_left, h1, zero_add]⟩
      · exact ⟨b, h2, hb⟩
    · exact ⟨a, ha, h1⟩
  have hβ : form σ J x z ≠ 0 := by rw [sk x z]; simpa using hzx
  have hσβ : σ (form σ J x z) ≠ 0 := by simpa using hβ
  have hq : σ (form σ J z z) = -form σ J z z := by
    have := sk z z
    linear_combination this
  set v := z + (-form σ J z z / 2 / form σ J x z) • x with hv
  have hvv : form σ J v v = 0 := by
    rw [hv, form_add_left, form_add_right, form_add_right, form_smul_left, form_smul_left, form_smul_right,
      form_smul_right, hx, sk z x, map_div₀, map_div₀, map_neg, hq, map_ofNat]
    field_simp
    ring
  obtain ⟨T₁, h₁, e₁⟩ := exists_isom_of_ne hσ hsk hx hvv (by
    rwa [hv, form_add_right, form_smul_right, hx, mul_zero, add_zero])
  obtain ⟨T₂, h₂, e₂⟩ := exists_isom_of_ne hσ hsk hvv hy (by
    rwa [hv, form_add_left, form_smul_left, hxy, mul_zero, add_zero])
  refine ⟨T₂ * T₁, fun a b => ?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h₂, h₁]
  · rw [← Matrix.mulVec_mulVec, e₁, e₂]

theorem gram_of_isom {T : Matrix (Fin n) (Fin n) E} (hT : ∀ z w, form σ J (T *ᵥ z) (T *ᵥ w) = form σ J z w) :
    Tᵀ * J * T.map σ = J := by
  ext i j
  have h := hT (Pi.single i 1) (Pi.single j 1)
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  rw [Matrix.mul_assoc]
  simpa [form, dotProduct, Matrix.mulVec, Matrix.mul_apply, Pi.single_apply, apply_ite] using h

end Witt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_ratU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0) {T : Matrix (Fin n) (Fin n) E}
    (hT : Tᵀ * J * T.map σ = J) : ∃ γ ∈ ratU σ J, mat γ = incM F T := by
  have hdT : T.det ≠ 0 := fun h0 => hd (by rw [← hT, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0]; simp)
  let g : GL (Fin n) E := Matrix.GeneralLinearGroup.mkOfDetNeZero T hdT
  refine ⟨⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) g, ?_⟩, Subgroup.mem_subgroupOf.2 ⟨g, rfl⟩, rfl⟩
  show (incM F T)ᵀ * incM F J * (incM F T).map (cA σ) = incM F J
  have e : (incM F T).map (cA σ) = incM F (T.map σ) := by
    ext i j; simp [incM, GlobalTheory.ThKLineCusp.cA_inclR]
  rw [e]
  conv_rhs => rw [← hT]
  simp only [incM, Matrix.map_mul, Matrix.transpose_map]

theorem mat_inv_mulVec {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (γ : UA σ J) (z : Fin n → AE F E) :
    mat γ⁻¹ *ᵥ (mat γ *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← GlobalTheory.UnipCT.mat_mul', inv_mul_cancel]
  exact Matrix.one_mulVec z

theorem conj_mem {n : ℕ} (W : Spc F E n) (γ : UA σ W.J) {x y : Fin n → E} (hγ : mat γ *ᵥ incV F x = incV F y)
    {u : UA σ W.J} (hu : u ∈ unipSp σ W (Matrix.of fun i (_ : Fin 1) => x i)) :
    γ * u * γ⁻¹ ∈ unipSp σ W (Matrix.of fun i (_ : Fin 1) => y i) := by
  have hle : (unipSp σ W (Matrix.of fun i (_ : Fin 1) => x i)).map (MulAut.conj γ).toMonoidHom ≤
      unipSp σ W (Matrix.of fun i (_ : Fin 1) => y i) := by
    unfold unipSp
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨u, hu, rfl⟩
    simp only [Set.mem_ofPred_eq, mat_mul_col_iff, incM_col_mulVec] at hu ⊢
    obtain ⟨h1, h2, h3⟩ := hu
    have hm : ∀ z, mat ((MulAut.conj γ).toMonoidHom u) *ᵥ z = mat γ *ᵥ (mat u *ᵥ (mat γ⁻¹ *ᵥ z)) := fun z => by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← GlobalTheory.UnipCT.mat_mul', ← GlobalTheory.UnipCT.mat_mul']
      rfl
    have hi : ∀ z, mat γ *ᵥ (mat γ⁻¹ *ᵥ z) = z := fun z => by simpa using mat_inv_mulVec γ⁻¹ z
    have hf : ∀ z, formA σ W.J (mat γ *ᵥ z) (incV F y) = formA σ W.J z (incV F x) := fun z => by
      rw [← hγ, formA_mat]
    refine ⟨?_, fun z hz => ?_, fun z k => ?_⟩
    · rw [hm, ← hγ, mat_inv_mulVec, h1]
    · obtain ⟨a, ha⟩ := h2 (mat γ⁻¹ *ᵥ z) fun k => by
        have := hz k
        change formA σ W.J _ (incV F y) = 0 at this
        change formA σ W.J _ (incV F x) = 0
        rw [← hf, hi, this]
      exact ⟨a, by rw [hm, ha, Matrix.mulVec_add, hi, Matrix.mulVec_smul, hγ]⟩
    · have := h3 (mat γ⁻¹ *ᵥ z) k
      change formA σ W.J _ (incV F x) = 0 at this
      change formA σ W.J _ (incV F y) = 0
      rw [← hf, Matrix.mulVec_sub, hi] at this
      rw [hm, this]
  exact hle ⟨u, hu, rfl⟩

theorem unip_eq_unipSp (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}
    (hH : GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0) :
    unip σ W H = unipSp σ W (Matrix.of fun i (_ : Fin 1) => H.x i) := by
  have hiota : ∀ w, formA σ W.J (incM F H.ι *ᵥ w) (incV F H.x) = 0 := by
    intro w
    have hk : ∀ k, formA σ W.J (incV F (H.ι *ᵥ Pi.single k 1)) (incV F H.x) = 0 := by
      intro k; rw [formA_incV, (hH.2.2.2.2.1 _).1, map_zero]
    set q := incM F W.J *ᵥ fun i => cA σ (incV F H.x i) with hq
    have h0 : q ᵥ* incM F H.ι = 0 := by
      funext k
      have := hk k
      simp only [formA, Matrix.mulVec_single_one, GlobalTheory.ThKLineCusp.incV_mulVec] at this
      rw [← hq] at this
      simpa [Matrix.vecMul, dotProduct, incM, incV, Matrix.mulVec, Pi.single_apply, mul_comm] using this
    show (incM F H.ι *ᵥ w) ⬝ᵥ q = 0
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, h0, zero_dotProduct]
  unfold unip unipSp
  congr 1
  ext u
  simp only [Set.mem_ofPred_eq, mat_mul_col_iff, incM_col_mulVec]
  constructor
  · rintro ⟨hx, hι⟩
    refine ⟨hx, ?_, ?_⟩
    · intro z hz
      obtain ⟨a, b, w, rfl⟩ := hH.decompA hσ hsk hd z
      have h0 := hz 0
      change formA σ W.J _ (incV F H.x) = 0 at h0
      rw [formA_add_left, formA_add_left, formA_smul_left, formA_smul_left, hiota, formA_incV,
        formA_incV, hH.2.1, map_zero, GlobalTheory.LeviPlaneSection.form_skew hσ hsk H.y H.x, hH.2.2.2.1] at h0
      have hb : b = 0 := by simpa using h0
      subst hb
      obtain ⟨c, hc⟩ := hι w
      refine ⟨fun _ => c, ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hc]
      simp only [zero_smul, add_zero]
      abel
    · intro z k
      change formA σ W.J (mat u *ᵥ z - z) (incV F H.x) = 0
      rw [formA_sub_left]
      nth_rewrite 1 [← hx]
      rw [formA_mat, sub_self]
  · rintro ⟨hx, h2, -⟩
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := h2 (incM F H.ι *ᵥ z) (fun k => hiota z)
    exact ⟨a 0, ha⟩

theorem constTerm_zero_all_lines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
  IsCMExt F E σ → ∀ (m m₁ : ℕ) (W : Spc F E m) (W₁ : Spc F E m₁) (P : Plane E m m₁), IsIsoPlane σ B P W W₁ →
  (∀ k l, σ (W.J l k) = -W.J k l) → ∀ f : UA σ W.J → ℂ, (∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h) → IsCT (W := W) P f 0 →
  ∀ x : Fin m → E, x ≠ 0 → form σ W.J x x = 0 →
    ∀ (ν : Measure (unipSp σ W (Matrix.of fun k (_ : Fin 1) => x k))) (𝓖 : Set (unipSp σ W (Matrix.of fun k (_ : Fin 1) => x k))),
      ν.IsHaarMeasure → IsFundamentalDomain ((ratU σ W.J).subgroupOf (unipSp σ W (Matrix.of fun k (_ : Fin 1) => x k))) 𝓖 ν →
      ν 𝓖 = 1 → ∀ h, ∫ u in 𝓖, f (u.1 * h) ∂ν = 0 := by
  intro F E _ _ _ _ _ σ B hcm m m₁ W W₁ P hP hsk f hf hct x hx0 hx ν 𝓖 hν h𝓖 h1 h
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hd : W.J.det ≠ 0 := Nondeg.det_ne_zero_of_cartan B W hP.2.2.2.2.2.2.1
  have hd₁ : W₁.J.det ≠ 0 := Nondeg.det_ne_zero_of_cartan B W₁ hP.2.2.2.2.2.2.2.cartan
  have hP0 : P.x ≠ 0 := fun h0 => by
    have := hP.2.2.2.1
    rw [h0] at this
    simp [form] at this
  obtain ⟨T, hT, hTx⟩ := exists_isom hσ hsk hd hx0 hP0 hx hP.2.1
  obtain ⟨γ, hγ, hm⟩ := exists_ratU hd (gram_of_isom hT)
  have hγx : mat γ *ᵥ incV F x = incV F P.x := by rw [hm, ← GlobalTheory.ThKLineCusp.incV_mulVec, hTx]
  have hγx' : mat γ⁻¹ *ᵥ incV F P.x = incV F x := by rw [← hγx, mat_inv_mulVec]
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI := (GlobalTheory.UnipCT.topFacts (F := F) σ W.J).1
  have key := transfer (MulAut.conj γ)
    ((continuous_const.mul continuous_id).mul continuous_const : Continuous fun u : UA σ W.J => γ * u * γ⁻¹)
    ((continuous_const.mul continuous_id).mul continuous_const : Continuous fun u : UA σ W.J => γ⁻¹ * u * γ)
    (unipSp σ W (Matrix.of fun k (_ : Fin 1) => x k)) (unip σ W P) (ratU σ W.J)
    (fun g => by
      rw [unip_eq_unipSp hσ (GLTwo.IsIsoPlane.isHypPlane hP) hsk hd₁]
      refine ⟨fun hg => conj_mem W γ hγx hg, fun hg => ?_⟩
      simpa [mul_assoc] using conj_mem W γ⁻¹ hγx' hg)
    (fun g => ⟨fun hg => mul_mem (mul_mem hγ hg) (inv_mem hγ), fun hg => by
      simpa [mul_assoc] using mul_mem (mul_mem (inv_mem hγ) hg) hγ⟩)
    (fun u => f (u * (γ * h))) (fun μ 𝓕 a b c => (hct μ 𝓕 a b c (γ * h)).symm) ν 𝓖 hν h𝓖 h1
  rw [← key]
  refine integral_congr_ae (.of_forall fun u => ?_)
  show f (u.1 * h) = f (γ * u.1 * γ⁻¹ * (γ * h))
  rw [← hf γ hγ (u.1 * h)]
  simp [mul_assoc]

end GlobalTheory.LineCuspAll
