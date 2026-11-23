import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMemIffUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSqFundamentalDomain
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.IsoLineCT

open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.LeviPlane Formalism.UG GlobalTheory.UnipMem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem fm_swap {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {c : E}
    (hJ : ∀ i j, σ ((c • J.map σ) j i) = (c • J.map σ) i j) (p q : Fin n → E) :
    σ c * fm (σ : E →+* E) J p q = c * σ (fm (σ : E →+* E) J q p) := by
  have hJ' : ∀ i j, σ c * J j i = c * σ (J i j) := fun i j => by
    have := hJ i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ] at this
    exact this
  simp only [fm, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, AlgHom.coe_toRingHom]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hJ' i j
  linear_combination (p j * σ (q i)) * this

end GlobalTheory.IsoLineCT

namespace GlobalTheory.IsoLineCT

open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.LeviPlane Formalism.UG GlobalTheory.UnipMem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem fm_mulVec_mulVec {R : Type} [CommRing R] (c : R →+* R) {n m : ℕ} (J : Matrix (Fin n) (Fin n) R)
    (ι : Matrix (Fin n) (Fin m) R) (w u : Fin m → R) :
    fm c J (ι *ᵥ w) (ι *ᵥ u) = fm c (ιᵀ * J * ι.map c) w u := by
  simp only [fm]
  rw [show (fun i => c ((ι *ᵥ u) i)) = ι.map c *ᵥ fun i => c (u i) from funext fun i => RingHom.map_mulVec c ι u i,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w ιᵀ, Matrix.vecMul_transpose]

theorem fm_zero_right' {R : Type} [CommRing R] (c : R →+* R) {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (u : Fin n → R) :
    fm c J u 0 = 0 := by
  have : (fun i => c ((0 : Fin n → R) i)) = 0 := funext fun i => by simp
  simp only [fm, this, Matrix.mulVec_zero, dotProduct_zero]

theorem det_ne_zero_cartan (B : Base F E) {n : ℕ} (Y : Spc F E n)
    (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) : Y.J.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (B.emb w).1
  let M : Matrix (Fin n) (Fin n) ℂ := Complex.I • Y.J.map τ
  let v' : Fin n → ℂ := fun i => τ (v i)
  have hv' : v' ≠ 0 := fun h => hv (funext fun i => τ.injective (by simpa [v'] using congrFun h i))
  have hMv : M *ᵥ v' = 0 := by
    ext i
    have := congrArg τ (congrFun hJv i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this
    simp only [M, v', Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Matrix.smul_apply, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  have hx : star v' ≠ 0 := fun h => hv' (by simpa using congrArg star h)
  have := (h w).2.2 (star v') hx
  rw [star_star] at this
  change 0 < (_ ⬝ᵥ M *ᵥ v').re at this
  rw [hMv, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem split_of_iso {σ : E →ₐ[F] E} {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (hP : IsIsoPlane σ B H Y Y₁) (v : Fin n → E) :
    ∃ (a t : E) (u : Fin n₁ → E), v = a • H.x + H.ι *ᵥ u + t • H.y := by
  obtain ⟨hn, hxx, hyy, hxy, horth, hgram, -, hcart⟩ := hP
  have hdet : Y₁.J.det ≠ 0 := det_ne_zero_cartan B Y₁ hcart
  have hgram' : H.ιᵀ * Y.J * H.ι.map (σ : E →+* E) = Y₁.J := hgram
  have hyy' : fm (σ : E →+* E) Y.J H.y H.y = 0 := hyy
  have hxy' : fm (σ : E →+* E) Y.J H.x H.y = 1 := hxy
  have horth' : ∀ u, fm (σ : E →+* E) Y.J (H.ι *ᵥ u) H.x = 0 ∧ fm (σ : E →+* E) Y.J (H.ι *ᵥ u) H.y = 0 := horth
  let L : ((E × E) × (Fin n₁ → E)) →ₗ[E] (Fin n → E) :=
    ((LinearMap.fst E E E).smulRight H.x + (LinearMap.snd E E E).smulRight H.y).comp (LinearMap.fst E _ _) +
      (Matrix.mulVecLin H.ι).comp (LinearMap.snd E _ _)
  have hL : ∀ p, L p = p.1.1 • H.x + p.1.2 • H.y + H.ι *ᵥ p.2 := fun p => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨a, t⟩, u⟩ h0
    rw [hL] at h0
    simp only at h0
    have ha : a = 0 := by
      have := congrArg (fun z => fm (σ : E →+* E) Y.J z H.y) h0
      simp only [fm_add_left, fm_smul_left, hxy', hyy', (horth' u).2] at this
      simpa [fm] using this
    subst ha
    have hu : u = 0 := by
      have hj : ∀ j, (Y₁.J *ᵥ fun k => σ (u k)) j = 0 := fun j => by
        have := congrArg (fun z => fm (σ : E →+* E) Y.J (H.ι *ᵥ Pi.single j 1) z) h0
        simp only [zero_smul, zero_add, fm_add_right, fm_smul_right, (horth' _).2, mul_zero, fm_mulVec_mulVec] at this
        rw [hgram', fm_zero_right'] at this
        simpa [fm] using this
      have h2 : (fun k => σ (u k)) = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet (funext hj)
      funext k
      exact (RingHom.injective (σ : E →+* E)) (by simpa using congrFun h2 k)
    subst hu
    have hy : H.y ≠ 0 := fun h => by rw [h, fm_zero_right'] at hxy'; exact zero_ne_one hxy'
    have ht : t = 0 := by
      simp only [zero_smul, zero_add, Matrix.mulVec_zero, add_zero] at h0
      exact (smul_eq_zero.1 h0).resolve_right hy
    subst ht
    rfl
  have hfr : Module.finrank E ((E × E) × (Fin n₁ → E)) = Module.finrank E (Fin n → E) := by
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun, hn]
    omega
  obtain ⟨⟨⟨a, t⟩, u⟩, hp⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj v
  refine ⟨a, t, u, ?_⟩
  rw [← hp, hL]
  abel

end GlobalTheory.IsoLineCT

namespace GlobalTheory.IsoLineCT

open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.LeviPlane Formalism.UG GlobalTheory.UnipMem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem gen_iff' {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0) {d d₁ : ℕ} {W : Spc F E d}
    {H' : Plane E d d₁} (hxx : fm (σ : E →+* E) W.J H'.x H'.x = 0) (hxy : fm (σ : E →+* E) W.J H'.x H'.y = 1)
    (hxι : ∀ w, fm (σ : E →+* E) W.J H'.x (H'.ι *ᵥ w) = 0)
    (hsplit : ∀ v : Fin d → E, ∃ (a t : E) (u : Fin d₁ → E), v = a • H'.x + H'.ι *ᵥ u + t • H'.y) (u : UA σ W.J) :
    (mat u *ᵥ incV F H'.x = incV F H'.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x) ↔
    ((mat u - 1) * adMat F (Matrix.of fun i (_ : Fin 1) => H'.x i) = 0 ∧
      adMat F (cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ)) * (mat u - 1) = 0 ∧
      ∀ x : Fin d → E, (cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ)) *ᵥ x = 0 →
        ∃ a : Fin 1 → AE F E, (mat u - 1) *ᵥ incV F x = adMat F (Matrix.of fun i (_ : Fin 1) => H'.x i) *ᵥ a) := by
  have hcol : ∀ a : Fin 1 → AE F E, adMat F (Matrix.of fun i (_ : Fin 1) => H'.x i) *ᵥ a = a 0 • incV F H'.x := fun a => by
    funext i; simp [Matrix.mulVec, dotProduct, incV, mul_comm]
  have h1 : (mat u - 1) * adMat F (Matrix.of fun i (_ : Fin 1) => H'.x i) = 0 ↔ mat u *ᵥ incV F H'.x = incV F H'.x := by
    rw [← sub_eq_zero (a := mat u *ᵥ _), show mat u *ᵥ incV F H'.x - incV F H'.x = (mat u - 1) *ᵥ incV F H'.x by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
    exact ⟨fun h => funext fun i => congrFun (congrFun h i) 0, fun h => Matrix.ext fun i _ => congrFun h i⟩
  have hrow : ∀ (v : Fin d → E) k, ((cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ)) *ᵥ v) k =
      c * σ (fm (σ : E →+* E) W.J H'.x v) := fun v k => row_mulVec (s := (σ : E →+* E)) hσ W.J c H'.x v k
  rw [h1]
  refine and_congr_right fun hx => ⟨fun h => ⟨?_, fun v hv => ?_⟩, fun h z => ?_⟩
  · have e : adMat F (cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ)) =
        cT (cA σ).toRingHom (Matrix.of fun i (_ : Fin 1) => incV F H'.x i) *
          (inclR (F := F) (AF F) c • (incM F W.J).map (cA σ).toRingHom) := by
      ext k j
      simp only [adMat, cT, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
        smul_eq_mul, map_sum, map_mul, incV, incM, cAr_inclR, RingHom.coe_coe]
    have hu : (mat u)ᵀ * incM F W.J * (mat u).map (cA σ).toRingHom = incM F W.J := u.2
    rw [e]
    refine Matrix.ext_of_mulVec_single fun j => funext fun k => ?_
    rw [← Matrix.mulVec_mulVec, row_mulVec (cA_invol hσ), Matrix.sub_mulVec, Matrix.one_mulVec, fm_sub_right]
    conv_lhs => enter [2, 2, 1]; rw [← hx, fm_mulVec hu]
    simp
  · obtain ⟨a, t, w, rfl⟩ := hsplit v
    have ht := congrFun hv 0
    rw [hrow, fm_add_right, fm_add_right, fm_smul_right, fm_smul_right, hxι, hxx, hxy] at ht
    have ht0 : t = 0 := by simpa [hc] using ht
    obtain ⟨b, hb⟩ := h (incV F w)
    refine ⟨fun _ => b, ?_⟩
    have e : incV F (a • H'.x + H'.ι *ᵥ w + t • H'.y) = inclR (F := F) (AF F) a • incV F H'.x + incM F H'.ι *ᵥ incV F w := by
      rw [ht0, zero_smul, add_zero, ← incV_mulVec]; funext i; simp [incV]
    rw [hcol, e, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hx, hb]
    abel
  · have h3 : ∀ j : Fin d₁, ∃ a : AE F E, (mat u - 1) *ᵥ (incM F H'.ι *ᵥ Pi.single j 1) = a • incV F H'.x := fun j => by
      obtain ⟨a, ha⟩ := h.2 (H'.ι *ᵥ Pi.single j 1) (funext fun k => by rw [hrow, hxι]; simp)
      refine ⟨a 0, ?_⟩
      rw [← hcol, ← ha, incV_mulVec]
      congr 2
      funext i; by_cases hij : i = j <;> simp [incV, Pi.single_apply, hij]
    choose a ha using h3
    refine ⟨∑ j, z j * a j, ?_⟩
    rw [← sub_eq_iff_eq_add', show mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z = (mat u - 1) *ᵥ (incM F H'.ι *ᵥ z) by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
    conv_lhs => rw [show z = ∑ j, z j • Pi.single j 1 from by funext i; simp [Finset.sum_apply, Pi.single_apply]]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, ha, smul_smul, Finset.sum_smul]

theorem mem_unip_iff' {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0) {d d₁ : ℕ} {W : Spc F E d}
    {H' : Plane E d d₁} (hxx : fm (σ : E →+* E) W.J H'.x H'.x = 0) (hxy : fm (σ : E →+* E) W.J H'.x H'.y = 1)
    (hxι : ∀ w, fm (σ : E →+* E) W.J H'.x (H'.ι *ᵥ w) = 0)
    (hsplit : ∀ v : Fin d → E, ∃ (a t : E) (u : Fin d₁ → E), v = a • H'.x + H'.ι *ᵥ u + t • H'.y) (g : UA σ W.J) :
    g ∈ unip σ W H' ↔ toGAd hσ W.J hc g ∈ unipRad σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) := by
  have e : (unip σ W H').map (toGAd hσ W.J hc).toMonoidHom =
      unipRad σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) := by
    rw [unip, MonoidHom.map_closure, unipRad]
    congr 1
    ext k
    obtain ⟨u, rfl⟩ := (toGAd hσ W.J hc).surjective k
    refine ((toGAd hσ W.J hc).injective.mem_set_image).trans ?_
    exact gen_iff' hσ hc hxx hxy hxι hsplit u
  rw [← e]
  exact (Subgroup.mem_map_iff_mem (f := (toGAd hσ W.J hc).toMonoidHom) (toGAd hσ W.J hc).injective).symm

end GlobalTheory.IsoLineCT

namespace GlobalTheory.IsoLineCT

open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.LeviPlane Formalism.UG GlobalTheory.UnipMem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isConstTerm_of_isCT {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0) {n d₁ : ℕ} {W : Spc F E n}
    {H' : Plane E n d₁} (hxx : fm (σ : E →+* E) W.J H'.x H'.x = 0) (hxy : fm (σ : E →+* E) W.J H'.x H'.y = 1)
    (hxι : ∀ w, fm (σ : E →+* E) W.J H'.x (H'.ι *ᵥ w) = 0)
    (hsplit : ∀ v : Fin n → E, ∃ (a t : E) (u : Fin d₁ → E), v = a • H'.x + H'.ι *ᵥ u + t • H'.y)
    (f : UA σ W.J → ℂ) (hf : IsCT H' f 0) :
    IsConstTerm σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) (fun x => f ((toGAd hσ W.J hc).symm x)) 0 := by
  let C : Matrix (Fin n) (Fin 1) E := Matrix.of fun i (_ : Fin 1) => H'.x i
  intro μ 𝓕 hμ h𝓕 h1 g
  let e := toGAd hσ W.J hc
  have hmem : ∀ u, u ∈ unip σ W H' ↔ e u ∈ unipRad σ (c • W.J.map σ) C := fun u =>
    mem_unip_iff' hσ hc hxx hxy hxι hsplit u
  let e' : unipRad σ (c • W.J.map σ) C ≃* unip σ W H' :=
    { toFun := fun v => ⟨e.symm v.1, (hmem _).2 (by rw [e.apply_symm_apply]; exact v.2)⟩
      invFun := fun u => ⟨e u.1, (hmem u.1).1 u.2⟩
      left_inv := fun v => Subtype.ext (e.apply_symm_apply v.1)
      right_inv := fun u => Subtype.ext (e.symm_apply_apply u.1)
      map_mul' := fun u v => Subtype.ext (map_mul e.symm u.1 v.1) }
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hes : Continuous e.symm := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have he' : Continuous e' := (hes.comp continuous_subtype_val).subtype_mk _
  have hes' : Continuous e'.symm := (he.comp continuous_subtype_val).subtype_mk _
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ W.J) := ⟨by
    have h : (fun p : UA σ W.J × UA σ W.J => p.1 * p.2) =
        e.symm ∘ (fun q : GAd σ (c • W.J.map σ) × GAd σ (c • W.J.map σ) => q.1 * q.2) ∘ Prod.map e e := by
      funext p
      simp
    rw [h]
    exact hes.comp (continuous_mul.comp (he.prodMap he))⟩
  haveI : ContinuousInv (UA σ W.J) := ⟨by
    have h : (fun p : UA σ W.J => p⁻¹) = e.symm ∘ (fun q : GAd σ (c • W.J.map σ) => q⁻¹) ∘ e := by
      funext p
      simp
    rw [h]
    exact hes.comp (continuous_inv.comp he)⟩
  haveI : IsTopologicalGroup (UA σ W.J) := {}
  haveI : IsTopologicalGroup (unip σ W H') := inferInstance
  let t : unipRad σ (c • W.J.map σ) C ≃ₜ unip σ W H' := ⟨e'.toEquiv, he', hes'⟩
  let me := t.toMeasurableEquiv
  have hp : MeasurePreserving me μ (μ.map me) := ⟨me.measurable, rfl⟩
  have hHaar : (μ.map me).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e' he' hes'
  have hps : MeasurePreserving me.symm (μ.map me) μ := hp.symm
  have hmemU : ∀ γ : (GlobalTheory.AdelicU.ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C),
      e' γ.1 ∈ (ratU σ W.J).subgroupOf (unip σ W H') := fun γ => by
    obtain ⟨u, -, hu2⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ.2))
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ⟨u, hu2⟩)
  have hmemP : ∀ δ : (ratU σ W.J).subgroupOf (unip σ W H'),
      e'.symm δ.1 ∈ (GlobalTheory.AdelicU.ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C) := fun δ => by
    obtain ⟨m, hm⟩ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 δ.2)
    have h2 := (e δ.1.1).2
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, ?_, hm⟩))
    exact unitary_of_map_inclR σ n _ m _ (by rw [hm]; rfl) h2
  let fm' : (GlobalTheory.AdelicU.ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C) →
      (ratU σ W.J).subgroupOf (unip σ W H') := fun γ => ⟨e' γ.1, hmemU γ⟩
  have hfb : Function.Bijective fm' :=
    ⟨fun a b hab => Subtype.ext (e'.injective (congrArg Subtype.val hab)),
      fun δ => ⟨⟨e'.symm δ.1, hmemP δ⟩, Subtype.ext (e'.apply_symm_apply δ.1)⟩⟩
  have hfd := h𝓕.preimage_of_equiv hps.quasiMeasurePreserving hfb fun γ x => by
    show e'.symm (e' γ.1 * x) = γ.1 * e'.symm x
    rw [map_mul, e'.symm_apply_apply]
  have hset : me ⁻¹' (me.symm ⁻¹' 𝓕) = 𝓕 := by
    ext x
    simp
  have hmass : (μ.map me) (me.symm ⁻¹' 𝓕) = 1 := by
    rw [me.map_apply, hset, h1]
  have hc' := hf (μ.map me) (me.symm ⁻¹' 𝓕) hHaar hfd hmass (e.symm g)
  rw [← hp.setIntegral_preimage_emb me.measurableEmbedding, hset] at hc'
  refine hc'.trans (integral_congr_ae (.of_forall fun u => ?_))
  show f (e.symm u.1 * e.symm g) = f (e.symm (u.1 * g))
  rw [map_mul]

end GlobalTheory.IsoLineCT

namespace GlobalTheory.IsoLineCT

theorem isConstTerm_isoPlane : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (∀ j < G.p, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) →
      ∀ i < G.p, ∀ f ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i, IsCT (W := sp i) (pl i) f 0 →
      ∀ c₀ : E, c₀ ≠ 0 → IsHermND σ (c₀ • (sp i).J.map σ) → ∀ φ' : GAd σ (c₀ • (sp i).J.map σ) → ℂ,
        (∀ (g : UA σ (sp i).J) (g' : GAd σ (c₀ • (sp i).J.map σ)), g.1 = g'.1 → φ' g' = f g) →
        (Matrix.of fun k (_ : Fin 1) => (pl i).x k) ≠ 0 ∧
        Formalism.UG.cT (σ : E →+* E) (Matrix.of fun k (_ : Fin 1) => (pl i).x k) * (c₀ • (sp i).J.map σ) * (Matrix.of fun k (_ : Fin 1) => (pl i).x k) = 0 ∧
        GlobalTheory.UAut.IsConstTerm σ (c₀ • (sp i).J.map σ) (Matrix.of fun k (_ : Fin 1) => (pl i).x k) φ' 0 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' R Rf hM _ d₁ H' i₀ i₁ sp pl _ hP c _ _ i hi f _ hct c₀ hc₀ hherm φ' hφ'
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hM.triple.base.cm
  have hPi := hP i hi
  have hxx : GlobalTheory.LeviPlane.fm (σ : E →+* E) (sp i).J (pl i).x (pl i).x = 0 := hPi.2.1
  have hxy : GlobalTheory.LeviPlane.fm (σ : E →+* E) (sp i).J (pl i).x (pl i).y = 1 := hPi.2.2.2.1
  have hxι : ∀ w, GlobalTheory.LeviPlane.fm (σ : E →+* E) (sp i).J (pl i).x ((pl i).ι *ᵥ w) = 0 := fun w => by
    have h := fm_swap hσ hherm.1 (pl i).x ((pl i).ι *ᵥ w)
    rw [show GlobalTheory.LeviPlane.fm (σ : E →+* E) (sp i).J ((pl i).ι *ᵥ w) (pl i).x = 0 from (hPi.2.2.2.2.1 w).1, map_zero,
      mul_zero] at h
    exact (mul_eq_zero.1 h).resolve_left ((map_ne_zero σ).2 hc₀)
  have hsplit := split_of_iso hPi
  have hφ : φ' = fun x => f ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ (sp i).J hc₀).symm x) :=
    funext fun x => hφ' _ x rfl
  refine ⟨fun h0 => ?_, ?_, ?_⟩
  · have hx : (pl i).x = 0 := funext fun k => congrFun (congrFun h0 k) 0
    rw [hx] at hxy
    simp [GlobalTheory.LeviPlane.fm] at hxy
  · ext k l
    refine (GlobalTheory.UnipMem.row_mulVec (s := (σ : E →+* E)) hσ (sp i).J c₀ (pl i).x (pl i).x k).trans ?_
    rw [hxx]
    simp
  · rw [hφ]
    exact isConstTerm_of_isCT hσ hc₀ hxx hxy hxι hsplit f hct

end GlobalTheory.IsoLineCT

end
