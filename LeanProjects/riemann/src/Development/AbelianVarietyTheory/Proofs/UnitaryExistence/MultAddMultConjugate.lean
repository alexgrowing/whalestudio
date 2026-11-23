import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ReflexNormIndexIdeal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulMemOfMemSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoeEqSpanDetOfIntVecLe

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatticeBetaCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise

section Index

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def detSpan (M : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) E := Submodule.span (𝓞 E) (detSet M)

omit [NumberField E] in
theorem detSet_eq (M : Submodule (𝓞 E) (Fin n → E)) :
    detSet M = {d | ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ M) ∧ d = (Matrix.of v).det} := by
  ext d
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [← Matrix.det_transpose (Matrix.of v)]
  rfl

omit [NumberField E] in
theorem indexIdeal_smul_le (L' L : Submodule (𝓞 E) (Fin n → E)) :
    indexIdeal L' L • detSpan L' ≤ detSpan L := by
  rw [indexIdeal, detSpan, Submodule.span_smul_span, Submodule.span_le]
  rintro _ ⟨a, ⟨g, hg, ha⟩, _, ⟨v, hv, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨fun i => g (v i), fun i => hg _ (hv i), ?_⟩
  have : (Matrix.of fun i j => g (v j) i) = LinearMap.toMatrix' g * Matrix.of fun i j => v j i := by
    ext i j
    rw [Matrix.of_apply, ← LinearMap.toMatrix'_mulVec]
    rfl
  rw [this, Matrix.det_mul, LinearMap.det_toMatrix', ← ha]
  rfl

theorem le_indexIdeal_smul {L' L : Submodule (𝓞 E) (Fin n → E)} (hle : L ≤ L') (hfg : L'.FG)
    (hsp : Submodule.span E (L' : Set (Fin n → E)) = ⊤) : detSpan L ≤ indexIdeal L' L • detSpan L' := by
  classical
  obtain ⟨-, f, c, hf, hc, hΛ, -⟩ :=
    exists_pseudoCoords (R := 𝓞 E) (K := E) n (Fin n → E) (by simp) L' ⊤ hfg hsp
  set F : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' (LinearMap.pi f) with hF
  have hFv : ∀ v, F.mulVec v = fun a => f a v := fun v => by rw [hF, LinearMap.toMatrix'_mulVec]; rfl
  have hF0 : F.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    rw [hFv] at hv
    exact hv0 (hf v fun a => congrFun hv a)
  have hint : ∀ a, ∀ y ∈ (c a)⁻¹, ∀ z ∈ c a, ∃ b : 𝓞 E, (b : E) = y * z := fun a y hy z hz =>
    (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff (hc a)).1 hy z hz)
  rw [detSpan, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  set W : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => w j i with hW
  have h1 : (1 : E) ∈ Submodule.span (𝓞 E)
      (∏ a, ((((c a)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) * (c a : Set E))) := by
    rw [← Submodule.prod_span]
    have : ∀ a, Submodule.span (𝓞 E) ((((c a)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) * (c a : Set E)) = 1 := by
      intro a
      rw [← Submodule.span_mul_span, ← FractionalIdeal.coe_one (S := (𝓞 E)⁰), ← inv_mul_cancel₀ (hc a),
        FractionalIdeal.coe_mul]
      congr 1 <;> exact Submodule.span_eq _
    simp only [this, Finset.prod_const_one]
    exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have key : ∀ z ∈ Submodule.span (𝓞 E)
      (∏ a, ((((c a)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) * (c a : Set E))),
      z * W.det ∈ indexIdeal L' L • detSpan L' := by
    intro z hz
    induction hz using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := (Set.mem_fintype_prod _ _).1 hz
      choose y hy t ht hyt using hu
      obtain rfl : u = fun a => y a * t a := funext fun a => (hyt a).symm
      choose b hb using fun a i => hint a _ (hy a) _ ((hΛ _).1 (hle (hw i)) a)
      have hB : (((Matrix.of b).det : 𝓞 E) : E) = W.det * ((∏ a, y a) * F.det) := by
        have : (algebraMap (𝓞 E) E).mapMatrix (Matrix.of b) = Matrix.diagonal y * F * W := by
          ext a i
          rw [Matrix.mul_assoc, Matrix.diagonal_mul]
          exact (hb a i).trans (congrArg _ (congrFun (hFv (w i)) a).symm)
        change algebraMap (𝓞 E) E _ = _
        rw [RingHom.map_det, this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm]
      have hI : (Matrix.of b).det ∈ indexIdeal L' L := by
        refine Ideal.subset_span ⟨Matrix.toLin' (W * (Matrix.diagonal y * F)), fun x hx => ?_, ?_⟩
        · choose b' hb' using fun a => hint a _ (hy a) _ ((hΛ _).1 hx a)
          have : Matrix.toLin' (W * (Matrix.diagonal y * F)) x = ∑ a, b' a • w a := by
            rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hFv]
            ext i
            simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
            change ∑ a, W i a * (Matrix.diagonal y).mulVec (fun a => f a x) a = _
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Matrix.mulVec_diagonal, ← hb', mul_comm]
            rfl
          rw [this]
          exact Submodule.sum_mem _ fun a _ => L.smul_mem _ (hw a)
        · rw [LinearMap.det_toLin', Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hB]
      have hV : (F.det)⁻¹ * ∏ a, t a ∈ detSpan L' := by
        refine Submodule.subset_span ⟨fun i => F⁻¹.mulVec (Pi.single i (t i)), fun i => (hΛ _).2 fun a => ?_, ?_⟩
        · have := congrFun (hFv (F⁻¹.mulVec (Pi.single i (t i)))) a
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hF0.isUnit, Matrix.one_mulVec] at this
          rw [← this]
          by_cases h : a = i
          · subst h; simpa using ht a
          · rw [Pi.single_eq_of_ne h]; exact (c a).zero_mem
        · have : (Matrix.of fun i j => F⁻¹.mulVec (Pi.single j (t j)) i) = F⁻¹ * Matrix.diagonal t := by
            ext i j
            simp [Matrix.mul_diagonal]
          rw [this, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      have := Submodule.smul_mem_smul hI hV
      convert this using 1
      rw [Algebra.smul_def, Finset.prod_mul_distrib]
      change _ = (((Matrix.of b).det : 𝓞 E) : E) * _
      rw [hB]
      field_simp
  simpa using key 1 h1

theorem detSpan_eq {L' L : Submodule (𝓞 E) (Fin n → E)} (hle : L ≤ L') (hfg : L'.FG)
    (hsp : Submodule.span E (L' : Set (Fin n → E)) = ⊤) : detSpan L = indexIdeal L' L • detSpan L' :=
  le_antisymm (le_indexIdeal_smul hle hfg hsp) (indexIdeal_smul_le L' L)

theorem span_inter (Λ : Lat E n) : Submodule.span E (Λ.inter : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff, ← (Lat.std E n).span_top, Submodule.span_le]
  intro x hx
  obtain ⟨d, hd, h⟩ := exists_smul_mem_of_mem_span_fraction (K := E) Λ.L x (Λ.span_top ▸ Submodule.mem_top)
  have h3 : d • x ∈ Submodule.span E (Λ.inter : Set (Fin n → E)) :=
    Submodule.subset_span ⟨(stdMod E n).smul_mem d hx, h⟩
  have h4 := Submodule.smul_mem _ ((algebraMap (𝓞 E) E d)⁻¹) h3
  rwa [← algebraMap_smul E d, inv_smul_smul₀ (by simpa using hd)] at h4

theorem detSpan_inter (Λ : Lat E n) : detSpan Λ.inter = latIdeal Λ • detSpan Λ.L :=
  detSpan_eq inf_le_right Λ.fg Λ.span_top

theorem absNorm_latIdeal (Λ : Lat E n) :
    Ideal.absNorm (latIdeal Λ) = Λ.inter.toAddSubgroup.relIndex Λ.L.toAddSubgroup := by
  obtain ⟨𝔫, -, hN, h⟩ := GlobalTheory.TensorLat.exists_indexIdeal_span_det (inf_le_right : Λ.inter ≤ Λ.L) Λ.fg (span_inter Λ)
  have := detSpan_inter Λ
  rw [detSpan, detSpan, detSet_eq, detSet_eq] at this
  rw [(h _).1 this, hN]
  rfl

theorem isUnit_detSpan (Λ : Lat E n) : IsUnit (detSpan Λ.L) := by
  obtain ⟨J, -, h0, -, hJ, -⟩ := GlobalTheory.TensorLat.exists_coe_eq_span_det (le_refl Λ.L) Λ.fg Λ.span_top
  rw [detSpan, detSet_eq, ← hJ]
  refine IsUnit.of_mul_eq_one ((J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) ?_
  rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ h0, FractionalIdeal.coe_one]

end Index

section Push

variable {E F : Type} [Field E] [Field F] (φ : E →+* F)

theorem span_image_span (S : Set E) :
    Submodule.span (𝓞 F) (φ '' (Submodule.span (𝓞 E) S : Set E)) = Submodule.span (𝓞 F) (φ '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx =>
    have : φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x := by
      change φ ((b : E) * x) = _
      rw [map_mul]; rfl
    rw [this]; exact Submodule.smul_mem _ _ hx

def extend : Submodule (𝓞 E) E →* Submodule (𝓞 F) F where
  toFun M := Submodule.span (𝓞 F) (φ '' M)
  map_one' := by rw [Submodule.one_eq_span, span_image_span, Set.image_singleton, map_one, Submodule.one_eq_span]
  map_mul' M N := by
    rw [Submodule.mul_eq_span_mul_set, span_image_span, Set.image_mul, Submodule.span_mul_span]

def coeI (E : Type) [Field E] : Ideal (𝓞 E) →* Submodule (𝓞 E) E where
  toFun := IsLocalization.coeSubmodule E
  map_one' := by rw [Ideal.one_eq_top, IsLocalization.coeSubmodule_top]
  map_mul' := IsLocalization.coeSubmodule_mul E

theorem smul_eq_coeI_mul (𝔞 : Ideal (𝓞 E)) (N : Submodule (𝓞 E) E) : 𝔞 • N = coeI E 𝔞 * N := by
  refine le_antisymm (Submodule.smul_le.2 fun a ha x hx => ?_) (Submodule.mul_le.2 ?_)
  · rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul ⟨a, ha, rfl⟩ hx
  · rintro _ ⟨a, ha, rfl⟩ x hx
    exact (Algebra.smul_def a x) ▸ Submodule.smul_mem_smul ha hx

theorem span_image_ideal (𝔞 : Ideal (𝓞 E)) :
    Submodule.span (𝓞 F) (φ.comp (algebraMap (𝓞 E) E) '' (𝔞 : Set (𝓞 E))) =
      coeI F (𝔞.map (RingOfIntegers.mapRingHom φ)) := by
  change _ = IsLocalization.coeSubmodule F (Ideal.span _)
  rw [IsLocalization.coeSubmodule_span, Set.image_image]
  rfl

theorem extend_coeI (𝔞 : Ideal (𝓞 E)) :
    extend φ (coeI E 𝔞) = coeI F (𝔞.map (RingOfIntegers.mapRingHom φ)) := by
  rw [← span_image_ideal]
  change Submodule.span (𝓞 F) (φ '' (algebraMap (𝓞 E) E '' (𝔞 : Set (𝓞 E)))) = _
  rw [Set.image_image]
  rfl

theorem span_eq_coeI_iff [NumberField F] (β : F) (I : Ideal (𝓞 F)) :
    Submodule.span (𝓞 F) {β} = coeI F I ↔ ∃ b : 𝓞 F, (b : F) = β ∧ Ideal.span {b} = I := by
  constructor
  · intro h
    obtain ⟨b, -, rfl⟩ : β ∈ coeI F I := h ▸ Submodule.mem_span_singleton_self β
    refine ⟨b, rfl, IsFractionRing.coeSubmodule_injective (𝓞 F) F ?_⟩
    rw [IsLocalization.coeSubmodule_span_singleton]
    exact h
  · rintro ⟨b, rfl, rfl⟩
    exact (IsLocalization.coeSubmodule_span_singleton F b).symm

end Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

theorem idealAt_eq (M : Submodule (𝓞 E) (Fin n → E)) (τ : E →+* ℂ) :
    idealAt c M τ = extend (embF c τ) (detSpan M) := (span_image_span _ _).symm

theorem idealAt_inter (Λ : Lat E n) (τ : E →+* ℂ) :
    idealAt c Λ.inter τ = coeI c.F ((latIdeal Λ).map (RingOfIntegers.mapRingHom (embF c τ))) * idealAt c Λ.L τ := by
  rw [idealAt_eq, idealAt_eq, detSpan_inter, smul_eq_coeI_mul, map_mul, extend_coeI]

theorem coeI_reflexIdeal (𝔞 : Ideal (𝓞 E)) : coeI c.F (reflexIdeal Dw c 𝔞) =
    ∏ τ : E →+* ℂ, coeI c.F (𝔞.map (RingOfIntegers.mapRingHom (embF c τ))) ^ Dw.mult τ := by
  simp only [reflexIdeal, map_prod, map_pow]

theorem betaIs_iff (Λ : Lat E n) (β : c.F) : BetaIs (Dw := Dw) c (toGen Λ) β ↔
    ∃ b : 𝓞 c.F, (b : c.F) = β ∧ Ideal.span {b} = reflexIdeal Dw c (latIdeal Λ) := by
  have hu : IsUnit (∏ τ : E →+* ℂ, idealAt c Λ.L τ ^ Dw.mult τ) :=
    IsUnit.prod_iff.2 fun τ _ => by rw [idealAt_eq]; exact ((isUnit_detSpan Λ).map _).pow _
  rw [← span_eq_coeI_iff, coeI_reflexIdeal, BetaIs, ln_eq]
  simp only [idealAt_inter, mul_pow, Finset.prod_mul_distrib]
  exact hu.mul_left_inj

theorem betaAbs_iff (Λ : Lat E n) (β : c.F) : BetaAbs (Dw := Dw) c (toGen Λ) β ↔
    ∀ s : c.F →+* ℂ, ‖s β‖ ^ 2 = (Ideal.absNorm (latIdeal Λ) : ℝ) ^ (Dw.p + Dw.q) := by
  rw [BetaAbs, ln_eq, absNorm_latIdeal]
  rfl

variable {Dw c} in
theorem isBe_ne_zero {𝔞 : Ideal (𝓞 E)} (h0 : 𝔞 ≠ ⊥) {β : c.F} (h : IsBe Dw c 𝔞 β) : β ≠ 0 := by
  rintro rfl
  have := h.2 c.F.val.toRingHom
  rw [map_zero, norm_zero, zero_pow two_ne_zero] at this
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 h0)) this.symm

theorem beta_iff' (Λ : Lat E n) (β : c.F) :
    (BetaIs (Dw := Dw) c (toGen Λ) β ∧ BetaAbs (Dw := Dw) c (toGen Λ) β) ↔ IsBeLat Dw c Λ β := by
  rw [betaIs_iff, betaAbs_iff]; rfl

theorem beta_iff (Λ : Lat E n) (β : c.F) :
    (β ≠ 0 ∧ BetaIs (Dw := Dw) c (toGen Λ) β ∧ BetaAbs (Dw := Dw) c (toGen Λ) β) ↔ IsBeLat Dw c Λ β := by
  rw [beta_iff']
  exact and_iff_right_of_imp (isBe_ne_zero (latIdeal_ne_bot Λ))

theorem isBe_iff (𝔞 : Ideal (𝓞 E)) (β : c.F) : IsBe Dw c 𝔞 β ↔
    Submodule.span (𝓞 c.F) {β} =
      ∏ τ : E →+* ℂ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ ∧
    ∀ σ : c.F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ (Dw.p + Dw.q) := by
  rw [IsBe, ← span_eq_coeI_iff, coeI_reflexIdeal]
  simp only [embK, span_image_ideal]

theorem kPsiIn_iff : KPsiIn (Dw := Dw) c ↔ ReflexLe Dw c :=
  forall₂_congr fun 𝔞 h0 => exists_congr fun β => by
    rw [← isBe_iff]
    exact and_iff_right_of_imp (isBe_ne_zero h0)

variable {Dw c} in

theorem isBe_unique {𝔞 : Ideal (𝓞 E)} (h0 : 𝔞 ≠ ⊥) {β β' : c.F} (h : IsBe Dw c 𝔞 β) (h' : IsBe Dw c 𝔞 β') :
    ∃ ζ : c.F, IsOfFinOrder ζ ∧ β' = ζ * β := by
  have hβ := isBe_ne_zero h0 h
  obtain ⟨⟨b, rfl, hb⟩, ha⟩ := h
  obtain ⟨⟨b', rfl, hb'⟩, ha'⟩ := h'
  obtain ⟨u, rfl⟩ : ∃ u, u * b = b' := Ideal.mem_span_singleton'.1 (by
    rw [hb, ← hb']; exact Ideal.mem_span_singleton_self _)
  refine ⟨u, isOfFinOrder_iff_pow_eq_one.2 ?_, rfl⟩
  obtain ⟨m, hm, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one c.F ℂ u.isIntegral_coe fun s => by
    have h1 := (ha' s).trans (ha s).symm
    have h2 : ‖s b‖ ≠ 0 := by simpa using hβ
    rw [pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero] at h1
    change ‖s ((u : c.F) * b)‖ = _ at h1
    rw [map_mul, norm_mul] at h1
    exact mul_right_cancel₀ h2 (h1.trans (one_mul _).symm)
  exact ⟨m, hm, h⟩

theorem isBeLat_betaH (Λ : Lat E n) (h : ∃ β, IsBeLat Dw c Λ β) :
    IsBeLat Dw c Λ (betaH (Dw := Dw) c (toGen Λ)) := by
  have h' := h.imp fun β => (beta_iff Dw c Λ β).2
  rw [betaH, dif_pos h']
  exact (beta_iff Dw c Λ _).1 h'.choose_spec

theorem betaH_eq (hK : ReflexLe Dw c) (Λ : Lat E n) :
    ∃ ζ : c.F, IsOfFinOrder ζ ∧ betaH (Dw := Dw) c (toGen Λ) = ζ * be hK Λ :=
  isBe_unique (latIdeal_ne_bot Λ) (be_spec hK Λ) (isBeLat_betaH Dw c Λ ⟨_, be_spec hK Λ⟩)

theorem betaH_congr {n' : ℕ} {Λ : Lat E n} {Λ' : Lat E n'} (h : latIdeal Λ = latIdeal Λ') :
    betaH (Dw := Dw) c (toGen Λ) = betaH (Dw := Dw) c (toGen Λ') := by
  have e : (fun β : c.F => β ≠ 0 ∧ BetaIs (Dw := Dw) c (toGen Λ) β ∧ BetaAbs (Dw := Dw) c (toGen Λ) β) =
      fun β : c.F => β ≠ 0 ∧ BetaIs (Dw := Dw) c (toGen Λ') β ∧ BetaAbs (Dw := Dw) c (toGen Λ') β :=
    funext fun β => propext (by rw [beta_iff, beta_iff, IsBeLat, IsBeLat, h])
  unfold betaH
  generalize (fun β : c.F => β ≠ 0 ∧ BetaIs (Dw := Dw) c (toGen Λ) β ∧ BetaAbs (Dw := Dw) c (toGen Λ) β) = p at e ⊢
  subst e
  rfl

theorem mult_add_mult_conjugate (τ : E →+* ℂ) :
    Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ) = Dw.p + Dw.q := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have h2 : starRingEnd ℂ (τ (H.rt : E)) = -τ (H.rt : E) := by
    generalize τ (H.rt : E) = z at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at hre him
    have h0 : z.re = 0 := by
      by_contra h
      have : z.im = 0 := mul_left_cancel₀ h (by linarith)
      rw [this] at hre
      nlinarith
    apply Complex.ext <;> simp [h0]
  have h3 : H.rt0 ≠ -H.rt0 := fun h => by
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    have := H.sqrt_neg_disc_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  simp only [Datum.mult, ComplexEmbedding.conjugate_coe_eq, h2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h | h
  · rw [h, if_pos rfl, if_neg h3.symm]
  · rw [h, neg_neg, if_pos rfl, if_neg h3.symm, add_comm]

theorem norm_reflexNorm (γ : E) (s : c.F →+* ℂ) :
    ‖s (reflexNorm Dw c γ)‖ ^ 2 = |(Algebra.norm ℚ γ : ℝ)| ^ (Dw.p + Dw.q) := by
  have h1 : ∀ σ : E →+* ℂ, ‖s (embF c (ComplexEmbedding.conjugate σ) γ)‖ = ‖s (embF c σ γ)‖ := fun σ => by
    have e : embF c (ComplexEmbedding.conjugate σ) γ = embF c σ (IsCMField.complexConj E γ) :=
      Subtype.ext (IsCMField.complexEmbedding_complexConj E σ γ).symm
    have := IsCMField.complexEmbedding_complexConj E (s.comp (embF c σ)) γ
    rw [e]
    exact (congrArg norm this).trans (Complex.norm_conj _)
  have h2 : ∏ σ : E →+* ℂ, ‖s (embF c σ γ)‖ ^ Dw.mult σ =
      ∏ σ : E →+* ℂ, ‖s (embF c σ γ)‖ ^ Dw.mult (ComplexEmbedding.conjugate σ) := by
    rw [← Equiv.prod_comp (ComplexEmbedding.involutive_conjugate E).toPerm]
    simp only [Function.Involutive.coe_toPerm, h1]
  have h3 : |(Algebra.norm ℚ γ : ℝ)| = ∏ σ : E →+* ℂ, ‖s (embF c σ γ)‖ := by
    have hb : Function.Bijective fun σ : E →+* ℂ => s.comp (embF c σ) :=
      Finite.injective_iff_bijective.1 fun σ τ h => RingHom.ext fun x =>
        congrArg Subtype.val (s.injective (DFunLike.congr_fun h x))
    rw [← norm_prod, Fintype.prod_bijective _ hb (fun σ => s (embF c σ γ)) (fun σ => σ γ) fun _ => rfl,
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ : E →+* ℂ => σ γ) (fun σ : E →ₐ[ℚ] ℂ => σ γ) fun _ => rfl,
      ← Algebra.norm_eq_prod_embeddings]
    simp
  rw [reflexNorm, map_prod, norm_prod, h3, sq]
  simp only [map_pow, norm_pow]
  nth_rewrite 2 [h2]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun σ _ => by rw [← pow_add, mult_add_mult_conjugate]

theorem isBe_principal (γ : 𝓞 E) : IsBe Dw c (Ideal.span {γ}) (reflexNorm Dw c (γ : E)) := by
  refine ⟨⟨∏ σ : E →+* ℂ, RingOfIntegers.mapRingHom (embF c σ) γ ^ Dw.mult σ, ?_, ?_⟩, fun s => ?_⟩
  · change algebraMap (𝓞 c.F) c.F _ = _
    simp only [map_prod, map_pow]
    rfl
  · simp only [reflexIdeal, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow,
      Ideal.prod_span_singleton]
  · rw [norm_reflexNorm, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
    simp

theorem reflexIdeal_mul (𝔞 𝔟 : Ideal (𝓞 E)) :
    reflexIdeal Dw c (𝔞 * 𝔟) = reflexIdeal Dw c 𝔞 * reflexIdeal Dw c 𝔟 := by
  simp only [reflexIdeal, Ideal.map_mul, mul_pow, Finset.prod_mul_distrib]

theorem reflexIdeal_pow (𝔞 : Ideal (𝓞 E)) (h : ℕ) : reflexIdeal Dw c (𝔞 ^ h) = reflexIdeal Dw c 𝔞 ^ h := by
  simp only [reflexIdeal, Ideal.map_pow, ← Finset.prod_pow, ← pow_mul, mul_comm h]

variable {Dw c}

theorem isBe_mul {𝔞 𝔟 : Ideal (𝓞 E)} {α β : c.F} (h : IsBe Dw c 𝔞 α) (h' : IsBe Dw c 𝔟 β) :
    IsBe Dw c (𝔞 * 𝔟) (α * β) := by
  obtain ⟨⟨a, rfl, ha⟩, h⟩ := h
  obtain ⟨⟨b, rfl, hb⟩, h'⟩ := h'
  refine ⟨⟨a * b, rfl, ?_⟩, fun s => ?_⟩
  · rw [reflexIdeal_mul, ← ha, ← hb, Ideal.span_singleton_mul_span_singleton]
  · rw [map_mul, norm_mul, mul_pow, h, h', map_mul, Nat.cast_mul, mul_pow]

theorem isBe_pow {𝔞 : Ideal (𝓞 E)} {α : c.F} (h : IsBe Dw c 𝔞 α) (k : ℕ) : IsBe Dw c (𝔞 ^ k) (α ^ k) := by
  induction k with
  | zero => simpa using isBe_top Dw c
  | succ k ih => rw [pow_succ, pow_succ]; exact isBe_mul ih h

theorem isBe_prod {ι : Type} (t : Finset ι) {𝔞 : ι → Ideal (𝓞 E)} {α : ι → c.F} (h : ∀ i, IsBe Dw c (𝔞 i) (α i)) :
    IsBe Dw c (∏ i ∈ t, 𝔞 i) (∏ i ∈ t, α i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isBe_top Dw c
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi]; exact isBe_mul (h i) ih

theorem isBe_of_pow {𝔞 : Ideal (𝓞 E)} {ψ : c.F} {k : ℕ} (hk : 0 < k) (h : IsBe Dw c (𝔞 ^ k) (ψ ^ k)) :
    IsBe Dw c 𝔞 ψ := by
  obtain ⟨⟨b, hb, hI⟩, h⟩ := h
  have hψ : IsIntegral ℤ ψ := IsIntegral.of_pow hk (hb ▸ b.isIntegral_coe)
  obtain ⟨b₀, rfl⟩ : ∃ b₀ : 𝓞 c.F, (b₀ : c.F) = ψ := ⟨⟨ψ, hψ⟩, rfl⟩
  refine ⟨⟨b₀, rfl, ?_⟩, fun s => ?_⟩
  · have e : b = b₀ ^ k := RingOfIntegers.ext hb
    rw [e, ← Ideal.span_singleton_pow, reflexIdeal_pow] at hI
    exact pow_left_injective hk.ne' hI
  · have := h s
    rw [map_pow, norm_pow, map_pow, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm k, pow_mul,
      pow_mul] at this
    exact (pow_left_inj₀ (by positivity) (by positivity) hk.ne').1 this

theorem exists_quotient' {R : Type} [CommRing R] [IsDomain R] {a b : R} {I : Ideal R} (ha : a ≠ 0)
    (hb : Ideal.span {b} = Ideal.span {a} * I) : ∃ u : R, u * a = b ∧ Ideal.span {u} = I := by
  have hba : b ∈ Ideal.span {a} * I := by rw [← hb]; exact Ideal.mem_span_singleton_self _
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ((Ideal.mul_le_left : Ideal.span {a} * I ≤ Ideal.span {a}) hba)
  refine ⟨u, rfl, ?_⟩
  rw [mul_comm u a, ← Ideal.span_singleton_mul_span_singleton] at hb
  exact (Ideal.span_singleton_mul_right_inj ha).1 hb

theorem exists_quotient {F : Type} [Field F] {a b : 𝓞 F} {I : Ideal (𝓞 F)} (ha : (a : F) ≠ 0)
    (hb : Ideal.span {b} = Ideal.span {a} * I) : ∃ u : 𝓞 F, (u : F) = (b : F) / a ∧ Ideal.span {u} = I := by
  obtain ⟨u, rfl, h⟩ := exists_quotient' (fun e => ha (by rw [e]; rfl)) hb
  exact ⟨u, by rw [eq_div_iff ha]; rfl, h⟩

theorem isBe_div {𝔞 𝔟 : Ideal (𝓞 E)} {α β : c.F} (h0 : 𝔞 ≠ ⊥) (h : IsBe Dw c 𝔞 α) (h' : IsBe Dw c (𝔞 * 𝔟) β) :
    IsBe Dw c 𝔟 (β / α) := by
  have hα := isBe_ne_zero h0 h
  obtain ⟨⟨a, rfl, ha⟩, h⟩ := h
  obtain ⟨⟨b, rfl, hb⟩, h'⟩ := h'
  rw [reflexIdeal_mul, ← ha] at hb
  refine ⟨exists_quotient hα hb, fun s => ?_⟩
  have : (Ideal.absNorm 𝔞 : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 h0)
  rw [map_div₀, norm_div, div_pow, h, h', map_mul, Nat.cast_mul, mul_pow,
    mul_div_cancel_left₀ _ (pow_ne_zero _ this)]

variable (Dw c)

theorem reflexLe_of_basis (hB : ReflexBasis Dw c) : ReflexLe Dw c := by
  obtain ⟨m, 𝔠, h, γ, ψ, hx, hγ, hψ⟩ := hB
  intro 𝔞 h0
  obtain ⟨a, ⟨ha, e⟩, -⟩ := hx (ClassGroup.mk0 ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h0⟩)
  have h1 : ∀ i, IsBe Dw c (𝔠 i) (ψ i) := fun i => isBe_of_pow (Nat.zero_lt_of_lt (ha i)) (by
    rw [hγ, hψ]; exact isBe_principal Dw c _)
  simp only [← map_pow, ← map_prod] at e
  obtain ⟨x, y, hx0, -, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 e
  have h2 := isBe_mul (isBe_principal Dw c y) (isBe_prod Finset.univ fun i => isBe_pow (h1 i) (a i))
  simp only [SubmonoidClass.coe_finset_prod, SubmonoidClass.coe_pow] at hxy
  rw [← hxy] at h2
  exact ⟨_, isBe_div (by simpa using hx0) (isBe_principal Dw c x) h2⟩

theorem reflexRoots_iff : ReflexRoots Dw c ↔ ReflexLe Dw c := by
  refine forall₂_congr fun 𝔞 h0 => ⟨?_, ?_⟩
  · rintro ⟨h, γ, ψ, hh, hγ, hψ⟩
    exact ⟨ψ, isBe_of_pow hh (by rw [hγ, hψ]; exact isBe_principal Dw c _)⟩
  · rintro ⟨β, hβ⟩
    let I : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h0⟩
    obtain ⟨h, hh, e⟩ := (isOfFinOrder_of_finite (ClassGroup.mk0 I)).exists_pow_eq_one
    rw [← map_pow] at e
    obtain ⟨γ, hγ⟩ : (𝔞 ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff (I ^ h).2).1 e
    change 𝔞 ^ h = Ideal.span {γ} at hγ
    obtain ⟨ζ, hζ, e⟩ := isBe_unique (pow_ne_zero h h0) (hγ ▸ isBe_principal Dw c γ) (isBe_pow hβ h)
    obtain ⟨k, hk, hζ⟩ := hζ.exists_pow_eq_one
    refine ⟨h * k, γ ^ k, β, Nat.mul_pos hh hk, by rw [pow_mul, hγ, Ideal.span_singleton_pow], ?_⟩
    rw [pow_mul, e, mul_pow, hζ, one_mul]
    simp only [reflexNorm, ← Finset.prod_pow, RingOfIntegers.coe_eq_algebraMap, map_pow, ← pow_mul, mul_comm k]

theorem mem_of_forall_prime {G : Type} [AddCommGroup G] (A : AddSubgroup G) (x : G)
    (h : ∀ p : ℕ, p.Prime → ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ A) : x ∈ A := by
  rw [← QuotientAddGroup.eq_zero_iff, ← AddMonoid.addOrderOf_eq_one_iff]
  by_contra hne
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hne
  obtain ⟨k, hk, hx⟩ := h p hp
  refine hk (hd.trans (addOrderOf_dvd_of_nsmul_eq_zero ?_))
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact hx

theorem stdForm_nsmul (k k' : ℕ) (x y : Fin n → E) : stdForm (k • x) (k' • y) = (k * k') • stdForm x y := by
  simp only [stdForm, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum, Nat.cast_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem selfDual_map {Λ : Lat E n} (h : Λ.SelfDual) {γ : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hγ : IsUnitary γ) :
    (Λ.map γ).SelfDual := by
  intro x
  obtain ⟨x, rfl⟩ := γ.surjective x
  constructor
  · rintro ⟨x', hx, e⟩ _ ⟨y, hy, rfl⟩
    obtain rfl : x' = x := γ.injective e
    exact (hγ x' y).symm ▸ (h x').1 hx y hy
  · intro hx
    exact ⟨x, (h x).2 fun y hy => hγ x y ▸ hx _ ⟨y, hy, rfl⟩, rfl⟩

theorem selfDual_of_inGenus {Λ : Lat E n} (h : Λ.InGenus) : Λ.SelfDual := by
  intro x
  constructor
  · intro hx y hy
    refine mem_of_forall_prime (algebraMap (𝓞 E) E).range.toAddSubgroup _ fun p hp => ?_
    obtain ⟨γ, hγ, h1, -⟩ := h p hp
    obtain ⟨k, hk, hx⟩ := h1 x hx
    obtain ⟨k', hk', hy⟩ := h1 y hy
    refine ⟨k * k', fun hd => (hp.dvd_mul.1 hd).elim hk hk', ?_⟩
    rw [← stdForm_nsmul]
    exact (selfDual_map std_selfDual hγ _).1 hx _ hy
  · intro hx
    refine mem_of_forall_prime Λ.L.toAddSubgroup _ fun p hp => ?_
    obtain ⟨γ, hγ, -, h2⟩ := h p hp
    obtain ⟨k, hk, h3⟩ := exists_uniform hp ((Lat.std E n).map γ).fg h2
    have : k • x ∈ ((Lat.std E n).map γ).L := (selfDual_map std_selfDual hγ _).2 fun y hy => by
      have e : stdForm (k • x) y = stdForm x (k • y) := by
        have e1 := stdForm_nsmul k 1 x y
        have e2 := stdForm_nsmul 1 k x y
        rw [one_smul, mul_one] at e1
        rw [one_smul, one_mul] at e2
        rw [e1, e2]
      rw [e]
      exact hx _ (h3 y hy)
    refine ⟨k * k, fun hd => (hp.dvd_mul.1 hd).elim hk hk, ?_⟩
    rw [mul_smul]
    exact h3 _ this

theorem exists_iff (n bad : ℕ) :
    (∀ Λ : GenLat E n, Λ.Unimod → Λ.TrivAt bad →
      ∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) ↔
    ∀ Λ : Lat E n, Λ.SelfDual → Λ.StdAt bad → ∃ β : c.F, IsBeLat Dw c Λ β := by
  constructor
  · intro h Λ h1 h2
    exact (h _ ((unimod_iff Λ).2 h1) ((trivAt_iff Λ bad).2 h2)).imp fun β => (beta_iff Dw c Λ β).1
  · intro h Γ h1 h2
    obtain ⟨Λ, rfl⟩ : ∃ Λ : Lat E n, toGen Λ = Γ := ⟨latEquiv.symm ⟨Γ, isLat_of_unimod Γ h1⟩, rfl⟩
    exact (h Λ ((unimod_iff Λ).1 h1) ((trivAt_iff Λ bad).1 h2)).imp fun β => (beta_iff Dw c Λ β).2

theorem betaExists_iff (n bad : ℕ) : BetaExists (Dw := Dw) c n bad ↔
    (ReflexLe Dw c → ∀ Λ : Lat E n, Λ.SelfDual → Λ.StdAt bad → ∃ β : c.F, IsBeLat Dw c Λ β) :=
  imp_congr (kPsiIn_iff Dw c) (exists_iff Dw c n bad)

theorem stdAt_one (Λ : Lat E n) : Λ.StdAt 1 := fun _ hp hd => absurd hd hp.not_dvd_one

theorem beExists_of_betaExists (h : ∀ n, BetaExists (Dw := Dw) c n 1) : BeExists Dw c :=
  fun hB n Λ hΛ => (betaExists_iff Dw c n 1).1 (h n) (reflexLe_of_basis Dw c hB) Λ (selfDual_of_inGenus hΛ)
    (stdAt_one Λ)

theorem beExists_iff (hG : GenusIffSelfDual H) : BeExists Dw c ↔
    (ReflexBasis Dw c → ∀ (n bad : ℕ) (Λ : GenLat E n), Λ.Unimod → Λ.TrivAt bad →
      ∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) := by
  refine imp_congr_right fun _ => forall_congr' fun n => ?_
  simp only [exists_iff]
  exact ⟨fun h _ Λ h1 _ => h Λ ((hG n Λ).2 h1), fun h Λ h1 => h 1 Λ ((hG n Λ).1 h1) (stdAt_one Λ)⟩

theorem typings_agree (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (c : Coeff l) :
    (∀ (n : ℕ) (Λ : Lat E n),
      Submodule.span (𝓞 E) (detSet (toGen Λ).Ln) = latIdeal Λ • Submodule.span (𝓞 E) (detSet (toGen Λ).La) ∧
      ((toGen Λ).Ln.toAddSubgroup.addSubgroupOf (toGen Λ).La.toAddSubgroup).index = Ideal.absNorm (latIdeal Λ) ∧
      (∀ τ, idealAt c (toGen Λ).Ln τ =
        IsLocalization.coeSubmodule c.F ((latIdeal Λ).map (RingOfIntegers.mapRingHom (embF c τ))) *
          idealAt c (toGen Λ).La τ) ∧
      (∀ β, BetaIs (Dw := Dw) c (toGen Λ) β ↔
        ∃ b : 𝓞 c.F, (b : c.F) = β ∧ Ideal.span {b} = reflexIdeal Dw c (latIdeal Λ)) ∧
      (∀ β, BetaAbs (Dw := Dw) c (toGen Λ) β ↔
        ∀ s : c.F →+* ℂ, ‖s β‖ ^ 2 = (Ideal.absNorm (latIdeal Λ) : ℝ) ^ (Dw.p + Dw.q)) ∧
      (∀ β, (β ≠ 0 ∧ BetaIs (Dw := Dw) c (toGen Λ) β ∧ BetaAbs (Dw := Dw) c (toGen Λ) β) ↔ IsBeLat Dw c Λ β) ∧
      (∀ hK : ReflexLe Dw c, ∃ ζ : c.F, IsOfFinOrder ζ ∧ betaH (Dw := Dw) c (toGen Λ) = ζ * be hK Λ) ∧
      (∀ (n' : ℕ) (Λ' : Lat E n'), latIdeal Λ = latIdeal Λ' →
        betaH (Dw := Dw) c (toGen Λ) = betaH (Dw := Dw) c (toGen Λ')) ∧
      (Λ.InGenus → (toGen Λ).Unimod)) ∧
    (KPsiIn (Dw := Dw) c ↔ ReflexLe Dw c) ∧
    (KPsiIn (Dw := Dw) c ↔ ReflexRoots Dw c) ∧
    (ReflexBasis Dw c → KPsiIn (Dw := Dw) c) ∧
    (∀ n bad, BetaExists (Dw := Dw) c n bad ↔
      (ReflexLe Dw c → ∀ Λ : Lat E n, Λ.SelfDual → Λ.StdAt bad → ∃ β : c.F, IsBeLat Dw c Λ β)) ∧
    ((∀ n, BetaExists (Dw := Dw) c n 1) → BeExists Dw c) ∧
    (GenusIffSelfDual H → (BeExists Dw c ↔
      (ReflexBasis Dw c → ∀ (n bad : ℕ) (Λ : GenLat E n), Λ.Unimod → Λ.TrivAt bad →
        ∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β))) :=
  ⟨fun _ Λ => ⟨by rw [ln_eq]; exact detSpan_inter Λ, by rw [ln_eq]; exact (absNorm_latIdeal Λ).symm,
      fun τ => by rw [ln_eq]; exact idealAt_inter c Λ τ, betaIs_iff Dw c Λ, betaAbs_iff Dw c Λ, beta_iff Dw c Λ,
      fun hK => betaH_eq Dw c hK Λ, fun _ _ h => betaH_congr Dw c h,
      fun h => (unimod_iff Λ).2 (selfDual_of_inGenus h)⟩,
    kPsiIn_iff Dw c, (kPsiIn_iff Dw c).trans (reflexRoots_iff Dw c).symm,
    fun h => (kPsiIn_iff Dw c).2 (reflexLe_of_basis Dw c h), betaExists_iff Dw c, beExists_of_betaExists Dw c,
    beExists_iff Dw c⟩

end GlobalTheory.LatticeBetaCompare
