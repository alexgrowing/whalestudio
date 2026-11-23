import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountableCharts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationsSamePointDifferByIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfCountableHolomorphicImagesCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfInjOnDifferentiableOnComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMapLiftsLocallyToPeriodFamiliesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.DimEq

variable {O : Type} [Ring O] {bar : O → O} {g : ℕ}

def trP {D D'' : PLat O bar} (M : Matrix (Fin g) (Fin g) ℂ) (P : D''.La →+ (Fin g → ℂ)) (w : D.La ≃ₗ[O] D''.La) :
    D.La →+ (Fin g → ℂ) where
  toFun x := M *ᵥ P (w x)
  map_zero' := by simp
  map_add' x y := by simp [Matrix.mulVec_add]

theorem mixedTracePairing_apply {D D'' : PLat O bar} (M : Matrix (Fin g) (Fin g) ℂ) (P : D''.La →+ (Fin g → ℂ)) (w : D.La ≃ₗ[O] D''.La)
    (x : D.La) : trP M P w x = M *ᵥ P (w x) := rfl

theorem hermForm_conj (N Hm : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℂ) :
    hermForm (Nᵀ * Hm * Nᴴᵀ) u v = hermForm Hm (N *ᵥ u) (N *ᵥ v) := by
  unfold hermForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.star_mulVec, Matrix.mulVec_transpose]

theorem comm_of_rel {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {D D'' : PLat O bar} {P : D.La →+ (Fin g → ℂ)}
    {P'' : D''.La →+ (Fin g → ℂ)} (hP : IsPeriod D ρ P) (hP'' : IsPeriod D'' ρ P'') (w : D.La ≃ₗ[O] D''.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hw : ∀ x, P'' (w x) = h (P x)) (a : O) (z : Fin g → ℂ) :
    h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
  have key : ((h.toLinearMap ∘ₗ Matrix.mulVecLin (ρ a)).restrictScalars ℝ) =
      ((Matrix.mulVecLin (ρ a) ∘ₗ h.toLinearMap).restrictScalars ℝ) := by
    apply LinearMap.ext_on_range hP.2.2.2.1
    intro x
    simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
    rw [← hP.1 a x, ← hw (a • x), ← hw x, map_smul, hP''.1]
  exact LinearMap.congr_fun key z

theorem countable_equiv (D D'' : PLat O bar) : Countable (D.La ≃ₗ[O] D''.La) := by
  let b := Module.Free.chooseBasis ℤ D.La
  let b'' := Module.Free.chooseBasis ℤ D''.La
  haveI : Countable D''.La := Function.Injective.countable b''.equivFun.injective
  apply Function.Injective.countable (f := fun w : D.La ≃ₗ[O] D''.La => fun i => w (b i))
  intro w₁ w₂ hw
  have : (w₁.toLinearMap.toAddMonoidHom.toIntLinearMap) = (w₂.toLinearMap.toAddMonoidHom.toIntLinearMap) :=
    b.ext fun i => congrFun hw i
  ext x
  exact LinearMap.congr_fun this x

end GlobalTheory.DimEq

namespace GlobalTheory.DimEq

variable {O : Type} [Ring O] {bar : O → O} {g : ℕ}

theorem isPeriod_trP {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {D D'' : PLat O bar} {P : D''.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D'' ρ P) (w : D.La ≃ₗ[O] D''.La) (hw : IsIsom D D'' w) (M : Matrix (Fin g) (Fin g) ℂ)
    (hM : IsUnit M.det) (hMc : ∀ a, M * ρ a = ρ a * M) : IsPeriod D ρ (trP M P w) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hHm, hpos, him⟩ := hP
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hNinj : Function.Injective (fun v : Fin g → ℂ => M⁻¹ *ᵥ v) := by
    intro u v huv
    have := congrArg (fun x => M *ᵥ x) huv
    simpa [Matrix.mulVec_mulVec, hMN] using this
  have hMinj : Function.Injective (fun v : Fin g → ℂ => M *ᵥ v) := by
    intro u v huv
    have := congrArg (fun x => M⁻¹ *ᵥ x) huv
    simpa [Matrix.mulVec_mulVec, hNM] using this
  let φ : (Fin g → ℂ) ≃ₜ (Fin g → ℂ) :=
    { toFun := fun v => M⁻¹ *ᵥ v
      invFun := fun v => M *ᵥ v
      left_inv := fun v => by simp [Matrix.mulVec_mulVec, hMN]
      right_inv := fun v => by simp [Matrix.mulVec_mulVec, hNM]
      continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
      continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id }
  have hrange : Set.range (trP M P w) = (fun v => M *ᵥ v) '' Set.range P := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨P (w x), ⟨w x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨w.symm u, by simp [mixedTracePairing_apply]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a x
    rw [mixedTracePairing_apply, mixedTracePairing_apply, map_smul, hlin, Matrix.mulVec_mulVec, hMc, ← Matrix.mulVec_mulVec]
  · intro x y hxy
    exact w.injective (hinj (hMinj hxy))
  · have hmem : ∀ v, v ∈ (trP M P w).range ↔ φ v ∈ P.range := by
      intro v
      simp only [AddMonoidHom.mem_range]
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨w x, by simp [φ, mixedTracePairing_apply, Matrix.mulVec_mulVec, hNM]⟩
      · rintro ⟨u, hu⟩
        refine ⟨w.symm u, ?_⟩
        rw [mixedTracePairing_apply, LinearEquiv.apply_symm_apply, hu]
        simp [φ, Matrix.mulVec_mulVec, hMN]
    let e := φ.subtype hmem
    exact e.isEmbedding.discreteTopology
  · let Lr : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := (Matrix.mulVecLin M).restrictScalars ℝ
    have hLr : Set.range (trP M P w) = Lr '' Set.range P := hrange
    rw [hLr, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    intro v
    exact ⟨M⁻¹ *ᵥ v, by simp [Lr, Matrix.mulVec_mulVec, hMN]⟩
  · refine ⟨(M⁻¹)ᵀ * Hm * (M⁻¹)ᴴᵀ, ?_, ?_, ?_⟩
    · unfold Matrix.IsHermitian
      have e1 : ((M⁻¹)ᴴᵀ)ᴴ = (M⁻¹)ᵀ := by ext i j; simp
      have e2 : ((M⁻¹)ᵀ)ᴴ = (M⁻¹)ᴴᵀ := by ext i j; simp
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hHm.eq, e1, e2, Matrix.mul_assoc]
    · intro z hz
      rw [hermForm_conj]
      apply hpos
      intro h0
      apply hz
      apply hNinj
      simpa using h0
    · intro x y
      rw [hermForm_conj, mixedTracePairing_apply, mixedTracePairing_apply]
      simp only [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
      rw [him, hw x y]

theorem isOpen_near {D : PLat O bar} {m : ℕ} (B : Set (Fin m → ℂ)) (hB : IsOpen B)
    (f : (Fin m → ℂ) → D.La → (Fin g → ℂ)) (hf : ∀ x, ContinuousOn (fun b => f b x) B) (s : Finset D.La)
    (P₀ : D.La → (Fin g → ℂ)) (ε : ℝ) : IsOpen {b | b ∈ B ∧ ∀ x ∈ s, ‖f b x - P₀ x‖ < ε} := by
  have : {b | b ∈ B ∧ ∀ x ∈ s, ‖f b x - P₀ x‖ < ε} =
      B ∩ ⋂ x ∈ s, (B ∩ (fun b => f b x) ⁻¹' Metric.ball (P₀ x) ε) := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
    constructor
    · rintro ⟨hb, h⟩
      exact ⟨hb, fun x hx => ⟨hb, h x hx⟩⟩
    · rintro ⟨hb, h⟩
      exact ⟨hb, fun x hx => (h x hx).2⟩
  rw [this]
  exact hB.inter (isOpen_biInter_finset fun x _ => (hf x).isOpen_inter_preimage hB Metric.isOpen_ball)

end GlobalTheory.DimEq

namespace GlobalTheory.DimEq

theorem dim_eq : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d d' : ℕ) (D' : PLat O bar) (t : Λ → D'.La), 0 < N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → C D' t → (∃ P, IsPeriod D' ρ P) → PerCoord D' ρ d' → d = d' := by
  intro O _ bar g ρ Λ F N C d d' D' t hN heta hd hqc hF hC hPex hPC
  obtain ⟨P₀, hP₀⟩ := hPex
  have hlft : LocallyOfFiniteType F.s := by
    haveI := hd
    haveI : Smooth F.s := SmoothOfRelativeDimension.smooth d F.s
    infer_instance
  let Qc : Set (Fin d → ℂ) → ((Fin d → ℂ) → (Sp ℂ ⟶ F.X)) → Prop := fun B y =>
    ∃ (D'' : PLat O bar) (t'' : Λ → D''.La) (P : (Fin d → ℂ) → (D''.La →+ (Fin g → ℂ)))
      (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ F.A)),
      IsHolPeriods D'' ρ B P ∧ ∀ b ∈ B, UnifAt F (RingHom.id ℂ) ρ N D'' t'' (P b) (y b) (e b)
  obtain ⟨K, hK, B, y, hch, hcov⟩ := GlobalTheory.CountableCharts.exists_countable_charts F.X F.s d hd hqc Qc (by
    intro B y b₀ hB hb₀ hys hyh
    obtain ⟨D'', t'', P'', e'', -, hU⟩ := hF.pts (y b₀) (hys b₀ hb₀)
    obtain ⟨B', P, e, hB', hb₀', hsub, -, hhol, -, hU'⟩ :=
      GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies O bar g ρ Λ F N D'' t'' d B y b₀ P'' e'' hN heta hlft hB hb₀ hys hyh hU
    exact ⟨B', hB', hb₀', hsub, D'', t'', P, e, hhol, hU'⟩)
  choose Dl tl Pl el hPl hUl using fun i => (hch i).2.2.2.2
  obtain ⟨BZ, Q, Z, s, ε, hBZ, hε, hQ, hZ0, hQZ0, hZQ, hnear, hinv, hZhol⟩ := hPC P₀ hP₀
  apply le_antisymm
  ·
    obtain ⟨y₀, e₀, hU₀⟩ := hF.occ D' t P₀ hC hP₀
    obtain ⟨i, c₀, hc₀, hyc₀⟩ := hcov y₀ hU₀.1
    subst hyc₀
    obtain ⟨B', P, e, hB', hc₀', hsub, hPc₀, hhol, -, hU'⟩ :=
      GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies O bar g ρ Λ F N D' t d (B i) (y i) c₀ P₀ e₀ hN heta hlft (hch i).1 hc₀ (hch i).2.1
        (hch i).2.2.1 hU₀
    let U := {b | b ∈ B' ∧ ∀ x ∈ s, ‖P b x - P₀ x‖ < ε}
    have hUo : IsOpen U := isOpen_near B' hB' (fun b x => P b x) (fun x => (hhol.2 x).continuousOn) s P₀ ε
    have hc₀U : c₀ ∈ U := ⟨hc₀', fun x _ => by simp [hPc₀, hε]⟩
    have hholU : IsHolPeriods D' ρ U P := ⟨fun b hb => hhol.1 b hb.1, fun x => (hhol.2 x).mono fun b hb => hb.1⟩
    refine GlobalTheory.T.le_of_injOn_differentiableOn_complex d d' U (fun b => Z (P b)) hUo ⟨c₀, hc₀U⟩ (hZhol d U P hUo hholU fun b hb => hb.2) ?_
    intro b hb b' hb' heq
    have heq' : Z (P b) = Z (P b') := heq
    obtain ⟨-, h1, hh1⟩ := hnear (P b) (hhol.1 b hb.1) hb.2
    obtain ⟨-, h2, hh2⟩ := hnear (P b') (hhol.1 b' hb'.1) hb'.2
    have hyy := hF.sep D' D' t t (P b) (P b') (y i b) (y i b') (e b) (e b') (hU' b hb.1) (hU' b' hb'.1)
      (LinearEquiv.refl O D'.La) (h1.symm.trans h2) ⟨fun x y => rfl, fun a => ⟨0, by simp⟩⟩ (fun x => by
        rw [LinearEquiv.refl_apply, hh2 x, ← heq', LinearEquiv.trans_apply, hh1 x, LinearEquiv.symm_apply_apply])
    exact (hch i).2.2.2.1 (hsub hb.1) (hsub hb'.1) hyy
  ·
    haveI : SecondCountableTopology (Matrix (Fin g) (Fin g) ℂ) :=
      inferInstanceAs (SecondCountableTopology (Fin g → Fin g → ℂ))
    let T : Set (Matrix (Fin g) (Fin g) ℂ) := {M | IsUnit M.det ∧ ∀ a, M * ρ a = ρ a * M}
    obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense T
    haveI : Countable S := hSc.to_subtype
    haveI : ∀ i, Countable {w : D'.La ≃ₗ[O] (Dl i).La // IsIsom D' (Dl i) w} := fun i =>
      haveI := countable_equiv D' (Dl i); inferInstance
    let J := Σ i : K, {w : D'.La ≃ₗ[O] (Dl i).La // IsIsom D' (Dl i) w} × S
    let per : J → (Fin d → ℂ) → (D'.La →+ (Fin g → ℂ)) := fun j c => trP (j.2.2 : T).1 (Pl j.1 c) j.2.1.1
    let U : J → Set (Fin d → ℂ) := fun j => {c | c ∈ B j.1 ∧ ∀ x ∈ s, ‖per j c x - P₀ x‖ < ε}
    have hdiff : ∀ j x, DifferentiableOn ℂ (fun c => per j c x) (B j.1) := by
      intro j x
      have h1 := (hPl j.1).2 (j.2.1.1 x)
      exact ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin (j.2.2 : T).1)).differentiable.comp_differentiableOn h1)
    have hUo : ∀ j, IsOpen (U j) := fun j =>
      isOpen_near (B j.1) (hch j.1).1 (fun c x => per j c x) (fun x => (hdiff j x).continuousOn) s P₀ ε
    have hperU : ∀ j, IsHolPeriods D' ρ (U j) (per j) := fun j =>
      ⟨fun c hc => isPeriod_trP ((hPl j.1).1 c hc.1) j.2.1.1 j.2.1.2 _ (j.2.2 : T).2.1 (j.2.2 : T).2.2,
        fun x => (hdiff j x).mono fun c hc => hc.1⟩
    let W := {b | b ∈ BZ ∧ ∀ x ∈ s, ‖Q b x - P₀ x‖ < ε}
    have hWo : IsOpen W := isOpen_near BZ hBZ (fun b x => Q b x) (fun x => (hQ.2 x).continuousOn) s P₀ ε
    have hWne : W.Nonempty := ⟨Z P₀, hZ0, fun x _ => by simp [hQZ0, hε]⟩
    refine GlobalTheory.T.le_of_countable_holomorphic_images_cover_open d d' J U (fun j c => Z (per j c)) W hUo
      (fun j => hZhol d (U j) (per j) (hUo j) (hperU j) fun c hc => hc.2) hWo hWne ?_
    intro b hb
    have hQb := hQ.1 b hb.1
    obtain ⟨yb, eb, hUb⟩ := hF.occ D' t (Q b) hC hQb
    obtain ⟨i, c, hc, hyc⟩ := hcov yb hUb.1
    subst hyc
    obtain ⟨w, h, hw, hwP, -⟩ := GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' (Dl i) t (tl i) (Q b) (Pl i c)
      (y i c) eb (el i c) hN hUb (hUl i c hc)
    have hPic := (hPl i).1 c hc
    let M₀ : Matrix (Fin g) (Fin g) ℂ := LinearMap.toMatrix' (h.symm : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    have hM₀v : ∀ v, M₀ *ᵥ v = h.symm v := fun v => by simp [M₀, LinearMap.toMatrix'_mulVec]
    have hM₀T : M₀ ∈ T := by
      refine ⟨?_, fun a => ?_⟩
      · let M₁ : Matrix (Fin g) (Fin g) ℂ := LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
        have : M₀ * M₁ = 1 := by
          apply Matrix.toLin'.injective
          apply LinearMap.ext
          intro v
          simp [M₀, M₁, Matrix.toLin'_mul, LinearMap.toMatrix'_mulVec]
        exact Matrix.isUnit_det_of_right_inverse this
      · apply Matrix.toLin'.injective
        apply LinearMap.ext
        intro v
        simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hM₀v]
        apply h.injective
        rw [LinearEquiv.apply_symm_apply, comm_of_rel hQb hPic w h hwP a, LinearEquiv.apply_symm_apply]
    let V : Set T := {M | ∀ x ∈ s, ‖(M : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pl i c (w x) - P₀ x‖ < ε}
    have hVo : IsOpen V := by
      have : V = ⋂ x ∈ s, {M : T | ‖(M : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pl i c (w x) - P₀ x‖ < ε} := by
        ext M; simp [V]
      rw [this]
      exact isOpen_biInter_finset fun x _ => isOpen_lt
        ((Continuous.matrix_mulVec continuous_subtype_val continuous_const).sub continuous_const).norm continuous_const
    have hM₀V : (⟨M₀, hM₀T⟩ : T) ∈ V := fun x hx => by
      show ‖M₀ *ᵥ Pl i c (w x) - P₀ x‖ < ε
      rw [hM₀v, hwP, LinearEquiv.symm_apply_apply]
      exact hb.2 x hx
    obtain ⟨M, hMS, hMV⟩ := hSd.exists_mem_open hVo ⟨_, hM₀V⟩
    let j : J := ⟨i, ⟨w, hw.1⟩, ⟨M, hMS⟩⟩
    refine Set.mem_iUnion.2 ⟨j, c, ⟨hc, hMV⟩, ?_⟩
    have hperj : IsPeriod D' ρ (per j c) := (hperU j).1 c ⟨hc, hMV⟩
    haveI : Invertible (M : Matrix (Fin g) (Fin g) ℂ) := Matrix.invertibleOfIsUnitDet _ M.2.1
    let hM : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := Matrix.toLinearEquiv' (M : Matrix (Fin g) (Fin g) ℂ) inferInstance
    have hZ : Z (per j c) = Z (Q b) := hinv (Q b) (per j c) hQb hperj hb.2 hMV (h.trans hM) (fun x => by
      show (M : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pl i c (w x) = _
      rw [hwP]
      rfl)
    show Z (per j c) = b
    rw [hZ, hZQ b hb.1 hb.2]

end GlobalTheory.DimEq
