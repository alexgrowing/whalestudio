import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.PerFrLact
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionShortThetaSeriesRootOfUnityMul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarkedLatticeIsometryDoubleCosetMove
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicElementOfMarkedComponentLattice
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameFreeFiniteOrderRuleConstPeriodSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvarianceStatement
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg

noncomputable section

namespace GlobalTheory.TwistTie

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Matrix
open GlobalTheory.ShortMove GlobalTheory.ShortMoveIso

theorem perFr_of_unitary {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X X' : Data E r)
    (hΨ : ∀ τ, τ ∈ X'.Ψ ↔ τ ∈ X.Ψ) (hG : X'.Gm = X.Gm) (hp : X'.p0 = X.p0) {x : Frame X.Ψ r} {x' : Frame X'.Ψ r}
    {γ : GL (Fin r) E} (hγ : ∀ u v, herm X.Gm (γ.1 *ᵥ u) (γ.1 *ᵥ v) = herm X.Gm u v)
    (hm : ∀ τ h h', mat x' ⟨τ, h'⟩ = γ.1.map τ * mat x ⟨τ, h⟩) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X' x' (γ.1 *ᵥ v) τ i = perFr X x v τ i := by
  have hemb : ∀ τ' : E →+* ℂ, Data.emb τ' (γ.1 *ᵥ v) = (γ.1.map τ') *ᵥ Data.emb τ' v := fun τ' => by
    funext a
    simp [Data.emb, Matrix.mulVec, dotProduct, map_sum]
  have hdetγ : ∀ τ' : E →+* ℂ, IsUnit ((γ.1.map τ').det) := fun τ' => by
    have hd : (γ.1.map τ').det = τ' γ.1.det := (RingHom.map_det τ' _).symm
    rw [hd]
    exact (Matrix.isUnits_det_units γ).map τ'
  unfold perFr
  rw [hp, hG]
  by_cases h1 : τ ∈ X.Ψ
  · rw [dif_pos h1, dif_pos ((hΨ τ).2 h1)]
    split_ifs with h2
    · rw [hm τ h1, hemb, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec (Data.emb τ v) (γ.1.map τ)⁻¹, Matrix.nonsing_inv_mul _ (hdetγ τ), Matrix.one_mulVec]
    · rfl
  rw [dif_neg h1, dif_neg (mt (hΨ τ).1 h1)]
  by_cases h3 : conjEmb τ ∈ X.Ψ
  · rw [dif_pos h3, dif_pos ((hΨ _).2 h3)]
    split_ifs with h4
    · have hu : (γ.1.map (conjEmb τ))ᵀ * X.Gm.map (conjEmb τ) *
          (γ.1.map (conjEmb τ)).map (starRingEnd ℂ) = X.Gm.map (conjEmb τ) := by
        have e := congrArg (fun M => M.map (conjEmb τ))
          (ustab_mat (Λ := ⊤) (γ := γ) ⟨hγ, fun _ => Iff.rfl⟩)
        simp only [Matrix.map_mul, Matrix.transpose_map] at e
        have hc : (γ.1.map (conjEmb τ)).map (starRingEnd ℂ) = (γ.1.map cc).map (conjEmb τ) := by
          ext a b
          simp [cc]
        rw [hc]
        exact e
      have hcol : ∀ j, col (γ.1.map (conjEmb τ) * mat x ⟨conjEmb τ, h3⟩) j =
          (γ.1.map (conjEmb τ)) *ᵥ col (mat x ⟨conjEmb τ, h3⟩) j := fun j => by
        funext a
        simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      have e1 : ∀ (A : Matrix (Fin r) (Fin r) ℂ) (c Y : Fin r → ℂ), (A *ᵥ c) ⬝ᵥ Y = c ⬝ᵥ (Aᵀ *ᵥ Y) :=
        fun A c Y => by rw [Matrix.dotProduct_mulVec c Aᵀ Y, Matrix.vecMul_transpose]
      rw [hm _ h3, hcol, hemb, hermC_eq, hermC_eq, star_mulVec', e1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu]
    · rfl
  rw [dif_neg h3, dif_neg (mt (hΨ _).1 h3)]

theorem point_eq_of_isometry {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (hr : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H Dw.p Dw.q ty) (hA : l.A = 1) {k k' : Fin F.n} (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k').La)
    (hEF : ∀ a b, (F.Di k').EF (gam a) (gam b) = (F.Di k).EF a b)
    (hM : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F.t k' a + l.M • x)
    {P : (F.Di k).La →+ (Fin g → ℂ)} {P' : (F.Di k').La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di k) ty P)
    (hP' : IsPeriod (F.Di k') ty P') (h : ∀ a, P' (gam a) = P a) : F.u k P = F.u k' P' :=
  (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1 E H Dw l Xo σ' g ty
    hr hσ hty (F.Di k) (F.Di k')
    (F.t k) (F.t k') P P' (F.u k P) (F.u k' P') (F.ex k P) (F.ex k' P')
    ⟨F.over_σ k P hP, hP, ⟨F.ex_add k P hP, F.ex_onto k P hP, GlobalTheory.ClassUniq.isHolTo_ex F k P hP,
      (F.ex_diff k P hP).1, (F.ex_diff k P hP).2⟩, F.ex_ker k P hP, F.ex_lin k P hP, F.ex_weil k P hP,
      F.ex_eta k P hP, F.ex_etaA k P hP⟩
    ⟨F.over_σ k' P' hP', hP', ⟨F.ex_add k' P' hP', F.ex_onto k' P' hP', GlobalTheory.ClassUniq.isHolTo_ex F k' P' hP',
      (F.ex_diff k' P' hP').1, (F.ex_diff k' P' hP').2⟩, F.ex_ker k' P' hP', F.ex_lin k' P' hP',
      F.ex_weil k' P' hP', F.ex_eta k' P' hP', F.ex_etaA k' P' hP'⟩).2
    ⟨gam, LinearEquiv.refl ℂ _, hEF, hM,
      fun a => ⟨gam (F.t _ a) - F.t _ a, by rw [hA, one_smul, add_sub_cancel]⟩, h⟩

set_option maxHeartbeats 1000000 in

theorem marked_isometry_half {D : D7} (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (X X' : Data D.host.E V.rank) (A A' : Datum H) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ)
    (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La) (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La)
    (h γ κ : GA D V) (hW : ModelW V rfl X) (hW' : ModelW V rfl X')
    (hE : ∀ a b, ((A.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin V.rank → D.host.E) (φ b)))
    (hE' : ∀ a b, ((A'.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (δ : GL (Fin V.rank) D.host.E)
    (hδu : ∀ u v, herm (-V.gram.transpose) (δ.1 *ᵥ u) (δ.1 *ᵥ v) = herm (-V.gram.transpose) u v)
    (hδf : ∀ v, (finHom V γ).1 *ᵥ finVec V v = finVec V (δ.1 *ᵥ v)) (hκ : latGHat V κ = latGHat V 1)
    (hs : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
      (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s a)) + l.M • w)
    (hm : Marked V rfl io l X.Λ (fun a => (φ (t a) : Fin V.rank → D.host.E)) h)
    (hm' : Marked V rfl io l X'.Λ (fun a => (φ' (t' a) : Fin V.rank → D.host.E)) (γ * h * κ)) :
    ∃ gam : A.La ≃ₗ[𝓞 D.host.E] A'.La, (∀ a b, A'.EF (gam a) (gam b) = A.EF a b) ∧
      (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ x, gam (t (s a)) = t' a + l.M • x) ∧
      ∀ a, (φ' (gam a) : Fin V.rank → D.host.E) = δ.1 *ᵥ (φ a : Fin V.rank → D.host.E) := by
  obtain ⟨hΛ, hm⟩ := hm
  obtain ⟨hΛ', hm'⟩ := hm'
  obtain ⟨ht1, ht2⟩ := transport (finHom V) (latGHat V) (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) l.M γ h κ hκ
  have hmem : ∀ v, v ∈ X.Λ ↔ finVec V v ∈ latGHat V h := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V h).1, ← SetLike.mem_coe, hΛ]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hmem' : ∀ v, v ∈ X'.Λ ↔ finVec V v ∈ latGHat V (γ * h * κ) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hΛ']
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ X.Λ ↔ δ.1 *ᵥ v ∈ X'.Λ := fun v => by
    rw [hmem, hmem', ht1, hδf]
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hri : ∀ v, δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, (δ⁻¹).1 *ᵥ (δ.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let ψ : X.Λ ≃ₗ[𝓞 D.host.E] X'.Λ :=
    { toFun := fun v => ⟨δ.1 *ᵥ v.1, (hlat _).1 v.2⟩
      invFun := fun v => ⟨(δ⁻¹).1 *ᵥ v.1, (hlat _).2 (by rw [hri]; exact v.2)⟩
      map_add' := fun u v => Subtype.ext (Matrix.mulVec_add δ.1 u.1 v.1)
      map_smul' := fun a v => Subtype.ext (Matrix.mulVec_smul δ.1 a v.1)
      left_inv := fun v => Subtype.ext (hli _)
      right_inv := fun v => Subtype.ext (hri _) }
  let gam : A.La ≃ₗ[𝓞 D.host.E] A'.La := φ.trans (ψ.trans φ'.symm)
  have hgam : ∀ a, (φ' (gam a) : Fin V.rank → D.host.E) = δ.1 *ᵥ (φ a : Fin V.rank → D.host.E) := by
    intro a
    simp [gam, ψ]
  have hG : X.Gm = -V.gram.transpose := hW.1
  have hG' : X'.Gm = -V.gram.transpose := hW'.1
  have hξ : X'.ξ0 = X.ξ0 := hW'.2.trans hW.2.symm
  refine ⟨gam, fun a b => ?_, fun a ha => ?_, hgam⟩
  · have h1 := hE' (gam a) (gam b)
    rw [hgam, hgam, hG', hξ, hδu, ← hG, ← hE a b] at h1
    exact_mod_cast h1
  · obtain ⟨z, hz, e⟩ := ht2 (finVec V (φ (t (s a)) : Fin V.rank → D.host.E))
      (finVec V (φ' (t' a) : Fin V.rank → D.host.E)) _ _ (hs a ha) (hm _ (map_mem_half _ s a ha)) (hm' a ha)
    obtain ⟨w, hw, e'⟩ := GlobalTheory.MarkCoset.finVec_div V l.M hM0 (δ.1 *ᵥ (φ (t (s a)) : Fin V.rank → D.host.E) -
      (φ' (t' a) : Fin V.rank → D.host.E)) z (by
        rw [← e, hδf]
        funext i
        exact TensorProduct.tmul_sub _ _ _)
    refine ⟨φ'.symm ⟨w, (hmem' w).2 (hw ▸ hz)⟩, φ'.injective (Subtype.ext ?_)⟩
    rw [hgam, sub_eq_iff_eq_add'.1 e', map_add, map_nsmul, LinearEquiv.apply_symm_apply]
    rfl

section Dict

variable {D : D7} (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}
  (U : Unf Xo c σ V.rank) (dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank)
  (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
  (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
  (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ)

set_option maxHeartbeats 1000000 in

theorem exists_dict_over (hσ : GoodEmb c σ) (hA : l.A = 1) (hpq : 1 ≤ Dw.p + Dw.q)
    (hU : IsUnf U) (hW : ∀ k, ModelW V rfl (U.X k)) (hD : DictLat U V rfl dict io e F ik φ th x₀)
    (hι : GlobalTheory.Member.IotaOK Dw V io) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀)
    (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) (y : FrPt Xo c (CAt σ)) :
    ∃ h, y.x = (U.un (dict h).1 ⟨(dict h).2, hdom h⟩).x := by
  have hty := (GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e
  obtain ⟨k, x, t, ht⟩ := hU.2.2.1 y
  obtain ⟨h1, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm
  obtain ⟨x₁, b, hb, ho, hx₁⟩ := h1 x.1 x.2
  have hx₁d : x₁ ∈ (U.X k).dom := ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm).2.1 x₁ ho).1
  obtain ⟨t', ht'⟩ := (hU.2.2.2.1 k k x ⟨x₁, hx₁d⟩).2 ⟨1, one_mem _, b, hb, by
    have : lact 1 x.1 = x.1 := funext fun τ => by
      change ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 * mat x.1 τ) = _
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
      rfl
    rw [this, ← hx₁]⟩
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, hL⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hmem : ∀ k (τ : D.host.E →+* ℂ), τ ∈ (U.X k).Ψ ↔ τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
    intro k τ
    rw [(hU.2.1 k).2 τ, hι.rt, hι.rt0]
  have hex : ∀ τ : D.host.E →+* ℂ, ∃ u : Matrix (Fin V.rank) (Fin V.rank) ℂ, ∀ hτ : τ ∈ (U.X k).Ψ,
      uᵀ * (-V.gramᵀ).map τ * u.map (starRingEnd ℂ) = (-V.gramᵀ).map τ ∧ mat x₁ ⟨τ, hτ⟩ = u * x₀ τ := by
    intro τ
    by_cases hτ : τ ∈ (U.X k).Ψ
    · obtain ⟨u, hu⟩ := h4 τ (x₀ τ) (mat x₁ ⟨τ, hτ⟩) (hx₀ k τ hτ) ((ho ⟨τ, hτ⟩).trans (hx₀ k τ hτ).symm)
      rw [hG] at hu
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h' => absurd h' hτ⟩
  choose u hu using hex
  obtain ⟨a, ha, hau⟩ := hL u fun τ hτ => (hu τ ((hmem k τ).2 hτ)).1
  obtain ⟨h₀, hh₀⟩ := GlobalTheory.ShortMove.exists_marked_of_component D V H Dw l Xo _ g _ F hty _ rfl (U.X k) (ik k) (φ k) io
    (hW k) (hD.1.1 k) hι.emb hι.isom
  obtain ⟨a₀, ha₀, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h₀
  have hfin : finHom V (a₀ * f) = finHom V (a * f) := by
    rw [map_mul, map_mul, show finHom V a₀ = 1 from ha₀, show finHom V a = 1 from ha]
  have hh : Marked V rfl io l (U.X k).Λ (fun a => (φ k (F.t (ik k) a) : Fin V.rank → D.host.E)) (a * f) := by
    obtain ⟨e₁, e₂⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.1 _ _ hfin
    unfold Marked at hh₀ ⊢
    rwa [e₁, e₂, hfin] at hh₀
  refine ⟨a * f, ?_⟩
  obtain ⟨γ, hγ, hΛ, hm, hfr⟩ := hD.2 (a * f)
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V γ hγ
  obtain ⟨gam, e₁, t₁, hgam⟩ := marked_isometry_half V l io (U.X k) (U.X (dict (a * f)).1) _ _ (φ k) (φ _) (F.t _) (F.t _)
    LinearMap.id (a * f) γ 1 (hW k) (hW _) (hD.1.1 k) (hD.1.1 _) δ hδu hδf rfl (fun a _ => ⟨0, zero_mem _, by
      rw [map_one, Units.val_one, Matrix.one_mulVec, smul_zero, add_zero]; rfl⟩) hh
    (by rw [mul_one]; exact ⟨hΛ, hm⟩)
  obtain ⟨P, hPe, hP, hy, -⟩ := hD.1.2 k ⟨x₁, hx₁d⟩
  obtain ⟨P', hPe', hP', hy', -⟩ := hD.1.2 (dict (a * f)).1 ⟨_, hdom _⟩
  rw [ht.1, ← ht'.1, hy, hy']
  refine point_eq_of_isometry F hpq hσ hty hA gam e₁ t₁ hP hP' fun v => funext fun j => ?_
  rw [hPe, hPe', hgam]
  refine perFr_of_unitary _ _ (fun τ => by rw [hmem, hmem]) (by rw [hG, hG])
    (by rw [(hU.2.1 _).1, (hU.2.1 _).1]) (by rw [hG]; exact hδu) (fun τ h h' => ?_) _ _ _
  rw [hfr ⟨τ, h'⟩, GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth _ ⟨τ, h'⟩) (hθ τ), (hAr τ).2.1, (hAr τ).2.1,
    (hAr τ).2.2.1 f hf, hδa τ _ (hθ τ), hau τ ((hmem k τ).1 h), (hu τ h).2, Matrix.mul_one, ← Matrix.mul_assoc]
  rfl

set_option maxHeartbeats 1000000 in

theorem value_ratio (hσ : σ = c.F.val.toRingHom) (hA : l.A = 1) (hpq : 1 ≤ Dw.p + Dw.q)
    (hU : IsUnf U) (hW : ∀ k, ModelW V rfl (U.X k)) (hD : DictLat U V rfl dict io e F ik φ th x₀)
    (hι : GlobalTheory.Member.IotaOK Dw V io) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀)
    (f : Rul Xo c) (hf : f ∈ sec Xo c 0 0) (c0 : ℂ) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (N : ℕ) (hN : 0 < N) (hc0 : c0 ^ N = 1)
    (hxN : ∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) ^ N = 1)
    (hval : ∀ h γ : GA D V, MarkBy U V rfl dict io F ik φ h γ → rdU U f (dict h).1 (dict h).2 =
      c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ))
    (hxi : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (s : Sim Dw) (ρ : Xo.X ≅ Xo.X) (hρ : Xo.LevAut s ρ) (κ : GA D V) (hκ : latGHat V κ = latGHat V 1)
    (hκ' : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
      (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s.f l.M a)) + l.M • w)
    (a : c.F) (ha : (a : ℂ) = (xi (Matrix.GeneralLinearGroup.det (finHom V κ)) : ℂˣ))
    (K : Type) [Field K] [Algebra c.F K] (y y' : FrPt Xo c K) (hy : y'.x = y.x ≫ ρ.hom) :
    evR Xo c f y' = algebraMap c.F K a * evR Xo c f y := by
  subst hσ
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  have hc0' : c0 ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hc0; exact zero_ne_one hc0
  have hty := (GlobalTheory.Relab.relab_good _ H l c _ hσ).2.2.2 Dw g e
  have hfree : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x →
      evR Xo c f y' = evR Xo c f y := fun K _ _ _ y y' h => by
    obtain ⟨z, z', hz, -, hz'⟩ := GlobalTheory.Frames.exists_complex_framed_pair _ _ _ _ Xo c K y y'
    have := hz' f hf 1 (by
      rw [map_one, one_mul]
      exact GlobalTheory.WeightZeroValue.evR_eq_of_same_point hf (by simpa using hz (𝟙 _) (by simpa using h)))
    rwa [map_one, one_mul] at this
  have val₀ : ∀ h : GA D V, ∃ hx : (dict h).2 ∈ (U.X (dict h).1).dom, toC (evR Xo c f (U.un _ ⟨_, hx⟩)) =
      c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V h)) : ℂˣ) : ℂ) := by
    intro h
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    have hv := hval h γ ⟨hγ, hΛ, hm⟩
    rw [map_mul, map_mul, map_mul, hxi γ hγ, one_mul] at hv
    obtain ⟨hx, ex⟩ := rdU_eq U f _ _ (hv ▸ mul_ne_zero hc0' (Units.ne_zero _))
    exact ⟨hx, ex.symm.trans hv⟩
  choose hdom val₀ using val₀
  have hroot : ∃ N : ℕ, 0 < N ∧ ∀ y : FrPt Xo c (CAt c.F.val.toRingHom), evR Xo c f y ^ N = 1 := ⟨N, hN, fun y => by
    obtain ⟨h, hh⟩ := exists_dict_over V U dict io e F ik φ th x₀ hσ hA hpq hU hW hD hι hth hx₀ hdom y
    rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hf hh]
    change toC (evR Xo c f _) ^ N = (1 : ℂ)
    rw [val₀, mul_pow, hc0, ← Units.val_pow_eq_pow_val, hxN, Units.val_one, one_mul]⟩
  have val : ∀ (h : GA D V) (i : Fin F.n) P (y : FrPt Xo c (CAt c.F.val.toRingHom)), i = ik (dict h).1 →
      IsPeriod (F.Di i) (fun j => relab c c.F.val.toRingHom (e j).1) P → y.x = F.u i P →
        toC (evR Xo c f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V h)) : ℂˣ) : ℂ) := by
    rintro h _ P y rfl hP hy
    obtain ⟨P₀, -, hP₀, hy₀, -⟩ := hD.1.2 (dict h).1 ⟨_, hdom h⟩
    rw [← val₀, GlobalTheory.FiniteOrderConst.const_on_period_space _ H Dw l Xo c _ f hf hfree hroot g _ F hty _ P P₀ y _ hP hP₀
      hy hy₀]
  have pt : ∀ y : FrPt Xo c (CAt c.F.val.toRingHom), ∃ k P,
      IsPeriod (F.Di (ik k)) (fun j => relab c c.F.val.toRingHom (e j).1) P ∧ y.x = F.u (ik k) P := by
    intro y
    obtain ⟨k, x, t, ht⟩ := hU.2.2.1 y
    obtain ⟨P, -, hP, hy, -⟩ := hD.1.2 k x
    exact ⟨k, P, hP, ht.1.trans hy⟩
  have hA' : ∀ {i i' : Fin F.n} (gam : (F.Di i).La ≃ₗ[𝓞 D.host.E] (F.Di i').La) a,
      ∃ x, gam (F.t i a) = F.t i' a + l.A • x := fun gam a =>
    ⟨gam (F.t _ a) - F.t _ a, by rw [hA, one_smul, add_sub_cancel]⟩
  obtain ⟨z, z', hz, -, hz'⟩ := GlobalTheory.Frames.exists_complex_framed_pair _ _ _ _ Xo c K y y'
  refine hz' f hf a ?_
  replace hz := hz _ hy
  obtain ⟨k, P, hP, hyP⟩ := pt z
  obtain ⟨k', P', hP', hyP'⟩ := pt z'
  obtain ⟨h, hh⟩ := GlobalTheory.ShortMove.exists_marked_of_component D V H Dw l Xo _ g _ F hty _ rfl (U.X k) (ik k) (φ k) io
    (hW k) (hD.1.1 k) hι.emb hι.isom
  obtain ⟨γ₁, hγ₁, hΛ₁, hm₁, -⟩ := hD.2 h
  obtain ⟨γ₂, hγ₂, hΛ₂, hm₂, -⟩ := hD.2 (h * κ)
  obtain ⟨δ₁, hδu₁, hδf₁, -⟩ := GlobalTheory.MarkCoset.rational_matrix V γ₁ hγ₁
  obtain ⟨δ₂, hδu₂, hδf₂, -⟩ := GlobalTheory.MarkCoset.rational_matrix V γ₂ hγ₂
  obtain ⟨g₁, e₁, t₁, -⟩ := marked_isometry_half V l io (U.X k) (U.X (dict h).1) _ _ (φ k) (φ _) (F.t _) (F.t _)
    LinearMap.id h γ₁ 1 (hW k) (hW _) (hD.1.1 k) (hD.1.1 _) δ₁ hδu₁ hδf₁ rfl (fun a _ => ⟨0, zero_mem _, by
      rw [map_one, Units.val_one, Matrix.one_mulVec, smul_zero, add_zero]; rfl⟩) hh
    (by rw [mul_one]; exact ⟨hΛ₁, hm₁⟩)
  obtain ⟨g₂, e₂, t₂, -⟩ := marked_isometry_half V l io (U.X k) (U.X (dict (h * κ)).1) _ _ (φ k) (φ _) (F.t _) (F.t _)
    (s.f l.M) h γ₂ κ (hW k) (hW _) (hD.1.1 k) (hD.1.1 _) δ₂ hδu₂ hδf₂ hκ hκ' hh
    (by rw [mul_assoc]; exact ⟨hΛ₂, hm₂⟩)
  obtain ⟨g₃, e₃, t₃⟩ := GlobalTheory.LevStab.exists_isometry_of_levAut F hρ hP hP' (hyP ▸ hz.symm.trans hyP')
  have i₁ : ik k = ik (dict h).1 := GlobalTheory.Dict.index_eq_of_marked_isometry F hpq hσ hty _ _ g₁ e₁ t₁ (hA' g₁)
  have i₂ : ik k' = ik (dict (h * κ)).1 := by
    refine GlobalTheory.Dict.index_eq_of_marked_isometry F hpq hσ hty _ _ (g₃.symm.trans g₂) (fun a b => ?_)
      (fun a ha => ?_) (hA' _)
    · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e₂, ← e₃, g₃.apply_symm_apply, g₃.apply_symm_apply]
    · obtain ⟨x, hx⟩ := t₂ a ha
      obtain ⟨z, hz⟩ := exists_eq_nsmul l (t₃ a) (sub_mem
        (GlobalTheory.LevStab.map_mem_smul_top _ g₃.toLinearMap (GlobalTheory.LevStab.map_mem_smul_top _ _
          (GlobalTheory.LevStab.map_mem_smul_top _ _ ha))) (GlobalTheory.LevStab.map_mem_smul_top _ _ ha))
      refine ⟨x - g₂ (g₃.symm z), ?_⟩
      have : F.t (ik k') a = g₃ (F.t (ik k) (s.f l.M a)) - l.M • z := by rw [← hz, sub_sub_cancel]
      rw [LinearEquiv.trans_apply, this, map_sub, map_sub, g₃.symm_apply_apply, hx, map_nsmul, map_nsmul, smul_sub,
        add_sub_assoc]
  change toC (evR Xo c f z') = (a : ℂ) * toC (evR Xo c f z)
  rw [val _ _ P z i₁ hP hyP, val _ _ P' z' i₂ hP' hyP', ha, map_mul, map_mul, map_mul, Units.val_mul]
  ring

end Dict

end GlobalTheory.TwistTie
