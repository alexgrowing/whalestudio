import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulReadingOfMovedSectionAtFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CabsGenEqOneOfNormPin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSqMultiplierAlongIsometryMoveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCoordinatesFrameRationalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointArithmeticGroupInvariantSig
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.GeoLevel

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

set_option maxHeartbeats 800000 in

theorem exists_isometry_of_move_deriv {g : ℕ} {σ' : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ) {i : Fin F.n} {P P' : (F.Di i).La →+ (Fin g → ℂ)}
    (p : IsPeriod (F.Di i) ty P) (p' : IsPeriod (F.Di i) ty P') (hu : F.u i P ≫ ρ = F.u i P')
    (hd : ∀ j, ∃ v, IsDerivAt0 (fun z => (F.ex i P z).left) (Pi.single j 1) v ∧
      IsDerivAt0 (fun z => (F.ex i P' z).left) (Pi.single j 1) (v ≫ ν.φ)) :
    ∃ gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La, (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) ∧
      (∀ a, P' (gam a) = P a) ∧ ∀ z, (F.ex i P' z).left = (F.ex i P z).left ≫ ν.φ := by
  obtain ⟨gam, h, hiso, hh, hex⟩ := exists_isometry_of_sabMap F ν p p' hu
  have hcol : ∀ j, h.toLinearMap (Pi.single j 1) = Pi.single j 1 := by
    intro j
    obtain ⟨v, hv, d1⟩ := hd j
    have d0 := FibreDeriv.isDerivAt0_comp hv ν.φ
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P' p') h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p'
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have hid : h.toLinearMap = LinearMap.id := by
    refine (Pi.basisFun ℂ (Fin g)).ext fun j => ?_
    rw [Pi.basisFun_apply, hcol, LinearMap.id_apply]
  have hz : ∀ z, h z = z := fun z => LinearMap.congr_fun hid z
  exact ⟨gam, hiso, fun a => by rw [hh, hz], fun z => by rw [← hex, hz]⟩

set_option maxHeartbeats 1600000 in

theorem evR_normUn_move {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
    {M : ModelsOf F r} {k : Fin F.n} (T : ThetaData e F M k) {un : (M.X k).dom → FrPt Xo c (CAt σ)}
    (hun : IsNormUn T un) (x x' : (M.X k).dom) (A : Matrix (Fin r) (Fin r) E)
    (hA : A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E))
    (hper : ∀ a, ∃ a', (M.φ k a' : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E) ∧ T.Pf x'.1 a' = T.Pf x.1 a)
    {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ) (hρ : ρ ≫ Xo.s = Xo.s)
    (hx : (un x').x = (un x).x ≫ ρ) (hu : ∀ τ i, (un x').u τ i = (un x).u τ i ≫ ν.φ)
    {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hw : Dom w n) {f f' : Rul Xo c} (hf : f ∈ sec Xo c w n)
    (hff : ∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') :
    evR Xo c f' (un x) = evR Xo c f (un x') := by
  obtain ⟨κ, hκ, hy⟩ := hun x
  obtain ⟨κ', hκ', hy'⟩ := hun x'
  have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x.2
  have hb' : T.co.symm x'.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x'.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x'.2
  have p := T.isPer _ hb
  have p' := T.isPer _ hb'
  obtain ⟨gam, hiso, hP, hex⟩ := exists_isometry_of_move_deriv F ν p p'
    ((congrArg (· ≫ ρ) hy.1).symm.trans (hx.symm.trans hy'.1)) (fun j => by
      obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j
      exact ⟨_, hy.2.1 τ i, hu τ i ▸ hy'.2.1 τ i⟩)
  have hgam : ∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E) := fun a => by
    obtain ⟨a', h1, h2⟩ := hper a
    have h3 : gam a = a' := p'.2.1 (by rw [hP, T.co.apply_symm_apply, T.co.apply_symm_apply, h2])
    rw [h3, h1]
  obtain ⟨y', hmv⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (un x)).1
  obtain ⟨t₀, ht⟩ := exists_frBor_gen (un x') y' (hmv.1.trans hx.symm)
    (funext fun τ => funext fun i => (hmv.2.1 τ i).trans (hu τ i).symm)
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have d1 := (T.norm _ hb).1.ne_zero
  have d2 := (T.norm _ hb').1.ne_zero
  have k1 : κ ≠ 0 := fun h0 => mul_ne_zero hC d1 (by rw [← hκ, h0]; simp)
  have k2 : κ' ≠ 0 := fun h0 => mul_ne_zero hC d2 (by rw [← hκ', h0]; simp)
  have hth := GlobalTheory.T.thetaSection_sq_multiplier_along_isometry_move E H Dw l Xo c σ g e F r M k T _ hb _ hb' κ κ' (un x) (un x') y' gam A ρ ν _ k1 k2 hy hy'
    hiso hgam hA hP hex hmv ht
  have ht2 : Formalism.L2.PjFree.toC (t₀ : CAt σ) ^ 2 = 1 := by
    rw [hκ, hκ'] at hth
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hC d2) d1) ?_
    refine hth.trans ?_
    ring
  have hred : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  rw [hff _ _ hmv, (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ) hred w n f hf _ _ _ ht,
    wchar_ex_sign Dw _ ht2 (fun _ => rfl) w n hw.2, one_mul]

theorem exists_isMatch_of_models (D : Datum H) {X X' : Data E r} (φ : D.La ≃ₗ[𝓞 E] X.Λ) (φ' : D.La ≃ₗ[𝓞 E] X'.Λ)
    (hΨ : X.Ψ = X'.Ψ) (hp : X.p0 = X'.p0) (hG : X'.Gm = X.Gm) (hξ : X'.ξ0 = X.ξ0)
    (ef : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (ef' : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (φ' a : Fin r → E) (φ' b))) :
    ∃ δ : GL (Fin r) E, IsMatch X X' δ ∧
      ∀ a, (φ' a : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E) := by
  have hs : ∀ (Y : Data E r) (ψ : D.La ≃ₗ[𝓞 E] Y.Λ), Function.Injective (Y.Λ.subtype ∘ₗ ψ.toLinearMap) ∧
      Submodule.span E (Set.range (Y.Λ.subtype ∘ₗ ψ.toLinearMap)) = ⊤ := fun Y ψ => by
    refine ⟨Subtype.val_injective.comp ψ.injective, ?_⟩
    rw [← Y.Λ_span]
    congr 1
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (ψ a).2
    · intro hv
      exact ⟨ψ.symm ⟨v, hv⟩, congrArg Subtype.val (ψ.apply_symm_apply _)⟩
  have hc : cc (-X.ξ0) = -(-X.ξ0) := by
    have := X.ξ0_im
    unfold cc at this ⊢
    rw [map_neg, this]
  rw [hG, hξ] at ef'
  obtain ⟨δ, h1, h2⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H D D r (-X.ξ0) X.Gm
    (X.Λ.subtype ∘ₗ φ.toLinearMap) (X'.Λ.subtype ∘ₗ φ'.toLinearMap) (LinearEquiv.refl _ _) hc
    ⟨(hs X φ).1, (hs X φ).2, X.Gm_herm, X.Gm_det, ef⟩ ⟨(hs X' φ').1, (hs X' φ').2, X.Gm_herm, X.Gm_det, ef'⟩
    (fun _ _ => rfl)
  have h3 : ∀ a, (φ' a : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E) := h2
  refine ⟨δ, ⟨hΨ, hp, hξ.symm, fun u v => by rw [hG, h1], fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩, h3⟩
  · have := h3 (φ.symm ⟨v, hv⟩)
    rw [φ.apply_symm_apply] at this
    exact this ▸ (φ' _).2
  · have := h3 (φ'.symm ⟨_, hv⟩)
    rw [φ'.apply_symm_apply] at this
    have e := congrArg (fun u => ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u) this
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at e
    rw [e]
    exact (φ _).2

end

set_option maxHeartbeats 3200000 in

theorem rdU_move_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (φD : Dw.La →ₗ[𝓞 E] (Fin r → E)), Function.Injective φD → Submodule.span E (Set.range φD) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φD x) (φD y))) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ (U.X k).ξ0).im < 0) → ∀ (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ), ((δ : Matrix (Fin r) (Fin r) E).det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) E).det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x)) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k φD hinj hsp hEF hneg δ h hdet ρ ν hρ hmm w n hw f hf f' hf' hff x hx
  obtain ⟨g, e, F, ik, φ, ⟨hef, hpin⟩, hnorm⟩ := exists_pinned_of_isUnf hU
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F r
    (U.X k).ξ0 (U.X k).Gm φD (U.X k).ξ0_im hneg ⟨hinj, hsp, (U.X k).Gm_herm, (U.X k).Gm_det, hEF⟩
  have T : ∀ k, ThetaData e F M k := fun k => (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g e F r M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g e F r M k (T k)
  have hok : FramesOK e F M un :=
    ⟨fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g e F r M k (T k) (un k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g e F r M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g e F r M un hσ hM hξ hok
  obtain ⟨δ₀, h₀, hφ⟩ := exists_isMatch_of_models (F.Di (ik k)) (φ k) (M.φ (ik k))
    (Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hM.type (ik k)).2 τ).symm)
    ((hU.2.1 k).1.trans (hM.type (ik k)).1.symm) (hMG _).1 (hMG _).2 (hef k) (hM.ef _)
  have hPf : ∀ (y : Frame (U.X k).Ψ r) a j, (T (ik k)).Pf (lact δ₀ (castFr h₀.psi y)) a j =
      Formalism.L2.PjFree.perFr (U.X k) y (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2 := fun y a j => by
    rw [(T (ik k)).per, hφ]
    exact GlobalTheory.T.period_coordinates_frame_rational_isometry E r _ _ δ₀ h₀ y _ _ _
  have key : ∀ y : (U.X k).dom, (un (ik k) ⟨_, h₀.mem_dom y.2⟩).x = (U.un k y).x ∧
      (un (ik k) ⟨_, h₀.mem_dom y.2⟩).u = (U.un k y).u ∧
      (IsUnitFr (U.X k) y.1 → ∃ P : (F.Di (ik k)).La →+ (Fin g → ℂ),
        IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P ∧ (U.un k y).x = F.u (ik k) P ∧
        NormPin F (ik k) P (U.un k y) ∧ NormPin F (ik k) P (un (ik k) ⟨_, h₀.mem_dom y.2⟩)) := fun y => by
    obtain ⟨P, a1, a2, a3, a4⟩ := hpin k y
    obtain ⟨P', b1, -, b3, b4, b5⟩ := hok.1 (ik k) ⟨_, h₀.mem_dom y.2⟩
    obtain rfl : P' = P := AddMonoidHom.ext fun v => funext fun j =>
      (b1 v j).trans (((T (ik k)).per _ v j).symm.trans ((hPf y.1 v j).trans (a1 v j).symm))
    refine ⟨b3.trans a3.symm, funext fun τ => funext fun i =>
      ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ _ a2).2.1 _).unique (b4 τ i) (a4 τ i), fun hy =>
      ⟨P', a2, a3, hnorm k y P' a1 hy, b5 fun τ i => (congrArg norm (h₀.dmin_eq y.1 τ i)).trans (hy _ i)⟩⟩
  obtain ⟨ν₁, hν₁, hid⟩ := (GlobalTheory.MoveCalc.frMove_calculus E H Dw l Xo c).1
  have hmm₀ : MoveMatch U (unfOf e F M un) k (ik k) h₀ (𝟙 _) ν₁ := fun y y' hy =>
    ⟨hy.1.trans ((Category.comp_id _).trans (key y).1.symm), (funext fun τ => funext fun i =>
      (hy.2.1 τ i).trans ((congrArg _ hν₁).trans (Category.comp_id _))).trans (key y).2.1.symm⟩
  obtain ⟨ε, -, hε⟩ := GlobalTheory.T.exists_const_mul_reading_of_moved_section_at_frame E H Dw l Xo c σ r U (unfOf e F M un) hσ hU hU₀ k (ik k) δ₀ h₀ (𝟙 _) ν₁
    (Category.id_comp _) hmm₀ (fun y y' t hy hmv hb => by
      obtain ⟨P, p, a1, a2, a3⟩ := (key y).2.2 hy
      exact cabs_gen_eq_one_of_normPin E H Dw l Xo c σ _ g _ F _ _ P P _ ν₁ _ _ y' t p p a1
        ((key y).1.trans a1) a2 a3 hmv hb) n
  have hself : ∀ (f₀ : Rul Xo c) (y y' : FrPt Xo c (CAt σ)), FrMove (𝟙 _) ν₁ y y' →
      evR Xo c f₀ y = evR Xo c f₀ y' := fun f₀ y y' hy => by
    rw [(GlobalTheory.exists_unique_frMove E H Dw l Xo c _ ν₁ (Category.id_comp _) (CAt σ) y).2 y y' ν₁ rfl (hid _ y) hy]
  have hx' := h.mem_dom hx
  rw [hε w hw f' hf' f' hf' (hself f') x hx, hε w hw f hf f hf (hself f) _ hx']
  refine congrArg (ε * ·) ?_
  refine (rdU_of_mem (unfOf e F M un) f' (ik k) (h₀.mem_dom hx)).trans
    (Eq.trans (congrArg Formalism.L2.PjFree.toC ?_) (rdU_of_mem (unfOf e F M un) f (ik k) (h₀.mem_dom hx')).symm)
  obtain ⟨y', hmv⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (U.un k ⟨x, hx⟩)).1
  obtain ⟨m1, m2⟩ := hmm ⟨x, hx⟩ y' hmv
  obtain ⟨k1, k2, -⟩ := key ⟨x, hx⟩
  obtain ⟨k3, k4, -⟩ := key ⟨_, hx'⟩
  refine evR_normUn_move (T (ik k)) (hun (ik k)) ⟨_, h₀.mem_dom hx⟩ ⟨_, h₀.mem_dom hx'⟩
    ((δ₀ * δ * δ₀⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ?_ (fun a => ?_) ν hρ ?_ (fun τ i => ?_) hw hf hff
  · have : ((δ₀ * δ * δ₀⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det = (δ : Matrix (Fin r) (Fin r) E).det := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    rw [this]
    exact hdet
  · obtain ⟨a', ha'⟩ := (φ k).surjective ⟨_, (h.lat _).1 (φ k a).2⟩
    have ha : (φ k a' : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ k a : Fin r → E) := congrArg Subtype.val ha'
    refine ⟨a', ?_, funext fun j => ?_⟩
    · rw [hφ, hφ, ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc, Units.inv_mul,
        Matrix.mul_one, Units.val_mul]
    · refine (hPf _ a' j).trans (Eq.trans ?_ (hPf _ a j).symm)
      rw [ha]
      exact GlobalTheory.T.period_coordinates_frame_rational_isometry E r _ _ δ h x _ _ _
  · exact k3.trans (m1.symm.trans (hmv.1.trans (congrArg (· ≫ ρ) k1.symm)))
  · exact (congrFun (congrFun (k4.trans m2.symm) τ) i).trans
      ((hmv.2.1 τ i).trans (congrArg (· ≫ ν.φ) (congrFun (congrFun k2.symm τ) i)))

end GlobalTheory.GeoLevel
