import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.NegWeil

variable {D : D7}

theorem symplOH_neg_neg (S T : HSp D) (x y : WO S T) : symplOH S T (-x) (-y) = symplOH S T x y := by
  have h : hO S T (-x) (-y) = hO S T x y := by
    unfold hO
    simp only [Matrix.neg_apply, map_neg, mul_neg, neg_mul, neg_neg]
  unfold symplOH symplO
  rw [h]

theorem heisO_refl (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (f : WO S T → ℂ) :
    (fun x => heisO ψ S T u f (-x)) = heisO ψ S T (-u) (fun x => f (-x)) := by
  funext x
  unfold heisO
  simp only [← symplOH_neg_neg S T x (-u), neg_neg, neg_add]

theorem ratW_neg (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ratW T S (-γ) = -ratW T S γ := by
  ext i j
  simp [ratW]

theorem actO_neg (S T : HSp D) (g : GA D S) (h : GA D T) (w : WO S T) : actO S T g h (-w) = -actO S T g h w := by
  unfold actO
  rw [Matrix.mul_neg, Matrix.neg_mul]

theorem theta_refl {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T fun x => f (-x) := by
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp continuous_neg, fun k L hL hL0 w => ?_⟩
  · have := hf.quasi (-γ) (-w)
    rw [ratW_neg] at this
    have e : symplOH S T (-ratW T S γ) (-w) = symplOH S T (ratW T S γ) w := symplOH_neg_neg S T _ _
    rw [e] at this
    rw [← this, neg_add]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U, hU, fun u hu hu0 => ?_⟩
    have h0 : (-u).map (infPart D) = 0 := by
      rw [Matrix.map_neg _ (map_neg (infPart D)), hu0, neg_zero]
    have := heisO_refl ψ S T (-u) f
    rw [neg_neg, h (-u) (U.neg_mem hu) h0] at this
    exact this.symm
  · have := hf.smooth k (-L) hL.neg (fun t => by
      rw [AddMonoidHom.neg_apply, Matrix.map_neg _ (map_neg (finPart D)), hL0, neg_zero]) (-w)
    simpa only [AddMonoidHom.neg_apply, neg_add] using this

theorem theta_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (c : ℂ) :
    IsThetaFunO ψ S T (c • f) := by
  refine ⟨fun γ w => ?_, ?_, hf.cont.const_smul c, fun k L hL hL0 w => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hf.quasi γ w]
    ring
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U, hU, fun u hu hu0 => ?_⟩
    funext w
    have := congrFun (h u hu hu0) w
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]
    ring
  · exact (hf.smooth k L hL hL0 w).const_smul c

noncomputable def reflEnd (X : Type) [AddGroup X] : Module.End ℂ (X → ℂ) →* Module.End ℂ (X → ℂ) where
  toFun L :=
    { toFun := fun f x => L (fun y => f (-y)) (-x)
      map_add' := fun f f' => by
        have : (fun y => (f + f') (-y)) = (fun y => f (-y)) + fun y => f' (-y) := rfl
        rw [this, map_add]; rfl
      map_smul' := fun c f => by
        have : (fun y => (c • f) (-y)) = c • fun y => f (-y) := rfl
        rw [this, map_smul]; rfl }
  map_one' := LinearMap.ext fun f => funext fun x => by
    show f (- -x) = f x
    rw [neg_neg]
  map_mul' L L' := LinearMap.ext fun f => funext fun x => by
    show L (L' fun y => f (-y)) (-x) = L (fun z => L' (fun y => f (-y)) (- -z)) (-x)
    simp only [neg_neg]

noncomputable def reflRep {S T : HSp D} (om : WRep S T) : WRep S T := (reflEnd (WO S T)).comp om

theorem reflRep_apply {S T : HSp D} (om : WRep S T) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    reflRep om p f = fun x => om p (fun y => f (-y)) (-x) := rfl

theorem weil_refl {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hw : IsWeilDatumO ψ S T χS χT om) : IsWeilDatumO ψ S T χS χT (reflRep om) := by
  refine ⟨hw.std, hw.hecS, hw.hecT, hw.resS, hw.resT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p f hf
    exact theta_refl (hw.om_pres p _ (theta_refl hf))
  · intro g h w₀ f hf
    rw [reflRep_apply, reflRep_apply, heisO_refl, hw.om_heis _ _ _ _ (theta_refl hf), heisO_refl, actO_neg, neg_neg]
  · intro γ hγ γ' hγ' f hf
    rw [reflRep_apply]
    show om (γ, γ') (fun y => f (-y)) (-0) = f 0
    rw [neg_zero, hw.om_aut γ hγ γ' hγ' _ (theta_refl hf), neg_zero]
  · intro f hf w
    exact hw.om_cont _ (theta_refl hf) (-w)
  · intro μ 𝓕 hμ h𝓕 p f hf
    haveI : BorelSpace (WO S T) := ⟨rfl⟩
    let dE : WO S T ≃+ WO S T := AddEquiv.neg _
    set ν : Measure (WO S T) := μ.map dE with hν
    have hνH : ν.IsAddHaarMeasure := dE.isAddHaarMeasure_map μ continuous_neg continuous_neg
    have hfm : Measurable (fun x : WO S T => -x) := continuous_neg.measurable
    have hmp : MeasurePreserving (fun x : WO S T => -x) ν μ := by
      refine ⟨hfm, ?_⟩
      rw [hν, Measure.map_map hfm (show Measurable dE from hfm)]
      have : (fun x : WO S T => -x) ∘ dE = id := funext fun w => neg_neg w
      rw [this, Measure.map_id]
    have hemb : MeasurableEmbedding (fun x : WO S T => -x) := (Homeomorph.neg (WO S T)).measurableEmbedding
    have hfd : IsAddFundamentalDomain (ratL T S) ((fun x : WO S T => -x) ⁻¹' 𝓕) ν := by
      refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := fun γ : ratL T S => -γ) neg_bijective ?_
      intro γ x
      show -(-(γ : WO S T) + x) = (γ : WO S T) + -x
      rw [neg_add, neg_neg]
    calc ∫⁻ w in 𝓕, ‖reflRep om p f w‖ₑ ^ 2 ∂μ
        = ∫⁻ z in (fun x : WO S T => -x) ⁻¹' 𝓕, ‖reflRep om p f (-z)‖ₑ ^ 2 ∂ν :=
          (hmp.setLIntegral_comp_preimage_emb hemb (fun w => ‖reflRep om p f w‖ₑ ^ 2) 𝓕).symm
      _ = ∫⁻ z in (fun x : WO S T => -x) ⁻¹' 𝓕, ‖om p (fun y => f (-y)) z‖ₑ ^ 2 ∂ν := by
          simp only [reflRep_apply, neg_neg]
      _ = ∫⁻ z in (fun x : WO S T => -x) ⁻¹' 𝓕, ‖f (-z)‖ₑ ^ 2 ∂ν := hw.om_unit ν _ hνH hfd p _ (theta_refl hf)
      _ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := hmp.setLIntegral_comp_preimage_emb hemb (fun w => ‖f w‖ₑ ^ 2) 𝓕
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun F => ℓ fun z => F (-z)
        map_add' := fun a b => by rw [← map_add]; rfl
        map_smul' := fun c a => by rw [← map_smul]; rfl }
    have h1 : ℓ (fun z => om (g, h) (fun y => f (-y)) (-z)) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * ℓ (fun z => f (- -z)) :=
      H ℓ' (fun u hu F hF => by
        show ℓ (fun z => heisO ψ S T u F (-z)) = ℓ fun z => F (-z)
        rw [heisO_refl]
        exact hℓ (-u) (fun i j => by rw [Matrix.neg_apply, mul_neg, hu]) _ (theta_refl hF)) _ (theta_refl hf)
    simp only [neg_neg] at h1
    exact h1

theorem det_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (ε : R) (M : Matrix n n R)
    (h : ∀ i j, ε * (M - 1) i j = (M - 1) i j) : ∃ t, t * ε = M.det - 1 := by
  rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq, map_one, RingHom.map_det]
  have : (Ideal.Quotient.mk (Ideal.span {ε})).mapMatrix M = (Ideal.Quotient.mk (Ideal.span {ε})).mapMatrix 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, ← Matrix.sub_apply, ← h i j]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [this, map_one, Matrix.det_one]

theorem idem_identity {R : Type} [CommRing R] {e e' d d' t : R} (e1 : e * e = e) (e2 : e * e' = 0) (e3 : e' * e' = e')
    (h1 : d' * d = 1) (ht : t * (e + e') = d - 1) : d * (e' * d' + (1 - e')) = e * d + (1 - e) := by
  linear_combination e' * h1 - (1 - e - e') * ht - t * e1 - 2 * t * e2 - t * e3

theorem conj_det_mul (V : HSp D) (g : GA D V) : cA D (Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g).det = 1 := by
  rw [← GlobalTheory.ConjAdjWeil.det_inv_eq, ← Matrix.det_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.det_one]

theorem detA_val (V : HSp D) (g : GA D V) : ((detA V g : (AE D)ˣ) : AE D) = (Formalism.L2.Theta.mt V g).det := rfl

theorem conj_detAt {e : AE D} {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hx : IsDetAt e V g x) :
    cA D (x : AE D) = cA D e * cA D (Formalism.L2.Theta.mt V g).det + (1 - cA D e) := by
  rw [hx, map_add, map_mul, map_sub, map_one]

theorem conj_idem {e : AE D} (he : IsSplitIdem D e) : cA D e * cA D e = cA D e := by rw [← map_mul, he.1]

theorem det_sub_one_of_suppAt {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    ∃ t, t * (e + cA D e) = (Formalism.L2.Theta.mt V g).det - 1 := det_sub_one _ _ hg

theorem det_mul_conj {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) : detA V g * Units.map (cA D).toMonoidHom x = x := by
  obtain ⟨t, ht⟩ := det_sub_one_of_suppAt hg
  have h3 := idem_identity he.1 he.2.1 (conj_idem he) (conj_det_mul V g) ht
  rw [← conj_detAt hx] at h3
  have h4 : (Formalism.L2.Theta.mt V g).det * cA D (x : AE D) = x := h3.trans (Eq.symm hx)
  apply Units.ext
  rw [Units.val_mul, detA_val, Units.coe_map]
  exact h4

theorem chi_det {χ : (AE D)ˣ →* Circle} {n : ℕ} (hR : ResEta D χ n) {e : AE D} (he : IsSplitIdem D e) {V : HSp D}
    {g : GA D V} (hg : SuppAt e V g) {x : (AE D)ˣ} (hx : IsDetAt e V g x) : χ (detA V g) = χ x * χ x := by
  have := congrArg χ (det_mul_conj he hg hx)
  rw [map_mul, GlobalTheory.ConjAdjWeil.chi_conj hR] at this
  exact mul_inv_eq_iff_eq_mul.1 this

noncomputable def twistRep {S T : HSp D} (χ : (AE D)ˣ →* Circle) (om : WRep S T) : WRep S T where
  toFun p := (((χ (detA S p.1))⁻¹ : Circle) : ℂ) • om p
  map_one' := by simp
  map_mul' p q := by
    rw [map_mul, smul_mul_smul_comm, Prod.fst_mul, map_mul, map_mul, mul_inv, Circle.coe_mul]

theorem twistRep_apply {S T : HSp D} (χ : (AE D)ˣ →* Circle) (om : WRep S T) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    twistRep χ om p f = (((χ (detA S p.1))⁻¹ : Circle) : ℂ) • om p f := rfl

theorem weil_twist {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hH : IsHeckeChar D χT) (hR : ResEta D χT T.rank)
    (hw : IsWeilDatumO ψ S T χS χT⁻¹ om) : IsWeilDatumO ψ S T χS χT (twistRep χT om) := by
  refine ⟨hw.std, hw.hecS, hH, hw.resS, hR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p f hf
    exact theta_smul (hw.om_pres p f hf) _
  · intro g h w₀ f hf
    rw [twistRep_apply, twistRep_apply, hw.om_heis _ _ _ _ hf]
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    ring
  · intro γ hγ γ' hγ' f hf
    rw [twistRep_apply, GlobalTheory.Eis.apply_detA hH hγ, Pi.smul_apply, hw.om_aut γ hγ γ' hγ' f hf]
    simp
  · intro f hf w
    have hc : Continuous fun p : GA D S × GA D T => (((χT (detA S p.1))⁻¹ : Circle) : ℂ) :=
      continuous_subtype_val.comp ((hH.1.comp (GlobalTheory.Eis.continuous_detA.comp continuous_fst)).inv)
    exact hc.mul (hw.om_cont f hf w)
  · intro μ 𝓕 hμ hF p f hf
    rw [← hw.om_unit μ 𝓕 hμ hF p f hf]
    congr 1
    funext w
    rw [twistRep_apply, Pi.smul_apply, smul_eq_mul, enorm_mul, ← ofReal_norm_eq_enorm (((χT (detA S p.1))⁻¹ : Circle) : ℂ),
      Circle.norm_coe, ENNReal.ofReal_one, one_mul]
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have hfac : splitFacO χS χT x y = (χT (detA S g))⁻¹ * splitFacO χS χT⁻¹ x y := by
      rw [chi_det hR he hg hx]
      simp only [splitFacO, MonoidHom.inv_apply, inv_inv]
      group
    rw [twistRep_apply, map_smul, H ℓ hℓ f hf, hfac, Circle.coe_mul, smul_eq_mul]
    ring

theorem exists_neg_datum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B), IsWeilDatumO ψ A B χA χB om → (∀ f : WO A B → ℂ, IsThetaFunO ψ A B f → IsThetaFunO ψ (negSp A) B fun x => conj (f (-x))) ∧ ∃ om' : WRep (negSp A) B, IsWeilDatumO ψ (negSp A) B χA⁻¹ χB om' ∧ ∀ (g : GA D (negSp A)) (h : GA D B) (f : WO A B → ℂ), IsThetaFunO ψ A B f → om' (g, h) (fun x => conj (f (-x))) = fun x => (((χB (detA A (negEquiv A g)))⁻¹ : Circle) : ℂ) * conj (om (negEquiv A g, h) f (-x)) := by
  intro D ψ A B χA χB om hw
  refine ⟨fun f hf => ?_, ?_⟩
  · exact ((GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std A B).1 (fun x => f (-x))).2.2 (theta_refl hf)
  · have h1 : IsWeilDatumO ψ (negSp A) B χA⁻¹ χB⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource om) :=
      GlobalTheory.ConjWeil.weil_conjSource D ψ A B χA χB om hw
    refine ⟨_, weil_twist hw.hecT hw.resT (weil_refl h1), fun g h f _ => ?_⟩
    have e : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (fun y : WO A B => conj (f (- -y))) = f := by
      funext y
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    show (fun x => (((χB (detA A (negEquiv A g)))⁻¹ : Circle) : ℂ) *
      conj (om (negEquiv A g, h) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (fun y : WO A B => conj (f (- -y)))) (-x))) = _
    rw [e]

end GlobalTheory.NegWeil
