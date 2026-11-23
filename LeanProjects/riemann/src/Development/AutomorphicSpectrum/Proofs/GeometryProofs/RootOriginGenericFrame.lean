import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsTriangularReframeExistsAndUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmplePointsLocalizedModel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenEx

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameTangent

attribute [local instance] Over.cartesianMonoidalCategory

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X₁ X₂ : Scheme.{0}} {t₁ : SAB H X₁}
  {t₂ : SAB H X₂} {f : X₁ ⟶ X₂} (m : SABMap t₁ t₂ f) {R : Type} [CommRing R] {x₁ : Sp R ⟶ X₁} {x₂ : Sp R ⟶ X₂}
  (h : x₁ ≫ f = x₂)

def pushHom (v : tEpsG x₁ ⟶ t₁.G) : tEpsG x₂ ⟶ t₂.G :=
  Over.homMk (v.left ≫ m.φ) (by
    have e := Over.w v
    have w := m.cart.1.w
    show (v.left ≫ m.φ) ≫ t₂.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x₂
    rw [Category.assoc, w, ← Category.assoc, e, ← h]
    simp)

@[simp] theorem pushHom_left (v : tEpsG x₁ ⟶ t₁.G) : (pushHom m h v).left = v.left ≫ m.φ := rfl

theorem pushHom_mul (u v : tEpsG x₁ ⟶ t₁.G) : pushHom m h (u * v) = pushHom m h u * pushHom m h v := by
  let T : Over X₁ := tEpsG x₁
  let a : (T ⟶ t₁.G) → (Over.mk (T.hom ≫ f) ⟶ t₂.G) := fun w => Over.homMk (w.left ≫ m.φ) (by
    have e := Over.w w
    have w' := m.cart.1.w
    show (w.left ≫ m.φ) ≫ t₂.G.hom = T.hom ≫ f
    rw [Category.assoc, w', ← Category.assoc, e])
  let e : tEpsG x₂ ⟶ Over.mk (T.hom ≫ f) := Over.homMk (𝟙 _) (by
    subst h
    simp [T])
  have h1 := m.cart.2 T u v (a u) (a v) rfl rfl
  have h2 : ∀ w, pushHom m h w = e ≫ a w := fun w => by
    apply Over.OverMorphism.ext
    simp [e, a]
  rw [h2, h2, h2, ← MonObj.comp_mul]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  rw [h1]
  rfl

theorem pushHom_one : pushHom m h (1 : tEpsG x₁ ⟶ t₁.G) = 1 := by
  have := pushHom_mul m h (1 : tEpsG x₁ ⟶ t₁.G) 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

theorem pushHom_smT (a : R) (v : tEpsG x₁ ⟶ t₁.G) : pushHom m h (GlobalTheory.FrameTangent.smT x₁ a v) = GlobalTheory.FrameTangent.smT x₂ a (pushHom m h v) := by
  apply Over.OverMorphism.ext
  show (spMap (epsMul a) ≫ v.left) ≫ m.φ = spMap (epsMul a) ≫ v.left ≫ m.φ
  rw [Category.assoc]

theorem pushHom_injective : Function.Injective (pushHom (x₁ := x₁) m h) := by
  intro u v e
  apply Over.OverMorphism.ext
  refine m.cart.1.hom_ext ?_ ?_
  · exact congrArg (fun w => w.left) e
  · rw [Over.w u, Over.w v]

def push : TanM x₁ t₁.G →ₗ[R] TanM x₂ t₂.G where
  toFun v := mkT (pushHom m h (tv v)) (by rw [← pushHom_smT, tv_zero', pushHom_one])
  map_add' u v := tv_injective (pushHom_mul m h _ _)
  map_smul' a v := tv_injective (pushHom_smT m h a (tv v))

@[simp] theorem push_left (v : TanM x₁ t₁.G) : (tv (push m h v)).left = (tv v).left ≫ m.φ := rfl

theorem push_injective : Function.Injective (push (x₁ := x₁) m h) := fun u v e =>
  tv_injective (pushHom_injective m h (congrArg tv e))

theorem push_surjective : Function.Surjective (push (x₁ := x₁) m h) := by
  intro w
  have hw : (tv w).left ≫ t₂.G.hom = (spMap (algebraMap R (DualNumber R)) ≫ x₁) ≫ f := by
    rw [Over.w (tv w), Category.assoc, h]
    rfl
  let v : tEpsG x₁ ⟶ t₁.G := Over.homMk (m.cart.1.lift (tv w).left _ hw) (IsPullback.lift_snd _ _ _ _)
  have hv : pushHom m h v = tv w := Over.OverMorphism.ext (IsPullback.lift_fst _ _ _ _)
  refine ⟨mkT v (pushHom_injective m h ?_), tv_injective hv⟩
  rw [pushHom_smT, hv, tv_zero', pushHom_one]

theorem push_act (a : 𝓞 E) (v : TanM x₁ t₁.G) :
    push m h (actL t₁.act a v) = actL t₂.act a (push m h v) := by
  apply tv_injective
  apply Over.OverMorphism.ext
  show ((tv v ≫ t₁.act.act a).left ≫ m.φ) = ((tv v).left ≫ m.φ) ≫ (t₂.act.act a).left
  rw [Over.comp_left, Category.assoc, Category.assoc, m.act]

end Push

section Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {Li : Type} [AddCommGroup Li] [Module Ω Li]
  (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G ξ Li)

theorem lie_smT (e : Li) : GlobalTheory.FrameTangent.smT ξ 0 (M.pt e) = 1 :=
  GlobalTheory.FrameTangent.smT_zero_ovT (t := t) (v := (M.pt e).left) ⟨Over.w (M.pt e), M.tan e⟩

def lieT : Li →ₗ[Ω] TanM ξ t.G where
  toFun e := mkT (M.pt e) (lie_smT M e)
  map_add' e e' := tv_injective (M.add e e')
  map_smul' c e := tv_injective (Over.OverMorphism.ext (M.smul c e))

@[simp] theorem tv_lieT (e : Li) : tv (lieT M e) = M.pt e := rfl

theorem lieT_injective : Function.Injective (lieT M) := fun _ _ h => M.inj (congrArg tv h)

theorem lieT_act {ρ : 𝓞 E →+* Module.End Ω Li} (hρ : M.IsActOf t.act.act ρ) (a : 𝓞 E) (e : Li) :
    lieT M (ρ a e) = actL t.act a (lieT M e) :=
  tv_injective (hρ a e)

end Lie

section Frame

open GlobalTheory.CompanionTheory.Ar.Small

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Ω : Type} [Field Ω] [Algebra c.F Ω]

theorem frame_matrix (y : FrPt Xo c Ω) (σ : E →+* ℂ) (W : Fin (D.mult σ) → TanM y.x Xo.univ.t.G)
    (hW : LinearIndependent Ω W)
    (he : ∀ i (a : 𝓞 E), actL Xo.univ.t.act a (W i) = algebraMap c.F Ω (embK c σ a) • W i) :
    ∃ g : Matrix (Fin (D.mult σ)) (Fin (D.mult σ)) Ω, IsUnit g.det ∧
      ∀ i, IsCombAt y.x (y.u σ) (fun j => g j i) (tv (W i)).left := by
  have ht : ∀ i, Formalism.L2.Pj.IsTanAt y.x (tv (W i)).left := fun i => GlobalTheory.FrameTangent.isTanAtG_of (t := Xo.univ.t) _ (tv_zero' _)
  have hg : ∀ i, IsEigAt c σ (tv (W i)).left := fun i a => congrArg (fun w => (tv w).left) (he i a)
  choose a ha _ using fun i => y.basis σ _ (ht i) (hg i)
  have hs : ∀ i, ∑ j, a i j • GlobalTheory.Reg.ReframeEx.toM (y.tan σ j) = W i := fun i =>
    tv_injective (Over.OverMorphism.ext ((GlobalTheory.Reg.ReframeEx.comb_iff (y.tan σ) _ _).1 (ha i)))
  refine ⟨Matrix.of fun j i => a i j, ?_, ha⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ p : Fin (D.mult σ) → Ω, ∑ i, p i • W i =
      ∑ j, ((Matrix.of fun j i => a i j).mulVec p) j • GlobalTheory.Reg.ReframeEx.toM (y.tan σ j) := by
    intro p
    simp_rw [← hs, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    simp [_root_.mul_comm]
  intro p q hpq
  apply linearIndependent_iff_injective_fintypeLinearCombination.1 hW
  simp only [Fintype.linearCombination_apply]
  rw [key, key, hpq]

theorem exists_reframed (y : FrPt Xo c Ω) {V : Type} [AddCommGroup V] [Module Ω V]
    (Φ : V →ₗ[Ω] TanM y.x Xo.univ.t.G) (hΦ : Function.Injective Φ)
    (b : ∀ s, Fin (labelRk D s) → V) (hb : ∀ s, LinearIndependent Ω (b s))
    (he : ∀ s k (a : 𝓞 E), actL Xo.univ.t.act a (Φ (b s k)) = algebraMap c.F Ω (labelEmb c s a) • Φ (b s k)) :
    ∃ y' : FrPt Xo c Ω, y'.x = y.x ∧ ∀ s k, y'.u (labelC s) (labelFin D s k) = (tv (Φ (b s k))).left := by
  let sO : (E →+* ℂ) → CMType H ⊕ CMType H := (labelEquiv H).symm
  have hs : ∀ σ, labelC (sO σ) = σ := (labelEquiv H).apply_symm_apply
  have hc : ∀ σ, D.mult σ = labelRk D (sO σ) := fun σ => by
    rw [← mult_labelC D (sO σ), hs]
  let W : ∀ σ, Fin (D.mult σ) → TanM y.x Xo.univ.t.G := fun σ i => Φ (b (sO σ) (Fin.cast (hc σ) i))
  have hg : ∀ σ, ∃ g : Matrix (Fin (D.mult σ)) (Fin (D.mult σ)) Ω, IsUnit g.det ∧
      ∀ i, IsCombAt y.x (y.u σ) (fun j => g j i) (tv (W σ i)).left := fun σ =>
    frame_matrix y σ (W σ) (((hb _).comp _ (Fin.cast_injective _)).map' Φ (LinearMap.ker_eq_bot.2 hΦ))
      (fun i a => by
        have e : embK c σ = labelEmb c (sO σ) := by rw [← embK_labelC, hs]
        rw [e]
        exact he _ _ a)
  choose g hu hcomb using hg
  obtain ⟨y', hx, hy⟩ := GlobalTheory.Reg.ReframeEx.exists_reframe y g hu
  refine ⟨y', hx, fun s k => ?_⟩
  have h3 := GlobalTheory.Reg.ReframeEx.comb_unique (y.tan _) (hy (labelC s) (labelFin D s k)) (hcomb (labelC s) (labelFin D s k))
  rw [h3]
  have e : sO (labelC s) = s := (labelEquiv H).symm_apply_apply s
  have h4 : ∀ (s' : CMType H ⊕ CMType H) (_ : s' = s) (h : D.mult (labelC s) = labelRk D s'),
      b s' (Fin.cast h (labelFin D s k)) = b s k := by
    rintro _ rfl h
    rfl
  show (tv (Φ (b (sO (labelC s)) (Fin.cast _ _)))).left = _
  rw [h4 _ e]

end Frame

section Point

open GlobalTheory.CompanionTheory.Ar.Small

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem exists_pt (𝔐 : GlobalTheory.CompanionTheory.Ar.HodgeCpt Y S y) :
    ∃ z : Sp Ω ⟶ Xo.XF c, z ≫ Y.j = 𝔐.ξ ≫ 𝔐.f ∧ z ≫ pullback.snd _ _ = spMap 𝔐.cst := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  have hfl : (Scheme.stalkClosedPointTo 𝔐.ξ₀).hom.Flat := RingHom.Flat.of_bijective 𝔐.gen₀.bij
  obtain ⟨v, hv⟩ := GlobalTheory.TorRef.DomFine.exists_generic_point (𝓞 c.F) c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense 𝔐.ξ₀ hfl
  letI := 𝔐.fn.toAlgebra
  let qq : FractionRing 𝔐.Ω₀ →+* Ω := IsFractionRing.lift (g := 𝔐.fn) 𝔐.fn.injective
  have hq : qq.comp (algebraMap 𝔐.Ω₀ (FractionRing 𝔐.Ω₀)) = 𝔐.fn := RingHom.ext fun a => IsFractionRing.lift_algebraMap 𝔐.fn.injective a
  have hz : (spMap qq ≫ v) ≫ Y.j = 𝔐.ξ ≫ 𝔐.f := by
    have e := 𝔐.fn_over
    have e' : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := e
    rw [e', ← hq, Category.assoc, Model.j, hv]
    show _ = Spec.map _ ≫ _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  refine ⟨spMap qq ≫ v, hz, ?_⟩
  have hb0 : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of (𝓞 c.F)) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  rw [← cancel_mono (spMap (algebraMap (𝓞 c.F) c.F))]
  have h1 := 𝔐.cst_over
  have h2 : spMap 𝔐.cst ≫ spMap (algebraMap (𝓞 c.F) c.F) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [h2, ← h1, ← Category.assoc 𝔐.ξ, ← hz, Model.j]
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]

end Point

end SlopeTestRemainingChoices

section Main

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameTangent GlobalTheory.CompanionTheory.Ar.Small

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem flag_mem (𝔐 : GlobalTheory.CompanionTheory.Ar.HodgeCpt Y S y) (Fl : 𝔐.Flag) (s : CMType H ⊕ CMType H) (k : Fin (labelRk D s)) :
    Fl.b s k ∈ 𝔐.Vgen s := by
  letI := 𝔐.fn.toAlgebra
  obtain ⟨cc, u, h1, -, -, -, -, -, h7, -⟩ := Fl.generic
  have hc : ∀ l', Fl.j (cc s l') ∈ 𝔐.Vgen s := fun l' =>
    (Fl.V₀_mem s _).1 ((h1 s).2 ▸ Submodule.subset_span ⟨l', rfl⟩)
  have hk : Fl.b s k ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω (Fl.b s) (k + 1) :=
    Submodule.subset_span ⟨k, by simp, rfl⟩
  rw [h7 s] at hk
  refine (Submodule.span_le.2 ?_) hk
  rintro _ ⟨k', -, rfl⟩
  exact Submodule.sum_mem _ fun l' _ => Submodule.smul_mem _ _ (hc l')

theorem flag_indep (𝔐 : GlobalTheory.CompanionTheory.Ar.HodgeCpt Y S y) (Fl : 𝔐.Flag) (s : CMType H ⊕ CMType H) :
    LinearIndependent Ω (Fl.b s) := by
  letI := 𝔐.fn.toAlgebra
  obtain ⟨cc, u, -, -, -, h4, -⟩ := Fl.generic
  exact h4 s

variable [Algebra c.F Ω]

def lieEquiv (y₀ : FrPt Xo c Ω) : TanM (ptF y₀) Y.oF.t.G ≃ₗ[Ω] TanM (ptF y₀ ≫ Y.j) Y.t.G :=
  LinearEquiv.ofBijective (push Y.m (x₁ := ptF y₀) rfl) ⟨push_injective _ _, push_surjective _ _⟩

theorem exists_Q (y₀ : FrPt Xo c Ω) {X' : Scheme.{0}} {t' : SAB H X'} {f : X' ⟶ Y.X} (m : SABMap t' Y.t f)
    {ξ : Sp Ω ⟶ X'} (hz : ξ ≫ f = ptF y₀ ≫ Y.j) {Li : Type} [AddCommGroup Li] [Module Ω Li]
    (M : GlobalTheory.CompanionTheory.Ar.LieModel t'.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (hρ : M.IsActOf t'.act.act ρ) :
    ∃ Q : Li →ₗ[Ω] TanM y₀.x Xo.univ.t.G, Function.Injective Q ∧
      (∀ (a : 𝓞 E) e, Q (ρ a e) = actL Xo.univ.t.act a (Q e)) ∧
      ∀ e, ∃ w : TanM (ptF y₀) Y.oF.t.G, (tv w).left ≫ Y.m.φ = (M.pt e).left ≫ m.φ ∧
        (tv (Q e)).left = (tv w).left ≫ Y.m0.toSABMap.φ := by
  let P := lieEquiv (Y := Y) y₀
  have hP : ∀ (a : 𝓞 E) u, P.symm (actL Y.t.act a u) = actL Y.oF.t.act a (P.symm u) := fun a u => by
    rw [LinearEquiv.symm_apply_eq]
    show _ = push Y.m rfl _
    rw [push_act]
    exact congrArg _ (P.apply_symm_apply u).symm
  refine ⟨(push Y.m0.toSABMap (ptF_fst y₀)) ∘ₗ P.symm.toLinearMap ∘ₗ (push m hz) ∘ₗ lieT M,
    (push_injective _ _).comp (P.symm.injective.comp ((push_injective _ _).comp (lieT_injective _))),
    fun a e => ?_, fun e => ⟨P.symm (push m hz (lieT M e)), ?_, rfl⟩⟩
  · have h1 : push m hz (lieT M (ρ a e)) = actL Y.t.act a (push m hz (lieT M e)) := by
      rw [lieT_act M hρ, push_act]
    have h3 : P.symm (push m hz (lieT M (ρ a e))) = actL Y.oF.t.act a (P.symm (push m hz (lieT M e))) :=
      (congrArg P.symm h1).trans (hP a _)
    exact (congrArg (push Y.m0.toSABMap (ptF_fst y₀)) h3).trans (push_act _ _ _ _)
  · exact congrArg (fun v => (tv v).left) (P.apply_symm_apply (push m hz (lieT M e)))

theorem exists_frame_at (y₀ : FrPt Xo c Ω) {X' : Scheme.{0}} {t' : SAB H X'} {f : X' ⟶ Y.X} (m : SABMap t' Y.t f)
    {ξ : Sp Ω ⟶ X'} (hz : ptF y₀ ≫ Y.j = ξ ≫ f) {Li : Type} [AddCommGroup Li] [Module Ω Li]
    (M : GlobalTheory.CompanionTheory.Ar.LieModel t'.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (hρ : M.IsActOf t'.act.act ρ)
    (b : ∀ s, Fin (labelRk D s) → Li) (hb : ∀ s, LinearIndependent Ω (b s))
    (he : ∀ s k (a : 𝓞 E), ρ a (b s k) = algebraMap c.F Ω (labelEmb c s a) • b s k) :
    ∃ y' : FrPt Xo c Ω, ptY Y y' = ξ ≫ f ∧
      ∀ s i, tanY Y y' (labelC s) (labelFin D s i) = (M.pt (b s i)).left ≫ m.φ := by
  obtain ⟨Q, hQ, hact, hw⟩ := exists_Q y₀ m hz.symm M ρ hρ
  obtain ⟨y', hx', hu⟩ := exists_reframed y₀ Q hQ b hb
    (fun s k a => by rw [← hact, he, map_smul])
  have hF' : ptF y' = ptF y₀ := pullback.hom_ext (by rw [ptF_fst, ptF_fst, hx']) (by rw [ptF_snd, ptF_snd])
  refine ⟨y', ?_, fun s i => ?_⟩
  · show ptF y' ≫ Y.j = _
    rw [hF', hz]
  · obtain ⟨w, h1, h2⟩ := hw (b s i)
    have h3 : tanF Y y' (labelC s) (labelFin D s i) = (tv w).left :=
      (eq_tanF Y y' _ _ (tv w).left (h2.symm.trans (hu s i).symm) (by rw [hF']; exact Over.w (tv w))).symm
    show tanF Y y' (labelC s) (labelFin D s i) ≫ Y.m.φ = _
    rw [h3, h1]

variable {Y₁ : Model Xo c (algebraMap (𝓞 c.F) c.F)}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y₁ Sys}

omit [Field Ω] [Algebra c.F Ω] in

theorem exists_genFrame (Or : RootOrigin Y₁ S RM Fx) : Nonempty (GenFrame Or) := by
  letI := cstAlg Or
  obtain ⟨z, hz, hzs⟩ := exists_pt Or.𝔐
  have hx : (z ≫ pullback.fst _ _) ≫ Xo.s = sOf c RM.Ω := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨y₀, h₀⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed _ hx
  have hF : ptF y₀ = z := by
    apply pullback.hom_ext
    · rw [ptF_fst, h₀]
    · rw [ptF_snd, hzs]
  subst hF
  have he : ∀ s k (a : 𝓞 E), Or.𝔐.ρ a (Or.Fl.b s k) = algebraMap c.F RM.Ω (labelEmb c s a) • Or.Fl.b s k :=
    fun s k a => by
      have h1 := (Submodule.mem_iInf _).1 (flag_mem Or.𝔐 Or.Fl s k) a
      have := LinearMap.mem_ker.1 h1
      exact sub_eq_zero.1 this
  obtain ⟨y', h1, h2⟩ := exists_frame_at y₀ Or.𝔐.m hz Or.𝔐.M Or.𝔐.ρ Or.𝔐.act Or.Fl.b (flag_indep Or.𝔐 Or.Fl) he
  exact ⟨⟨y', h1, h2, GlobalTheory.NonIntegralFrameExample.spread_holds Xo c _ y'⟩⟩

end Main

end GlobalTheory.CompanionTheory.Ar.GenEx
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.GenEx

theorem genFrame_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx), Nonempty (Small.GenFrame Or) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ Or => exists_genFrame Or

end GlobalTheory.CompanionTheory.Ar.GenEx
