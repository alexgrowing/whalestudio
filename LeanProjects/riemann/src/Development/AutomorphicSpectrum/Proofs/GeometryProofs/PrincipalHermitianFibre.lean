import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductConjugateStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeFibre

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexAt NumberField.ComplexEmbedding

section Linear

variable {F W : Type*} [AddCommGroup F] [Module ℂ F] [AddCommGroup W] [Module ℂ W]

@[reducible] def coreOfForm (e : F ≃ₗ[ℂ] W) (h : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hh : ∀ v w, h w v = starRingEnd ℂ (h v w)) (hp : ∀ v, v ≠ 0 → 0 < (h v v).re) :
    InnerProductSpace.Core ℂ F where
  inner a b := h (e a) (e b)
  conj_inner_symm a b := by
    simpa using (hh (e b) (e a)).symm
  re_inner_nonneg a := by
    by_cases ha : e a = 0
    · simp [ha]
    · exact (hp _ ha).le
  add_left a b c := by simp
  smul_left a b r := by simp
  definite a h0 := by
    by_contra ha
    have := hp (e a) (fun h1 => ha (by simpa using h1))
    rw [h0] at this
    simp at this

variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module (𝓞 L) V]

theorem exists_metric [Module.Finite (𝓞 L) V] [Module.Projective (𝓞 L) V]
    (W : (L →+* ℂ) → Type) [∀ σ, AddCommGroup (W σ)] [∀ σ, Module ℂ (W σ)]
    (e : ∀ σ, Fibre σ V ≃ₗ[ℂ] W σ) (h : ∀ σ, W σ →ₗ⋆[ℂ] W σ →ₗ[ℂ] ℂ)
    (hh : ∀ σ v w, h σ w v = starRingEnd ℂ (h σ v w)) (hp : ∀ σ v, v ≠ 0 → 0 < (h σ v v).re)
    (hc : ∀ σ (x y : V), h (conjugate σ) (e _ ((1 : ComplexAt (conjugate σ)) ⊗ₜ x)) (e _ ((1 : ComplexAt (conjugate σ)) ⊗ₜ y)) =
      starRingEnd ℂ (h σ (e σ ((1 : ComplexAt σ) ⊗ₜ x)) (e σ ((1 : ComplexAt σ) ⊗ₜ y)))) :
    ∃ m : HermitianMetric L V, ∀ σ (x y : V), (m.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] y) =
      h σ (e σ ((1 : ComplexAt σ) ⊗ₜ x)) (e σ ((1 : ComplexAt σ) ⊗ₜ y)) := by
  have tm : ∀ (σ : L →+* ℂ) (z : ComplexAt σ) (x : V), (z ⊗ₜ[𝓞 L] x : Fibre σ V) =
      ((ofComplex σ).symm z : ℂ) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) := fun σ z x => by
    rw [TensorProduct.smul_tmul', complex_smul_def]
    simp
  have cm : ∀ (σ : L →+* ℂ) (x : V), conjMap σ V ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) =
      (1 : ComplexAt (conjugate σ)) ⊗ₜ[𝓞 L] x := fun σ x => by
    rw [conjMap_tmul, map_one]
  refine ⟨⟨fun σ => coreOfForm (e σ) (h σ) (hh σ) (hp σ), fun σ x y => ?_⟩, fun σ x y => rfl⟩
  change h _ (e _ _) (e _ _) = starRingEnd ℂ (h σ (e σ x) (e σ y))
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul z a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add c d hc' hd => simp only [map_add, ← hc', ← hd]
    | tmul w b =>
      rw [tm σ z a, tm σ w b, conjMap_smul, conjMap_smul, cm, cm]
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, hc, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply]

end Linear

section Geo

theorem exists_fibre_equiv {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] {L : Type} [Field L] [NumberField L]
    (x : Sp (𝓞 L) ⟶ S) {V : Type} [AddCommGroup V] [Module (𝓞 L) V] (M : LieModel G x V) (σ : L →+* ℂ)
    {W : Type} [AddCommGroup W] [Module ℂ W] (Mσ : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ x) W)
    (j : V →ₛₗ[σ.comp (algebraMap (𝓞 L) L)] W)
    (hj : ∀ a, M.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) a (Mσ.pt (j a))) :
    ∃ e : Fibre σ V ≃ₗ[ℂ] W, ∀ a, e ((1 : ComplexAt σ) ⊗ₜ a) = j a := by
  letI i₀ : Algebra (𝓞 L) ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAlgebra
  letI i₂ : Module (𝓞 L) W := Module.compHom W (algebraMap (𝓞 L) ℂ)
  haveI i₃ : IsScalarTower (𝓞 L) ℂ W := ⟨fun a z w => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let j' : V →ₗ[𝓞 L] W := { toFun := j, map_add' := map_add j, map_smul' := fun a v => j.map_smulₛₗ a v }
  have hb : IsBaseChange ℂ j' :=
    GlobalTheory.T.lie_model_isBaseChange S G (𝓞 L) ℂ x V W M Mσ j' hj
  let l : ComplexAt σ ≃ₗ[𝓞 L] ℂ :=
    { toFun := (ofComplex σ).symm, invFun := ofComplex σ, map_add' := map_add _,
      map_smul' := fun a z => rfl, left_inv := (ofComplex σ).left_inv, right_inv := (ofComplex σ).right_inv }
  let e₀ : Fibre σ V ≃ₗ[𝓞 L] ℂ ⊗[𝓞 L] V := TensorProduct.congr l (LinearEquiv.refl _ V)
  let E : Fibre σ V ≃+ W := e₀.toAddEquiv.trans hb.equiv.toAddEquiv
  have he : ∀ z a, E (z ⊗ₜ a) = ((ofComplex σ).symm z) • j a := fun z a => by
    change hb.equiv (e₀ (z ⊗ₜ a)) = _
    change hb.equiv (l z ⊗ₜ a) = _
    rw [hb.equiv_tmul]
    rfl
  refine ⟨{ E with map_smul' := fun c t => ?_ }, fun a => ?_⟩
  · change E (c • t) = c • E t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [TensorProduct.smul_tmul', he, he, complex_smul_def, map_mul, mul_smul]
      simp
    | add a b ha hb' => rw [smul_add, map_add, map_add, ha, hb', smul_add]
  · exact (he 1 a).trans (by simp)

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_comp_alt {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem lifts_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ S}
    {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) {c : R →+* R'} {x' : Sp R' ⟶ S} {a : V}
    {v : epsAt x' ⟶ G} (h : M.Lifts c (𝟙 G.left) a v) : v.left = spMap (dualMap c) ≫ (M.pt a).left :=
  (Category.comp_id _).symm.trans h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polarised_at {L : Type} [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L))
    (m : SABMap tK t (spMap (algebraMap (𝓞 L) L))) (hK : IsPrincipal tK) (σ : L →+* ℂ) :
    ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _)),
      IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L := by
  obtain ⟨hP, hA, -⟩ := hK
  obtain ⟨t', ⟨m₁⟩⟩ := exists_sab (spMap σ) tK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  have e : spMap σ ≫ spMap (algebraMap (𝓞 L) L) = spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ := by
    rw [Category.comp_id, spectrumMap_comp]
  refine ⟨t', e ▸ n, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsProper) m₁.cart.1 hP
  · obtain ⟨w, gw, -⟩ := m₁.lin
    exact relAmple_pull m₁.cart.1 tK.PP.isLB t'.PP.isLB ((isGen_iff w).1 gw) ⊤ (isAffineOpen_top _)
      (fun _ => trivial) hA

theorem hodgeInnerProduct_conj_of_eq {X : Scheme.{0}} (t : SAB H X) {z z' : Sp ℂ ⟶ X}
    (hz : z' = spMap (starRingEnd ℂ) ≫ z) {v w : epsAt z ⟶ t.G} {v' w' : epsAt z' ⟶ t.G} {c : ℂ}
    (hv : v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left)
    (hw : w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left) (h : HodgeIP t.G t.PP.L z v w c) :
    HodgeIP t.G t.PP.L z' v' w' (starRingEnd ℂ c) := by
  subst hz
  exact GlobalTheory.T.hodge_inner_product_conjugate E H X t z v w v' w' c hv hw h

end Geo

theorem exists_hermitianBundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (_ : SABMap tK t (spMap (algebraMap (𝓞 L) L))), IsPrincipal tK → ∃ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G (𝟙 _) B.carrier), IsFibre (HodgeIP t.G t.PP.L) (𝟙 _) B MB := by
  intro E _ _ _ H L _ _ t tK m hK
  haveI : Smooth t.G.hom := t.semi.smooth
  obtain ⟨V, i₁, i₂, ⟨M⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ t.G (𝓞 L) (𝟙 _)
  obtain ⟨hf, hpj⟩ := GlobalTheory.T.lie_model_finite_projective _ t.G (𝓞 L) (𝟙 _) V M
  have hW := fun σ : L →+* ℂ => GlobalTheory.CompanionTheory.Ar.lieModel_exists _ t.G ℂ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _)
  choose W iW₁ iW₂ hM using hW
  let Mσ : ∀ σ : L →+* ℂ, LieModel t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) (W σ) := fun σ => (hM σ).some
  choose j hj using fun σ : L →+* ℂ =>
    (GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts _ t.G (𝓞 L) ℂ (σ.comp (algebraMap (𝓞 L) L)) (𝟙 _) V (W σ) M (Mσ σ)).exists
  choose e he using fun σ : L →+* ℂ => exists_fibre_equiv t.G (𝟙 _) M σ (Mσ σ) (j σ) (hj σ)
  choose h hI hh hp using fun σ : L →+* ℂ =>
    GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form E H _ t _ (W σ) (Mσ σ) (polarised_at t tK m hK σ)
  have hcs : ∀ σ : L →+* ℂ, (conjugate σ).comp (algebraMap (𝓞 L) L) =
      (starRingEnd ℂ).comp (σ.comp (algebraMap (𝓞 L) L)) := fun σ => RingHom.ext fun a => rfl
  have hl : ∀ (σ : L →+* ℂ) (x : V), ((Mσ (conjugate σ)).pt (j _ x)).left =
      spMap (dualMap (starRingEnd ℂ)) ≫ ((Mσ σ).pt (j σ x)).left := fun σ x => by
    have e₁ : spMap (dualMap ((conjugate σ).comp (algebraMap (𝓞 L) L))) =
        spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) := by
      rw [hcs, dualMap_comp_alt, spectrumMap_comp]
    exact (lifts_left M (hj _ x)).trans ((congrArg (· ≫ (M.pt x).left) e₁).trans ((Category.assoc _ _ _).trans
      (congrArg (spMap (dualMap (starRingEnd ℂ)) ≫ ·) (lifts_left M (hj σ x)).symm)))
  have hz : ∀ σ : L →+* ℂ, spMap ((conjugate σ).comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ =
      spMap (starRingEnd ℂ) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ := fun σ => by
    rw [Category.comp_id, Category.comp_id, hcs, spectrumMap_comp]
  obtain ⟨mt, hmt⟩ := exists_metric W e h hh hp fun σ x y => by
    rw [he, he, he, he]
    exact ((hI _ _ _ _).1 (hodgeInnerProduct_conj_of_eq t (hz σ) (hl σ x) (hl σ y) ((hI σ _ _ _).2 rfl))).symm
  refine ⟨{ carrier := V, metric := mt }, M, fun σ x x' v v' hv hv' => ?_⟩
  have key : ∀ (a : V) (u : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) ⟶ t.G),
      M.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 t.G.left) a u → u = (Mσ σ).pt (j σ a) := fun a u ha => by
    exact Over.OverMorphism.ext ((lifts_left M ha).trans (lifts_left M (hj σ a)).symm)
  obtain rfl := key x v hv
  obtain rfl := key x' v' hv'
  have := hmt σ x x'
  rw [he, he] at this
  rw [this]
  exact (hI σ _ _ _).2 rfl

end GlobalTheory.CompanionTheory.Ar.HodgeFibre
