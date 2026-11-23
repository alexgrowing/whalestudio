import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.TieFrame

theorem one_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  have e := h.2 T 1 1 (pushPt h.1.w 1) (pushPt h.1.w 1) rfl rfl
  rw [_root_.mul_one] at e
  have e' : pushPt h.1.w (1 : T ⟶ G') = 1 := mul_eq_left.1 (Over.OverMorphism.ext e)
  refine (congrArg Over.Hom.left e').trans ?_
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  exact Category.assoc _ _ _

theorem exists_hom {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {A : Over (Sp K)} [GrpObj A]
    {φ : A.left ⟶ G.left} {φ' : A.left ⟶ G'.left} (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hφ : IsGrpPullback A G (spMap (algebraMap V K)) φ) (hφ' : IsGrpPullback A G' (spMap (algebraMap V K)) φ') :
    ∃ F : G ⟶ G', IsMonHom F ∧ φ ≫ F.left = φ' := by
  obtain ⟨e, he, h₁⟩ := grpPullback_iso hφ (isGrpPullback_pullback G _)
  obtain ⟨e', he', h₂⟩ := grpPullback_iso hφ' (isGrpPullback_pullback G' _)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := HomExtExamples.homExtSt_holds V K G G' hG hG' (e.inv ≫ e'.hom) inferInstance
  have a : ((Over.pullback (spMap (algebraMap V K))).map F).left ≫ pullback.fst G'.hom _ =
      pullback.fst G.hom _ ≫ F.left := pullback.lift_fst _ _ _
  refine ⟨F, hF, ?_⟩
  rw [← h₁, Category.assoc, ← a, hFf, ← Category.assoc, ← Over.comp_left, e.hom_inv_id_assoc, h₂]

theorem dual_w {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  rw [spMap_spMap, spMap_spMap]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_pull {V O : Type} [CommRing V] [CommRing O] {G : Over (Sp V)} [GrpObj G] {G' : Over (Sp O)} [GrpObj G']
    {f : V →+* O} {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) π) {u : epsOver V V ⟶ G} (hu : IsTan u) :
    ∃ x : LieG G', x.1.left ≫ π = spMap (dualMap f) ≫ u.left := by
  have w : (spMap (dualMap f) ≫ u.left) ≫ G.hom = spMap (algebraMap O (DualNumber O)) ≫ spMap f := by
    rw [Category.assoc, Over.w u, ← dual_w]
    rfl
  refine ⟨⟨Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ w), ?_⟩, h.1.lift_fst _ _ w⟩
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  refine Eq.trans ?_ (one_comp h (specO O O)).symm
  change (spMap (TrivSqZeroExt.fstHom O O O).toRingHom ≫ h.1.lift _ _ w) ≫ π = spMap (algebraMap O O) ≫ _
  have e : spMap (TrivSqZeroExt.fstHom O O O).toRingHom ≫ spMap (dualMap f) =
      spMap f ≫ spMap (TrivSqZeroExt.fstHom V V V).toRingHom := by
    rw [spMap_spMap, spMap_spMap]
    congr 1
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [Category.assoc, h.1.lift_fst, ← Category.assoc, e, Category.assoc, hu, Hom.one_def, Over.comp_left,
    Over.toUnit_left]
  change spMap f ≫ spMap (algebraMap V V) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap]

theorem exists_lieTie_of_frMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∃ x : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → LieG P.Gt, ∀ τ j, LieTie P ψ (x τ j) (z.u τ j) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz
  letI := io.toAlgebra
  obtain ⟨hk, G, t', m₁, m₂, π, φ, hπ, -, hφ, h4, rfl, -⟩ := hP
  obtain ⟨G₀, t₀, n₁, n₂, ⟨ub, ht, -, -, hub⟩, -⟩ := y₀.2.2
  obtain ⟨e, he, h₁⟩ := grpPullback_iso n₁.cart m₁.cart
  have h₂ : IsGrpPullback t₀.G G.G (spMap (algebraMap T.V T.Fr)) (e.hom.left ≫ m₂.φ) :=
    ((isGrpPullback_of_iso e).comp m₂.cart).congr (Category.id_comp _) rfl
  obtain ⟨F, hF, h₃⟩ := exists_hom G₀.semi G.semi n₂.cart h₂
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  suffices h : ∀ τ j, ∃ x : LieG P.Gt, LieTie P (φ ≫ m₁.φ) x (z.u τ j) by
    choose x hx using h
    exact ⟨x, hx⟩
  intro τ j
  obtain ⟨u', h5, h6⟩ := hub τ j
  have ht' : IsTan (ub τ j ≫ F) := by
    unfold IsTan
    rw [Over.comp_left, ← Category.assoc, ht τ j, ← Over.comp_left, MonObj.one_comp]
  obtain ⟨xG, hx⟩ := exists_pull hπ ht'
  obtain ⟨x, hc, -⟩ := existsUnique_left (P := P) hp (isAdicComplete_dualNumber p) xG.1
  have h7 := hc.comp (TrivSqZeroExt.fstHom O O O)
  rw [xG.2] at h7
  have hu : (u' ≫ e.hom.left) ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    haveI : Mono (spMap (algebraMap T.V T.Fr)) :=
      haveI : IsPreimmersion (spMap (algebraMap T.V T.Fr)) := IsPreimmersion.of_isLocalization (nonZeroDivisors T.V)
      inferInstance
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, Category.assoc, ← m₂.cart.1.w,
      ← Category.assoc e.hom.left, ← h₃, Category.assoc, Over.w F, ← Category.assoc, h6, Category.assoc,
      Over.w (ub τ j), ← dual_w]
    rfl
  have w : (spMap (dualMap k.toRingHom) ≫ u' ≫ e.hom.left) ≫ t'.G.hom =
      spMap (algebraMap C (DualNumber C)) ≫ spMap k.toRingHom := by
    rw [Category.assoc, hu, dual_w]
  refine ⟨⟨x, (existsUnique_left (P := P) hp₀ inferInstance 1).unique h7 Corr.one⟩, xG,
    Over.homMk (hφ.1.lift _ _ w) (hφ.1.lift_snd _ _ w), hc, ?_, hπ.1.hom_ext ?_ ?_⟩
  · change hφ.1.lift _ _ w ≫ _ = _
    rw [hφ.1.lift_fst_assoc, hz.2.1, ← h5, Category.assoc, Category.assoc, h₁]
  · change (hφ.1.lift _ _ w ≫ _) ≫ _ = _
    rw [Category.assoc, ← h4, hφ.1.lift_fst_assoc, Category.assoc, Category.assoc, ← h₃, ← Category.assoc u', h6,
      Category.assoc, Category.assoc, hx, ← Category.assoc, ← Category.assoc (spMap _) (spMap _), spMap_spMap,
      spMap_spMap, Over.comp_left]
    congr 2
    refine RingHom.ext fun s => TrivSqZeroExt.ext ?_ ?_
    · simpa [dualMap] using (hk s.fst).symm
    · simpa [dualMap, Algebra.algebraMap_eq_smul_one] using (hk s.snd).symm
  · change (hφ.1.lift _ _ w ≫ _) ≫ _ = _
    rw [Category.assoc, P.gen_pull.1.w, hφ.1.lift_snd_assoc, Category.assoc, Over.w xG.1]
    exact (dual_w _).symm

end GlobalTheory.CompHt.TieFrame
