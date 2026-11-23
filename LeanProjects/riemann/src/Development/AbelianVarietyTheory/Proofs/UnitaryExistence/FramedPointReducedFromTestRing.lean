import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReducedFiniteTypeIffTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFactorOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliPointFromFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFgSubalgebraDescAway
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMapStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatricesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePointStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndCompStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniversalFrameTestRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesFramedPointsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameEqOfBaseChangeInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointsGluePrincipalCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.Frames.TestDescent

open GlobalTheory.FramedBaseChange

theorem spec_comp_alg {K S T U : Type} [Field K] [CommRing S] [CommRing T] [CommRing U] [Algebra K S]
    [Algebra K T] [Algebra K U] (φ : S →ₐ[K] T) (ψ : T →ₐ[K] U) :
    spMap (ψ.comp φ).toRingHom = spMap ψ.toRingHom ≫ spMap φ.toRingHom :=
  spec_comp φ.toRingHom ψ.toRingHom

theorem algHom_eq_of_spec {K S T : Type} [Field K] [CommRing S] [CommRing T] [Algebra K S]
    [Algebra K T] (φ ψ : S →ₐ[K] T) (h : spMap φ.toRingHom = spMap ψ.toRingHom) : φ = ψ := by
  have h1 := Spec.map_injective h
  have h2 : φ.toRingHom = ψ.toRingHom := congrArg CommRingCat.Hom.hom h1
  exact AlgHom.coe_ringHom_injective h2

theorem eq_of_away {S : Type} [CommRing S] {n : ℕ} (h : Fin n → S) (hs : Ideal.span (Set.range h) = ⊤)
    (a b : S) (hab : ∀ i, algebraMap S (Localization.Away (h i)) a = algebraMap S (Localization.Away (h i)) b) :
    a = b := by
  refine Localization.algebraMap_injective_of_span_eq_top _ hs ?_
  funext r
  obtain ⟨_, i, rfl⟩ := r
  exact hab i

theorem exists_lift_away {K S T : Type} [Field K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    (x : S) (f : S →ₐ[K] T) (hf : IsUnit (f x)) :
    ∃ ν : Localization.Away x →ₐ[K] T, ν.comp (IsScalarTower.toAlgHom K S (Localization.Away x)) = f := by
  have hf' : ∀ y : Submonoid.powers x, IsUnit (f y) := by
    rintro ⟨_, m, rfl⟩
    simp only [map_pow]
    exact hf.pow m
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers x) hf', ?_⟩
  ext s
  exact IsLocalization.lift_eq (M := Submonoid.powers x) (g := f.toRingHom) hf' s

theorem away_algHom_ext {K S T : Type} [Field K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    (x : S) (f g : Localization.Away x →ₐ[K] T)
    (h : ∀ s, f (algebraMap S _ s) = g (algebraMap S _ s)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  exact IsLocalization.ringHom_ext (Submonoid.powers x) (RingHom.ext h)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_of_cover {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (h : Fin n → S)
    (hs : Ideal.span (Set.range h) = ⊤) (y y' : FrPt Xo c S) (hx : y'.x = y.x)
    (z : ∀ i, FrPt Xo c (Localization.Away (h i)))
    (hy : ∀ i, FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away (h i))) y (z i))
    (hy' : ∀ i, FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away (h i))) y' (z i)) : y = y' := by
  obtain ⟨g, a, -, hga⟩ := (GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c S y y').1 hx
  have key := fun i => (GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c _ (z i) (z i)).2 _ _ _ _
    ((GlobalTheory.T.frameChange_comm_baseChange E H Dw l Xo c S _ _ y y' (z i) (z i) g a hga (hy i)).1 (hy' i))
    (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c _ (z i) (z i) (z i)).1
  have hg : g = fun _ => 1 := by
    funext τ
    ext p q
    refine eq_of_away h hs _ _ fun i => ?_
    have := congrFun (congrFun (congrFun (key i).1 τ) p) q
    simp only [Matrix.map_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have ha : a = 1 := by
    ext
    refine eq_of_away h hs _ _ fun i => ?_
    have := (key i).2
    simpa using this
  subst hg ha
  exact (GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S y (fun _ => 1) 1 (fun _ => by simp)).unique
    (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c _ y y y).1 hga

theorem exists_chart_cover (hB : Out.SecBaseChangeSt) {S : Type} [CommRing S] [Algebra c.F S]
    (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    ∃ (xF : Sp S ⟶ Xo.XF c) (n : ℕ) (g : Fin n → S) (p : Fin n → TRing c.F)
      (j : ∀ i, Sp (p i).R ⟶ Xo.XF c) (y₀ : ∀ i, FrPt Xo c (p i).R),
      xF ≫ pullback.fst _ _ = x ∧ Ideal.span (Set.range g) = ⊤ ∧ (∀ i, OpenChart (j i) (y₀ i)) ∧
      ∀ i (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam (g i)) →
        ∃ ψ : (p i).R →ₐ[c.F] T, spMap lam.toRingHom ≫ xF = spMap ψ.toRingHom ≫ j i := by
  classical
  let xF : Sp S ⟶ Xo.XF c := pullback.lift x (spMap (algebraMap c.F S)) (hx.trans (spec_comp _ _))
  choose p j y₀ hj hr using fun q : Sp S => GlobalTheory.T.exists_openChart_framedPoint_testRing hB E H Dw l Xo c (xF q)
  choose g hg hfac using fun q : Sp S => GlobalTheory.Frames.openChart_factor_near_prime E H Dw l Xo c _ (j q) (y₀ q)
    (hj q) S xF (pullback.lift_snd _ _ _) q (hr q)
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hg ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨t, ht, htspan⟩ := (Ideal.span_eq_top_iff_finite _).1 hspan
  choose q hq using fun a : t => ht a.2
  let e := t.equivFin.symm
  refine ⟨xF, t.card, fun i => g (q (e i)), fun i => p (q (e i)), fun i => j (q (e i)),
    fun i => y₀ (q (e i)), pullback.lift_fst _ _ _, ?_, fun i => hj _, fun i => hfac _⟩
  rw [eq_top_iff, ← htspan]
  refine Ideal.span_mono fun a ha => ⟨e.symm ⟨a, ha⟩, ?_⟩
  simp [hq]

theorem exists_away_val {K S : Type} [Field K] [CommRing S] [Algebra K S] (S₁ : Subalgebra K S) (b : S₁) :
    ∃ θ : Localization.Away b →ₐ[K] Localization.Away (b : S),
      (∀ s : S₁, θ (algebraMap S₁ _ s) = algebraMap S _ (s : S)) ∧ Function.Injective θ := by
  obtain ⟨b, hb⟩ := b
  obtain ⟨θ, hθ, hinj, -⟩ := GlobalTheory.exists_awayMap_subalgebra K S S₁ b hb
  exact ⟨θ, hθ, hinj⟩

theorem frMap_restrict {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (S₁ : Subalgebra c.F S) (h : S) (h₁ : S₁) (hh : (h₁ : S) = h)
    (κ : Localization.Away h₁ →ₐ[c.F] Localization.Away h)
    (hκ : ∀ s : S₁, κ (algebraMap S₁ _ s) = algebraMap S _ (s : S))
    (z : FrPt Xo c (Localization.Away h))
    (hz : FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away h)) y z)
    (v : FrPt Xo c (Localization.Away h₁)) (hv : FrMap κ v z)
    (b : S₁) (θ : Localization.Away b →ₐ[c.F] Localization.Away (b : S))
    (hθ : ∀ s : S₁, θ (algebraMap S₁ _ s) = algebraMap S _ (s : S))
    (α : Localization.Away h₁ →ₐ[c.F] Localization.Away b)
    (hα : α.toRingHom.comp (algebraMap S₁ _) = algebraMap S₁ _)
    (w : FrPt Xo c (Localization.Away (b : S)))
    (hw : FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away (b : S))) y w)
    (u : FrPt Xo c (Localization.Away b)) (hu : FrMap α v u) : FrMap θ u w := by
  have hα' : ∀ s : S₁, α (algebraMap S₁ _ s) = algebraMap S₁ _ s := fun s => RingHom.congr_fun hα s
  have hun : IsUnit (IsScalarTower.toAlgHom c.F S (Localization.Away (b : S)) h) := by
    have h1 : IsUnit (algebraMap S₁ (Localization.Away h₁) h₁) :=
      IsLocalization.Away.algebraMap_isUnit _
    have h2 := (h1.map α).map θ
    rw [hα', hθ, hh] at h2
    exact h2
  obtain ⟨ν, hν⟩ := exists_lift_away h _ hun
  have e : ν.comp κ = θ.comp α := by
    refine away_algHom_ext _ _ _ fun s => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hκ, hα', hθ]
    exact AlgHom.congr_fun hν (s : S)
  have m1 : FrMap ν z w := cancel _ ν hz (by rw [hν]; exact hw)
  have m2 : FrMap (θ.comp α) v w := by rw [← e]; exact trans _ _ hv m1
  exact cancel _ θ hu m2

theorem x_restrict {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra c.F A] [Algebra c.F B]
    (x : Sp R ⟶ Xo.X) (f : R →+* A) (g : R →+* B) (α : A →ₐ[c.F] B) (hα : α.toRingHom.comp f = g)
    {v : FrPt Xo c A} {u : FrPt Xo c B} (hv : v.x = spMap f ≫ x) (hu : FrMap α v u) :
    u.x = spMap g ≫ x := by
  rw [hu.1, hv, ← Category.assoc, ← spec_comp, hα]

theorem exists_descent_of_local (hB : Out.SecBaseChangeSt) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (S₁ : Subalgebra c.F S) (x₁ : Sp S₁ ⟶ Xo.X) (hx₁ : x₁ ≫ Xo.s = sOf c S₁)
    (hx : spMap S₁.val.toRingHom ≫ x₁ = y.x) {n : ℕ} (h : Fin n → S) (h₁ : Fin n → S₁)
    (hh : ∀ i, (h₁ i : S) = h i) (hs : Ideal.span (Set.range h) = ⊤) (hs₁ : Ideal.span (Set.range h₁) = ⊤)
    (κ : ∀ i, Localization.Away (h₁ i) →ₐ[c.F] Localization.Away (h i))
    (hκ : ∀ i (s : S₁), κ i (algebraMap S₁ _ s) = algebraMap S _ (s : S))
    (z : ∀ i, FrPt Xo c (Localization.Away (h i)))
    (hz : ∀ i, FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away (h i))) y (z i))
    (v : ∀ i, FrPt Xo c (Localization.Away (h₁ i)))
    (hvx : ∀ i, (v i).x = spMap (algebraMap S₁ (Localization.Away (h₁ i))) ≫ x₁)
    (hv : ∀ i, FrMap (κ i) (v i) (z i)) :
    ∃ y₁ : FrPt Xo c S₁, FrMap S₁.val y₁ y := by
  obtain ⟨y₁, hy₁x, hy₁⟩ := GlobalTheory.T.framedPoints_glue_principal_cover hB E H Dw l Xo c S₁ x₁ hx₁ n h₁ hs₁ v hvx (by
    intro i j α β hα hβ u hu
    obtain ⟨u', hu'⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hB E H Dw l Xo c _ _ β (v j)
    obtain ⟨θ, hθ, hinj⟩ := exists_away_val S₁ (h₁ i * h₁ j)
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hB E H Dw l Xo c _ _
      (IsScalarTower.toAlgHom c.F S (Localization.Away ((h₁ i * h₁ j : S₁) : S))) y
    have a1 := frMap_restrict y S₁ _ _ (hh i) (κ i) (hκ i) _ (hz i) _ (hv i) _ θ hθ α hα w hw u hu
    have b1 := frMap_restrict y S₁ _ _ (hh j) (κ j) (hκ j) _ (hz j) _ (hv j) _ θ hθ β hβ w hw u' hu'
    have a2 := x_restrict x₁ _ _ α hα (hvx i) hu
    have b2 := x_restrict x₁ _ _ β hβ (hvx j) hu'
    have : u = u' := GlobalTheory.T.frame_eq_of_baseChange_injective hB E H Dw l Xo c _ _ θ u u' w hinj (b2.trans a2.symm) a1 b1
    rw [this]
    exact hu')
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hB E H Dw l Xo c _ _ S₁.val y₁
  have : w = y := by
    refine eq_of_cover h hs w y ?_ z (fun i => ?_) hz
    · rw [hw.1, hy₁x, hx]
    · have e : (κ i).comp (IsScalarTower.toAlgHom c.F S₁ (Localization.Away (h₁ i))) =
          (IsScalarTower.toAlgHom c.F S (Localization.Away (h i))).comp S₁.val :=
        AlgHom.ext fun s => hκ i s
      refine cancel _ _ hw ?_
      rw [← e]
      exact trans _ _ (hy₁ i) (hv i)
  subst this
  exact ⟨y₁, hw⟩

theorem x_of_descended {R A S₀ T₁ T : Type} [CommRing R] [CommRing A] [CommRing S₀] [CommRing T₁] [CommRing T]
    [Algebra c.F R] [Algebra c.F A] [Algebra c.F S₀] [Algebra c.F T₁] [Algebra c.F T]
    (xF : Sp S₀ ⟶ Xo.XF c) (j : Sp R ⟶ Xo.XF c) (y₀ : FrPt Xo c R) (hj : OpenChart j y₀)
    (κ : T₁ →ₐ[c.F] T) (hinj : Function.Injective κ) (lam₁ : S₀ →ₐ[c.F] T₁) (lam : S₀ →ₐ[c.F] T)
    (hlam : κ.comp lam₁ = lam) (ψ₁ : R →ₐ[c.F] T₁) (ψ : R →ₐ[c.F] T)
    (hψ₁ : spMap lam₁.toRingHom ≫ xF = spMap ψ₁.toRingHom ≫ j)
    (hψ : spMap lam.toRingHom ≫ xF = spMap ψ.toRingHom ≫ j)
    (π : R →ₐ[c.F] A) (a' : A →ₐ[c.F] T₁) (ha : (κ.comp a').comp π = ψ)
    (u : FrPt Xo c A) (hu : u.x = spMap π.toRingHom ≫ y₀.x) (v : FrPt Xo c T₁) (hv : FrMap a' u v) :
    v.x = spMap lam₁.toRingHom ≫ xF ≫ pullback.fst _ _ := by
  haveI := hj.1
  have e2 : κ.comp ψ₁ = ψ := by
    apply algHom_eq_of_spec
    refine (cancel_mono j).1 ?_
    rw [← hlam, spec_comp_alg _ κ, Category.assoc, hψ₁] at hψ
    rw [spec_comp_alg _ κ, Category.assoc]
    exact hψ
  have e3 : a'.comp π = ψ₁ := by
    refine AlgHom.ext fun t => hinj ?_
    have := AlgHom.congr_fun (ha.trans e2.symm) t
    exact this
  rw [hv.1, hu, ← Category.assoc, ← spec_comp_alg, e3, ← hj.2.1, ← Category.assoc,
      ← hψ₁, Category.assoc]

set_option maxHeartbeats 800000 in

theorem exists_fg_descent (hB : Out.SecBaseChangeSt) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) :
    ∃ S₁ : Subalgebra c.F S, S₁.FG ∧ ∃ y₁ : FrPt Xo c S₁, FrMap S₁.val y₁ y := by
  obtain ⟨S₀, hS₀, x₀, hx₀, hx⟩ := GlobalTheory.moduli_point_from_fg_subalgebra E H Dw l Xo c S y.x y.x_over
  obtain ⟨xF, n, g, p, j, y₀, hxF, hg, hj, hfac⟩ := exists_chart_cover hB x₀ hx₀
  let h : Fin n → S := fun i => (g i : S)
  have hs : Ideal.span (Set.range h) = ⊤ := by
    have := congrArg (Ideal.map S₀.val) hg
    rwa [Ideal.map_top, Ideal.map_span, ← Set.range_comp] at this
  choose A π X s u hu using fun i => GlobalTheory.T.exists_universalFrame_testRing hB E H Dw l Xo c (p i) (y₀ i)
  choose z hz using fun i => GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hB E H Dw l Xo c _ _
    (IsScalarTower.toAlgHom c.F S (Localization.Away (h i))) y
  choose ψ hψ using fun i => hfac i (Localization.Away (h i))
    ((IsScalarTower.toAlgHom c.F S (Localization.Away (h i))).comp S₀.val)
    (IsLocalization.Away.algebraMap_isUnit (h i))
  have hzx : ∀ i, (z i).x = spMap (ψ i).toRingHom ≫ (y₀ i).x := by
    intro i
    rw [← (hj i).2.1, ← Category.assoc, ← hψ, Category.assoc, hxF, spec_comp_alg, Category.assoc, hx, (hz i).1]
  choose a ha hau using fun i =>
    (GlobalTheory.T.universalFrame_classifies_framedPoints hB E H Dw l Xo c _ _ (y₀ i) (π i) (X i) (s i) (u i) (hu i) _ (z i) (ψ i) (hzx i)).exists
  obtain ⟨S₁, h₁, hS₁, hle, hh, hs₁, hd⟩ := GlobalTheory.exists_fg_subalgebra_desc_away c.F S S₀ hS₀ n h
    (fun i => (A i).R) (fun i => inferInstance) a hs
  choose κ a' hκ hinj hκa using hd
  choose v hv using fun i => GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hB E H Dw l Xo c _ _ (a' i) (u i)
  let incl : S₀ →ₐ[c.F] S₁ := Subalgebra.inclusion hle
  refine ⟨S₁, hS₁, exists_descent_of_local hB y S₁ (spMap incl.toRingHom ≫ x₀) ?_ ?_ h h₁ hh hs hs₁ κ hκ z hz v
    (fun i => ?_) (fun i => cancel _ _ (hv i) ((hκa i).symm ▸ hau i))⟩
  · rw [Category.assoc, hx₀, sOf, sOf, ← spec_comp]
    rfl
  · rw [← Category.assoc, ← spec_comp_alg, ← hx]
    rfl
  · have hg₁ : incl (g i) = h₁ i := Subtype.ext (hh i).symm
    obtain ⟨ψ', hψ'⟩ := hfac i (Localization.Away (h₁ i))
      ((IsScalarTower.toAlgHom c.F S₁ (Localization.Away (h₁ i))).comp incl) (by
        rw [AlgHom.comp_apply, hg₁]
        exact IsLocalization.Away.algebraMap_isUnit (h₁ i))
    have e1 : (κ i).comp ((IsScalarTower.toAlgHom c.F S₁ (Localization.Away (h₁ i))).comp incl) =
        (IsScalarTower.toAlgHom c.F S (Localization.Away (h i))).comp S₀.val :=
      AlgHom.ext fun t => hκ i (incl t)
    obtain ⟨u₀, hu₀, hch⟩ := (hu i).2
    have t := x_of_descended xF (j i) (y₀ i) (hj i) (κ i) (hinj i) _ _ e1 ψ' (ψ i) hψ' (hψ i) (π i) (a' i)
      (by rw [hκa, ha]) (u i) (hch.1.trans hu₀.1) (v i) (hv i)
    rw [t, hxF, spec_comp_alg, Category.assoc]
    rfl

end GlobalTheory.Frames.TestDescent

namespace GlobalTheory.Frames

theorem allTest_of_secBaseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), AllTest Xo c := by
  intro hB E _ _ _ H Dw l Xo c S _ _ _ y
  obtain ⟨S₁, hS₁, y₁, hy₁⟩ := TestDescent.exists_fg_descent hB y
  have hred : IsReduced S₁ := isReduced_of_injective S₁.val Subtype.val_injective
  obtain ⟨p, ⟨e⟩⟩ := (GlobalTheory.reduced_finiteType_iff_testRing c.F).1 S₁
    ((Subalgebra.fg_iff_finiteType S₁).1 hS₁) hred
  obtain ⟨y', hy'⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hB E H Dw l Xo c _ _ (e.symm : S₁ →ₐ[c.F] p.R) y₁
  refine ⟨p, S₁.val.comp (e : p.R →ₐ[c.F] S₁), y', FramedBaseChange.cancel _ _ hy' ?_⟩
  have : (S₁.val.comp (e : p.R →ₐ[c.F] S₁)).comp (e.symm : S₁ →ₐ[c.F] p.R) = S₁.val := by
    ext t
    simp
  rw [this]
  exact hy₁

end GlobalTheory.Frames
