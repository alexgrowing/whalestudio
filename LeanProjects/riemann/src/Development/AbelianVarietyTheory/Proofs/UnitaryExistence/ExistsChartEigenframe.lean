import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnivChartOfStandardSmooth
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ModuliChart

theorem exists_sec_of_secOn {X X' S S' : Scheme.{0}} {p : X ⟶ S} {p' : X' ⟶ S'} {t : S' ⟶ S} {F : X' ⟶ X}
    (hF : IsPullback F p' p t) {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull F))
    {V : S.Opens} (hV : ∀ y, t y ∈ V) {θ : ∀ i, Γ(X, p ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (p ⁻¹ᵁ V))
    (hne : ∀ y ∈ V, ∃ (g : X) (i : L.ι), p g = y ∧ g ∈ X.basicOpen (θ i)) :
    ∃ th : L'.Sec, ∀ y : S', ∃ x : X', p' x = y ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨w, hw⟩ := hw
  have hFV : ∀ y : X', p (F y) ∈ V := fun y => by
    rw [← Scheme.Hom.comp_apply, hF.w, Scheme.Hom.comp_apply]; exact hV _
  have le : ∀ j, F ⁻¹ᵁ L.U j ≤ F ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ L.U j) := fun j y hy => ⟨hFV y, hy⟩
  have val : ∀ (y : X') j, F y ∈ L.U j → gs (𝟙 X') y _ ((F.appLE _ _ (le j)).hom (θ j)) =
      (F.stalkMap y).hom (gs (𝟙 X) (F y) _ (θ j)) := fun y j h => by
    rw [gs_appLE F _ _ (le j) (𝟙 X') y h, Category.id_comp, gs_stalkMap F y _ (le j h)]
  obtain ⟨th, hth⟩ := sec_down ((isGen_iff w).1 hw) hL hL' (fun j => (F.appLE _ _ (le j)).hom (θ j))
    fun y j j' h h' => by
      rw [val y j h, val y j' h', LBGerm.gs_secOn hθ (F y) j j' (hFV y) h h', map_mul]
      congr 1
      have := PushInv.gm_comp F (𝟙 X) y (L.U j ⊓ L.U j') ⟨h, h'⟩ (L.g j j')
      rw [Category.comp_id] at this
      exact this.symm
  refine ⟨th, fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hne (t y) (hV y)
  obtain ⟨x, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback hF g y hg
  obtain rfl : F x = g := h₁
  obtain ⟨k, hk⟩ := exists_chart hL' x
  have hm : F x ∈ p ⁻¹ᵁ V ⊓ L.U i := X.basicOpen_le _ hi
  refine ⟨x, h₂, (SectionBaseChange.mem_nonzeroLocus th _).2 ⟨k, hk, ?_⟩⟩
  have e := hth _ (𝟙 _) x i k hm.2 hk
  rw [val x i hm.2] at e
  have hu : IsUnit (gs (𝟙 X) (F x) _ (θ i)) := by
    rw [gs_eq (𝟙 X) (F x) _ hm]
    exact (X.mem_basicOpen _ _ hm).1 hi
  exact isUnit_of_mul_isUnit_right (e ▸ hu.map (F.stalkMap x).hom)

theorem exists_away_point {R : Type} [CommRing R] (p : PrimeSpectrum R) {r : R} (hr : r ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (Localization.Away r), spMap (algebraMap R (Localization.Away r)) q = p := by
  have h : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_pull {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} (s' : S' ⟶ Sp B)
    (f : S' ⟶ S) (h : f ≫ s = s') (o : Obj D l b s) : ∃ o' : Obj D l b s', Nonempty (ObjMap o' o f) :=
  ObjPull.objPull_of_pol pol_pull E H D l B B b b (RingHom.id B) S S' s s' f rfl rfl
    (h.trans ((Category.comp_id _).symm.trans (congrArg (s' ≫ ·) (Spec.map_id _).symm))) o

theorem objMap_comp {B : Type} [CommRing B] {b : Base l B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    {s'' : S'' ⟶ Sp B} {o : Obj D l b s} {o' : Obj D l b s'} {o'' : Obj D l b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (m' : ObjMap o'' o' f') (m : ObjMap o' o f) : Nonempty (ObjMap o'' o (f' ≫ f)) := by
  obtain ⟨n, -⟩ := ((ObjMaps.id_comp_cancel E H D l B B B b b b S S' S'' s s' s'' o o' o'').2 f f' m).1 m'
  exact ⟨n⟩

theorem exists_eigen_chart (c : Coeff l) {g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H D.p D.q ty)
    {R : Type} [CommRing R] (j : c.F →+* R)
    (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (p : Sp R) :
    ∃ (R' : Type) (_ : CommRing R') (f : R →+* R')
      (o' : Obj D l (baseKA l) (spMap (f.comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom))
      (v : Fin g → (epsR R' ⟶ o'.t.G)), IsOpenImmersion (spMap f) ∧ p ∈ Set.range (spMap f) ∧
      Nonempty (ObjMap o' o (spMap f)) ∧ IsLieBasis v ∧
      ∀ i a, (v i ≫ o'.t.act.act a).left =
        spMap (epsScaleR (f.comp j ⟨ty i (a : E), c.conj (ty i) a⟩)) ≫ (v i).left := by
  obtain ⟨r, hr, v₀, hv₀⟩ := LieLoc.lie_locally_free R o.t.G _ (ObjDim.smoothOfRelativeDimension o) p
  obtain ⟨p₁, hp₁⟩ := exists_away_point p hr
  let R₁ := Localization.Away r
  let f₁ : R →+* R₁ := algebraMap R R₁
  obtain ⟨o₁, ⟨m₁⟩⟩ := exists_pull
    (spMap (f₁.comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (spMap f₁)
    (by rw [spMap_comp j f₁, Category.assoc]) o
  obtain ⟨e, he, -⟩ := grpPullback_iso m₁.cart (isGrpPullback_pullback o.t.G (spMap f₁))
  have hv₁ : IsLieBasis (fun i => v₀ i ≫ e.inv) := Chart.isLieBasis_iso e (by
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using hv₀)
  obtain ⟨r', hr', Hv⟩ := exists_isLieBasis_eigen E H D l c g ty hty R₁ (f₁.comp j) o₁ _ _ hv₁ p₁
  obtain ⟨p₂, hp₂⟩ := exists_away_point p₁ hr'
  let R₂ := Localization.Away r'
  let f₂ : R₁ →+* R₂ := algebraMap R₁ R₂
  obtain ⟨o₂, ⟨m₂⟩⟩ := exists_pull
    (spMap ((f₂.comp f₁).comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (spMap f₂)
    (by rw [RingHom.comp_assoc, spMap_comp (f₁.comp j) f₂, Category.assoc]) o₁
  obtain ⟨v, hv, hev⟩ := Hv o₂.t ⟨m₂.toSABMap⟩
  have i₁ : IsOpenImmersion (spMap f₁) := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))
  have i₂ : IsOpenImmersion (spMap f₂) := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R₁ (Localization.Away r')))))
  refine ⟨R₂, inferInstance, f₂.comp f₁, o₂, v, ?_, ?_, ?_, hv, hev⟩
  · rw [spMap_comp f₁ f₂]; infer_instance
  · refine ⟨p₂, ?_⟩
    rw [spMap_comp f₁ f₂]
    exact (congrArg (spMap f₁) hp₂).trans hp₁
  · rw [spMap_comp f₁ f₂]; exact objMap_comp m₂ m₁

theorem exists_chart_eigenframe : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → ∀ x : Xo.XF c, ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.F R) (jR : Sp R ⟶ Xo.XF c) (o : Obj D l (baseKA l) (spMap (algebraMap c.F R) ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (v : Fin g → (epsR R ⟶ o.t.G)) (th : o.t.PP.L.Sec), Algebra.FiniteType c.F R ∧ IsReduced R ∧ IsOpenImmersion jR ∧ x ∈ Set.range jR ∧ jR ≫ pullback.snd _ _ = spMap (algebraMap c.F R) ∧ Nonempty (ObjMap o Xo.univ (jR ≫ pullback.fst _ _)) ∧ IsLieBasis v ∧ (∀ i a, (v i ≫ o.t.act.act a).left = spMap (epsScaleR (algebraMap c.F R ⟨ty i (a : E), c.conj (ty i) a⟩)) ≫ (v i).left) ∧ (∀ y : Sp R, ∃ x : o.t.G.left, o.t.G.hom x = y ∧ x ∈ Out.nonzeroLocus th) ∧ (∀ s : o.t.PP.L.Sec, ∃! a : R, ∀ i, s.f i = constFn o.t.G.hom _ a * th.f i) := by
  intro hS E _ _ _ H D l Xo c g ty hty x
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  let π : Xo.XF c ⟶ Xo.X := pullback.fst _ _
  let σ : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  have hσ : Smooth σ := inferInstanceAs (Smooth (pullback.snd Xo.s _))
  have hred : AlgebraicGeometry.IsReduced (Xo.XF c) :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ σ hσ).1
  obtain ⟨V, hV, θ, hθ, -, hne⟩ := PushInv.pushInvertible hS Xo.X (Obj.toPolAV Xo.univ) (π x)
  obtain ⟨B, j₀, hj₀, ⟨p, hp⟩, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := Xo.XF c) (x := x) (U := π ⁻¹ᵁ V) hV
  let j : c.F →+* B := (Spec.preimage (j₀ ≫ σ)).hom
  have hj : j₀ ≫ σ = spMap j := (Spec.map_preimage (j₀ ≫ σ)).symm
  obtain ⟨o₀, ⟨m₀⟩⟩ := exists_pull (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (j₀ ≫ π)
    (by rw [← hj, Category.assoc, Category.assoc]; exact congrArg (j₀ ≫ ·) pullback.condition) Xo.univ
  obtain ⟨R, _, f, o, v, hf, ⟨q, hq⟩, ⟨m₁⟩, hv, hev⟩ := exists_eigen_chart c hty j o₀ p
  obtain ⟨m⟩ := objMap_comp m₁ m₀
  let jR : Sp R ⟶ Xo.XF c := spMap f ≫ j₀
  have hjR : IsOpenImmersion jR := IsOpenImmersion.comp (spMap f) j₀
  have hs : jR ≫ σ = spMap (f.comp j) := by
    rw [spMap_comp j f, ← hj]; exact Category.assoc _ _ _
  have hL : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨th, hth⟩ := exists_sec_of_secOn m.cart.1 Xo.univ.t.PP.isLB o.t.PP.isLB hL (V := V)
    (fun y => hsub ⟨spMap f y, rfl⟩) hθ hne
  letI : Algebra c.F R := (f.comp j).toAlgebra
  refine ⟨R, inferInstance, inferInstance, jR, o, v, th, ?_, ?_, hjR, ⟨q, ?_⟩, hs, ?_, hv, hev, hth,
    SectionBaseChange.generates hS (Obj.toPolAV Xo.univ) m.cart.1 o.t.PP.isLB hL th hth⟩
  · have h : LocallyOfFiniteType (spMap (f.comp j)) := by rw [← hs]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := CommRingCat.ofHom (f.comp j))).1 h
  · have h : AlgebraicGeometry.IsReduced (Sp R) := isReduced_of_isOpenImmersion jR
    exact (affine_isReduced_iff (CommRingCat.of R)).1 h
  · exact (congrArg j₀ hq).trans hp
  · have e : jR ≫ π = spMap f ≫ j₀ ≫ π := Category.assoc _ _ _
    exact (congrArg (fun u => Nonempty (ObjMap o Xo.univ u)) e).mpr ⟨m⟩

end GlobalTheory.ModuliChart
