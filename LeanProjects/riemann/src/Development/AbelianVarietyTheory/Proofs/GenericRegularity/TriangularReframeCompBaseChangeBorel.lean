import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S]

theorem reframe_scal_mul (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  unfold scal Out.liftFun
  simp only [map_mul]

theorem reframe_scal_one (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x (1 : S) i = 1 := by
  unfold scal Out.liftFun
  simp only [map_one]

theorem generators_unit {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ r : LB.Sec (PPx x), ∃! a : S, ∀ i, r.f i = scal x a i * s.f i)
    (hs' : ∀ r : LB.Sec (PPx x), ∃! a : S, ∀ i, r.f i = scal x a i * s'.f i) :
    ∃ a : Sˣ, ∀ i, s'.f i = scal x (a : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c, -, hc⟩ := hs s
  have h1 : b * a = c := hc _ fun i => by rw [reframe_scal_mul, _root_.mul_assoc, ← ha i, ← hb i]
  have h2 : (1 : S) = c := hc _ fun i => by rw [reframe_scal_one, _root_.one_mul]
  exact ⟨⟨a, b, by rw [mul_comm, h1, ← h2], by rw [h1, ← h2]⟩, ha⟩

variable [Algebra c.F S]

theorem Reframe.trans {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {y y' y'' : FrPt Xo c S}
    (h : Reframe g y y') (h' : Reframe g' y' y'') : Reframe (fun τ => g τ * g' τ) y y'' := by
  obtain ⟨hx, hc⟩ := h
  obtain ⟨hx', hc'⟩ := h'
  refine ⟨hx'.trans hx, fun τ i => ?_⟩
  have h2 := hc' τ i
  rw [hx] at h2
  exact GlobalTheory.TangentLinear.isCombAt_mulVec _ _ _ _ _ _ _ (y.u τ) (y.tan τ) (y'.u τ) (g τ) (fun j => g' τ j i)
    (y''.u τ i) (hc τ) h2

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem comp_list_prod' {X Y : Over Xo.X} (f : X ⟶ Y) (L : List (Y ⟶ Xo.univ.t.G)) :
    f ≫ L.prod = (L.map (f ≫ ·)).prod := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem Reframe.baseChange {T : Type} [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T}
    (h : Reframe g y y') (hz : FrMap φ y z) (hz' : FrMap φ y' z') : Reframe (fun τ => (g τ).map φ) z z' := by
  obtain ⟨hx, hc⟩ := h
  obtain ⟨hzx, hzu, -⟩ := hz
  obtain ⟨hzx', hzu', -⟩ := hz'
  refine ⟨by rw [hzx', hzx, hx], fun τ i => ?_⟩
  obtain ⟨u, hu, hp⟩ := hc τ i
  have r1 : (dualMap φ.toRingHom).comp (algebraMap S (DualNumber S)) =
      (algebraMap T (DualNumber T)).comp φ.toRingHom := by
    refine RingHom.ext fun s => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have r2 : ∀ a : S, (dualMap φ.toRingHom).comp (epsMul a) =
      (epsMul (φ.toRingHom a)).comp (dualMap φ.toRingHom) := by
    intro a
    refine RingHom.ext fun s => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]
  have hw : spMap (dualMap φ.toRingHom) ≫ (tEps y.x).hom = (tEps z.x).hom := by
    show spMap (dualMap φ.toRingHom) ≫ (spMap (algebraMap S (DualNumber S)) ≫ y.x) =
      spMap (algebraMap T (DualNumber T)) ≫ z.x
    rw [hzx, ← Category.assoc, ← Category.assoc, spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, r1]
  obtain ⟨F, hF⟩ : ∃ F : tEps z.x ⟶ tEps y.x, F.left = spMap (dualMap φ.toRingHom) :=
    ⟨Over.homMk _ hw, rfl⟩
  refine ⟨fun j => F ≫ u j, fun j => ?_, ?_⟩
  · have hu' : (u j).left = spMap (epsMul (g τ j i)) ≫ y.u τ j := hu j
    show (F ≫ u j).left = spMap (epsMul (φ.toRingHom (g τ j i))) ≫ z.u τ j
    rw [Over.comp_left, hF, hu', hzu τ j, ← Category.assoc, ← Category.assoc, spMap_comp_moduli_spaces,
      spMap_comp_moduli_spaces, r2]
  · have hl : (List.ofFn fun j => F ≫ u j).prod = F ≫ (List.ofFn u).prod := by
      simp only [comp_list_prod', List.map_ofFn, Function.comp_def]
    rw [hl, Over.comp_left, hF, hp, hzu' τ i]

private theorem appLE_id_apply' {X : Scheme} (U : X.Opens) (e : U ≤ (𝟙 X) ⁻¹ᵁ U) (r : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U e).hom r = r := by
  change (X.presheaf.map (𝟙 (Opposite.op U))).hom r = r
  rw [X.presheaf.map_id]
  rfl

theorem frBor_iff_reframe (y y' : FrPt Xo c S) : (∃ t : Ix Dw → Sˣ, FrBor t y y') ↔
    ∃ b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S,
      (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, IsUnit (b τ i i)) ∧ Reframe b y y' := by
  constructor
  · rintro ⟨t, hx, hcomb, -⟩
    choose cf hcf1 hcf2 hcf3 using hcomb
    refine ⟨fun τ j i => cf τ i j, fun τ => ⟨fun p q hpq => hcf2 τ q p hpq, fun p => ?_⟩, hx, fun τ i => hcf3 τ i⟩
    show IsUnit (cf τ p p)
    rw [hcf1 τ p]
    exact Units.isUnit _
  · rintro ⟨b, hb, hx, hcomb⟩
    cases y'
    dsimp only at hx hcomb ⊢
    subst hx
    obtain ⟨a, ha⟩ := generators_unit y.s _ y.gen ‹_›
    obtain ⟨t, ht0, ht1⟩ : ∃ t : Ix Dw → Sˣ, t none = a ∧ ∀ τ i, (t (some ⟨τ, i⟩) : S) = b τ i i :=
      ⟨fun o => o.elim a fun p => ((hb p.1).2 p.2).unit, rfl, fun τ i => ((hb τ).2 i).unit_spec⟩
    refine ⟨t, rfl, fun τ i => ⟨fun j => b τ j i, (ht1 τ i).symm, fun j hij => (hb τ).1 hij, hcomb τ i⟩,
      𝟙 _, Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
    rw [ht0, ← ha i]
    exact appLE_id_apply' _ _ _

end

theorem reframe_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S], (∀ (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' y'' : FrPt Xo c S), Reframe g y y' → Reframe g' y' y'' → Reframe (fun τ => g τ * g' τ) y y'') ∧ (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), Reframe g y y' → FrMap φ y z → FrMap φ y' z' → Reframe (fun τ => (g τ).map φ) z z') ∧ ∀ y y' : FrPt Xo c S, (∃ t : Ix Dw → Sˣ, FrBor t y y') ↔ ∃ b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, IsUnit (b τ i i)) ∧ Reframe b y y' := by
  intro E _ _ _ H Dw l Xo c S _ _
  exact ⟨fun g g' y y' y'' h h' => Reframe.trans h h',
    fun T _ _ φ g y y' z z' h hz hz' => Reframe.baseChange φ h hz hz', fun y y' => frBor_iff_reframe y y'⟩

end GlobalTheory.Reg
