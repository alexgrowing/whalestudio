import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsBasisOfSaturated
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.SaturatedCharts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Gen

variable {S : Scheme.{0}} {M : Over S} [MonObj M]

theorem comp_listProd {X Y : Over S} (f : X ⟶ Y) : ∀ {k : ℕ} (u : Fin k → (Y ⟶ M)),
    f ≫ (List.ofFn u).prod = (List.ofFn fun i => f ≫ u i).prod
  | 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact MonObj.comp_one f
  | k + 1, u => by
    simp only [List.ofFn_succ, List.prod_cons, MonObj.comp_mul]
    rw [comp_listProd f (fun i => u i.succ)]

theorem listProd_comp {X : Over S} {N : Over S} [MonObj N] (g : M ⟶ N) [IsMonHom g] :
    ∀ {k : ℕ} (u : Fin k → (X ⟶ M)), (List.ofFn u).prod ≫ g = (List.ofFn fun i => u i ≫ g).prod
  | 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact MonObj.one_comp g
  | k + 1, u => by
    simp only [List.ofFn_succ, List.prod_cons, MonObj.mul_comp]
    rw [listProd_comp g (fun i => u i.succ)]

end Gen

theorem fst_comp_jetTan {V : Type} [CommRing V] {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (TrivSqZeroExt.fstHom V V V).comp (jetTan (R := V) (m := 0) ℓ) = (jetAug : Jet V κ (0 + 1) →ₐ[V] V) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  by_cases h : i = ℓ <;>
    simp [jetTan, jetAug, liftJet, h, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.lift_mk] <;>
    erw [Ideal.Quotient.lift_mk] <;> simp [h]

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
variable (t : SAB H (Sp V))

def toT (v : Sp (DualNumber V) ⟶ t.G.left) (h : v ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := V) (DualNumber V) ⟶ t.G :=
  Over.homMk v h

def eT : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := V) (DualNumber V) ⟶ tEpsG (𝟙 (Sp V)) :=
  Over.homMk (𝟙 _) (by simp)

def eT' : tEpsG (𝟙 (Sp V)) ⟶ ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := V) (DualNumber V) :=
  Over.homMk (𝟙 _) (by simp)

theorem prodPts_of_combAt {m : ℕ} (v : Fin m → (Sp (DualNumber V) ⟶ t.G.left))
    (hv : ∀ i, v i ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) (a : Fin m → V)
    (w : Sp (DualNumber V) ⟶ t.G.left) (hw : w ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    (hc : IsCombAtG t (𝟙 (Sp V)) v a w) :
    toT t w hw = ReciprocityTheory.ChartRestriction.G.Chart.prodPts a (fun i => toT t (v i) (hv i)) := by
  obtain ⟨u, hu, hp⟩ := hc
  have h1 : toT t w hw = eT ≫ (List.ofFn u).prod := by
    apply Over.OverMorphism.ext
    simp only [toT, Over.homMk_left, Over.comp_left, eT, Category.id_comp]
    exact hp.symm
  rw [h1, comp_listProd]
  unfold ReciprocityTheory.ChartRestriction.G.Chart.prodPts
  congr 2
  funext i
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, eT, Over.homMk_left, Category.id_comp, hu i, toT]
  rfl

theorem combAt_of_prodPts {m : ℕ} (v : Fin m → (Sp (DualNumber V) ⟶ t.G.left))
    (hv : ∀ i, v i ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) (a : Fin m → V)
    (w : Sp (DualNumber V) ⟶ t.G.left) (hw : w ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    (he : toT t w hw = ReciprocityTheory.ChartRestriction.G.Chart.prodPts a (fun i => toT t (v i) (hv i))) :
    IsCombAtG t (𝟙 (Sp V)) v a w := by
  refine ⟨fun i => eT' ≫ ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD (a i)) ≫ toT t (v i) (hv i),
    fun i => ?_, ?_⟩
  · simp only [Over.comp_left, eT', Over.homMk_left, Category.id_comp, toT]
    rfl
  · rw [← comp_listProd eT' (fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD (a i)) ≫
      toT t (v i) (hv i))]
    have he' : (List.ofFn fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD (a i)) ≫
        toT t (v i) (hv i)).prod = toT t w hw := he.symm
    rw [he']
    simp [eT', toT]

theorem chartTan_of (v : Sp (DualNumber V) ⟶ t.G.left) (h : IsTanAtG t (𝟙 (Sp V)) v) :
    ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t v ((h.1).trans (Category.comp_id _))) := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom V V V).toRingHom) ≫ v =
    Spec.map (CommRingCat.ofHom (algebraMap V V)) ≫ η[t.G].left
  refine h.2.trans ?_
  show 𝟙 _ ≫ η[t.G].left = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rfl

theorem tanAt_of (v : Sp (DualNumber V) ⟶ t.G.left) (hv : v ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    (h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t v hv)) : IsTanAtG t (𝟙 (Sp V)) v := by
  refine ⟨hv.trans (Category.comp_id _).symm, ?_⟩
  have h' := congrArg CommaMorphism.left h
  refine h'.trans ?_
  show Spec.map (CommRingCat.ofHom (algebraMap V V)) ≫ η[t.G].left = 𝟙 _ ≫ η[t.G].left
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rfl

theorem isTan_iff' (w : epsOver V V ⟶ t.G) :
    IsTan w ↔ ReciprocityTheory.ChartRestriction.G.Chart.IsTan (R := V) (G := t.G) w :=
  ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg CommaMorphism.left h⟩

theorem isComb_iff' {m : ℕ} (v : Fin m → (epsOver V V ⟶ t.G)) (a : Fin m → V) (w : epsOver V V ⟶ t.G) :
    IsComb v a w ↔ w = ReciprocityTheory.ChartRestriction.G.Chart.prodPts (R := V) (G := t.G) a v := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD (a i)) ≫ v i := by
      funext i
      apply Over.OverMorphism.ext
      rw [hu i]
      rfl
    rw [this]
    rfl
  · intro h
    exact ⟨fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD (a i)) ≫ v i, fun i => rfl, h⟩

end Tan

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

set_option maxHeartbeats 1000000 in
open ReciprocityTheory.ChartRestriction.G.Chart (tcoord tan_ext prodPts prodPts_tan) in
theorem saturation_charts_holds : ChartSaturated Xo c := by
  intro T io y C τ
  have hsm : Smooth C.I.G.G.hom := C.I.G.semi.smooth
  obtain ⟨n, x, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc (R := T.V) C.I.G.G

  let D : Fin (chD C.ch) → (Sp (DualNumber T.V) ⟶ C.I.G.G.left) := fun j =>
    (homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫
      C.xT 1).left
  have hDo : ∀ j, D j ≫ C.I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := fun j =>
    (Over.w (homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) :
      Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ C.xT 1)).trans (Category.comp_id _)
  have hz : spMap ((jetAug : Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] T.V) : Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →+* T.V) ≫
      (C.xT 1).left = (1 : overAt (𝟙 (Sp T.V)) T.V ⟶ C.I.G.G).left :=
    congrArg CommaMorphism.left (C.chartT.zero 1)
  have hDt : ∀ j, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT C.I.G (D j) (hDo j)) := by
    intro j
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫
        (spMap ((jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] DualNumber T.V) :
          Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →+* DualNumber T.V) ≫ (C.xT 1).left) =
      Spec.map (CommRingCat.ofHom (algebraMap T.V T.V)) ≫ η[C.I.G.G].left
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have e1 : ((TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom).comp
        ((jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] DualNumber T.V) :
          Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →+* DualNumber T.V) = ((jetAug (m := 0 + 1) : Jet T.V (Fin 1 × Fin (chD C.ch)) (0 + 1) →ₐ[T.V] T.V) :
          _ →+* T.V) := by
      rw [← fst_comp_jetTan]
      rfl
    rw [e1]
    refine hz.trans ?_
    show (spMap (algebraMap T.V T.V) ≫ 𝟙 _) ≫ η[C.I.G.G].left = _
    rw [Category.comp_id]
  let Mv : Fin (chD C.ch) → (Fin n → T.V) := fun j => tcoord hx _ (hDt j)
  let L : (Fin (chD C.ch) → T.V) →ₗ[T.V] (Fin n → T.V) :=
    { toFun := fun a => ∑ j, a j • Mv j
      map_add' := fun a b => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hL : ∀ a, L a = ∑ j, a j • Mv j := fun _ => rfl

  have hcomb : ∀ (a : Fin (chD C.ch) → T.V) (w : Sp (DualNumber T.V) ⟶ C.I.G.G.left)
      (hw : w ≫ C.I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V))),
      IsCombAtG C.I.G (𝟙 (Sp T.V)) D a w →
      ∃ h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT C.I.G w hw), tcoord hx _ h = L a := by
    intro a w hw hc
    have e := prodPts_of_combAt C.I.G D hDo a w hw hc
    obtain ⟨h, hh⟩ := prodPts_tan hx a _ hDt
    exact ⟨e ▸ h, (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx e _ h).trans hh⟩

  have htgo : ∀ k, C.tgT k ≫ C.I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := fun k =>
    ((C.tgBasis.1 k).1).trans (Category.comp_id _)
  have htgt : ∀ k, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT C.I.G (C.tgT k) (htgo k)) := fun k =>
    chartTan_of C.I.G (C.tgT k) (C.tgBasis.1 k)
  have htgc : ∀ k, tcoord hx _ (htgt k) = Mv k := by
    intro k
    obtain ⟨h, hh⟩ := hcomb (Pi.single k (1 : T.V)) (C.tgT k) (htgo k) (C.chartT.tan k)
    rw [ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx rfl (htgt k) h, hh, hL]
    simp [Pi.single_apply]

  have hLinj : Function.Injective L := by
    intro a b hab
    let tg' : Fin (chD C.ch) → (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := T.V) (DualNumber T.V) ⟶ C.I.G.G) :=
      fun k => toT C.I.G (C.tgT k) (htgo k)
    obtain ⟨ha, ea⟩ := prodPts_tan hx a tg' htgt
    obtain ⟨hb, eb⟩ := prodPts_tan hx b tg' htgt
    have heq : prodPts a tg' = prodPts b tg' := by
      apply tan_ext hx ha hb
      rw [ea, eb]
      simp only [tg', htgc]
      simpa only [hL] using hab
    have hwo : (prodPts a tg').left ≫ C.I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w _
    have hwT : IsTanAtG C.I.G (𝟙 (Sp T.V)) (prodPts a tg').left :=
      tanAt_of C.I.G _ hwo (by
        have : toT C.I.G (prodPts a tg').left hwo = prodPts a tg' := Over.OverMorphism.ext rfl
        rw [this]; exact ha)
    obtain ⟨a0, _, huniq⟩ := C.tgBasis.2 _ hwT
    have hA : IsCombAtG C.I.G (𝟙 (Sp T.V)) C.tgT a (prodPts a tg').left :=
      combAt_of_prodPts C.I.G C.tgT htgo a _ hwo (Over.OverMorphism.ext rfl)
    have hB : IsCombAtG C.I.G (𝟙 (Sp T.V)) C.tgT b (prodPts a tg').left :=
      combAt_of_prodPts C.I.G C.tgT htgo b _ hwo
        ((Over.OverMorphism.ext rfl : toT C.I.G _ hwo = prodPts a tg').trans heq)
    exact (huniq a hA).trans (huniq b hB).symm

  let u : Fin (Dw.mult τ) → (Fin (chD C.ch) → T.V) := fun i => C.uvecT ⟨τ, i⟩
  let ub : Fin (Dw.mult τ) → (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := T.V) (DualNumber T.V) ⟶ C.I.G.G) :=
    fun i => C.I.ub τ i
  have hubt : ∀ i, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (ub i) := fun i => (isTan_iff' C.I.G _).1 (C.I.tan τ i)
  have hubc : ∀ i, tcoord hx _ (hubt i) = L (u i) := by
    intro i
    obtain ⟨h, hh⟩ := hcomb (C.uvecT ⟨τ, i⟩) (C.I.ub τ i).left (Over.w _) (C.dirT ⟨τ, i⟩)
    exact (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx (Over.OverMorphism.ext rfl) (hubt i) h).trans hh
  have hcombub : ∀ (g : Fin (Dw.mult τ) → T.V), ∃ h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (prodPts g ub),
      tcoord hx _ h = L (∑ i, g i • u i) := by
    intro g
    obtain ⟨h, hh⟩ := prodPts_tan hx g ub hubt
    refine ⟨h, hh.trans ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hubc i, map_smul]

  have hli : LinearIndependent T.V u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨hp, ep⟩ := hcombub g
    have h1 : prodPts g ub = 1 := by
      apply tan_ext hx hp ReciprocityTheory.ChartRestriction.G.Chart.isTan_one
      rw [ep, hg, map_zero, ReciprocityTheory.ChartRestriction.G.Chart.tcoord_one]
    have h0 : prodPts (0 : Fin (Dw.mult τ) → T.V) ub = 1 := by
      unfold prodPts
      have : (fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD ((0 : Fin (Dw.mult τ) → T.V) i)) ≫
          ub i) = fun _ => 1 := funext fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap_scaleD_zero (hubt i)
      rw [this]
      simp
    have htan1 : IsTan (1 : epsOver T.V T.V ⟶ C.I.G.G) :=
      (isTan_iff' C.I.G _).2 ReciprocityTheory.ChartRestriction.G.Chart.isTan_one
    have heig1 : IsEigV c io C.I.G τ (1 : epsOver T.V T.V ⟶ C.I.G.G) := by
      intro b z _
      have hb := C.I.G.act.hom b
      have e1 : (1 : epsOver T.V T.V ⟶ C.I.G.G) ≫ C.I.G.act.act b = 1 := MonObj.one_comp _
      have e2 : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD z) ≫
          (1 : epsOver T.V T.V ⟶ C.I.G.G) = 1 := MonObj.comp_one _
      rw [e1]
      exact (congrArg CommaMorphism.left e2).symm
    obtain ⟨a0, _, huniq⟩ := C.I.basis τ 1 htan1 heig1
    have hg1 := huniq g ((isComb_iff' C.I.G _ _ _).2 h1.symm)
    have hg0 := huniq 0 ((isComb_iff' C.I.G _ _ _).2 h0.symm)
    intro i
    exact congrFun (hg1.trans hg0.symm) i

  have hsat : ∀ (v : Fin (chD C.ch) → T.V) (a : T.V), a ≠ 0 →
      a • v ∈ Submodule.span T.V (Set.range u) → v ∈ Submodule.span T.V (Set.range u) := by
    intro v a ha hv
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun T.V).1 hv
    let w := ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := x) (L v)
    have hwt : ReciprocityTheory.ChartRestriction.G.Chart.IsTan w := ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx _
    have hwc : tcoord hx w hwt = L v := ReciprocityTheory.ChartRestriction.G.Chart.tcoord_tvec hx _
    obtain ⟨hp, ep⟩ := hcombub g
    have hsc : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD a) ≫ w = prodPts g ub := by
      apply tan_ext hx (ReciprocityTheory.ChartRestriction.G.Chart.isTan_scale a hwt) hp
      rw [ReciprocityTheory.ChartRestriction.G.Chart.tcoord_scale hx a hwt, hwc, ep, hg, map_smul]
    have heig : ∀ (b : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c τ b) →
        w ≫ C.I.G.act.act b = ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD z) ≫ w := by
      intro b z hz
      have hb := C.I.G.act.hom b
      have hwb : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (w ≫ C.I.G.act.act b) := ReciprocityTheory.ChartRestriction.G.Chart.isTan_comp hwt _
      have hube : ∀ i, ub i ≫ C.I.G.act.act b =
          ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD z) ≫ ub i := fun i =>
        Over.OverMorphism.ext (C.I.eig τ i b z hz)
      have hubet : ∀ i, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (ub i ≫ C.I.G.act.act b) := fun i =>
        ReciprocityTheory.ChartRestriction.G.Chart.isTan_comp (hubt i) _
      have hubec : ∀ i, tcoord hx _ (hubet i) = z • L (u i) := fun i => by
        rw [ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx (hube i) (hubet i) (ReciprocityTheory.ChartRestriction.G.Chart.isTan_scale z (hubt i)),
          ReciprocityTheory.ChartRestriction.G.Chart.tcoord_scale hx z (hubt i), hubc i]

      have hpb : prodPts g ub ≫ C.I.G.act.act b = prodPts g (fun i => ub i ≫ C.I.G.act.act b) := by
        unfold prodPts
        rw [listProd_comp]
        simp only [Category.assoc]
      obtain ⟨hq, eq⟩ := prodPts_tan hx g (fun i => ub i ≫ C.I.G.act.act b) hubet
      have key : a • tcoord hx _ hwb = a • (z • L v) := by
        have e1 : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD a) ≫ w) ≫ C.I.G.act.act b =
            prodPts g (fun i => ub i ≫ C.I.G.act.act b) := by rw [hsc, hpb]
        have e2 : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.scaleD a) ≫ (w ≫ C.I.G.act.act b) =
            prodPts g (fun i => ub i ≫ C.I.G.act.act b) := by rw [← Category.assoc, e1]
        have e3 := ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx e2 (ReciprocityTheory.ChartRestriction.G.Chart.isTan_scale a hwb) hq
        rw [ReciprocityTheory.ChartRestriction.G.Chart.tcoord_scale hx a hwb, eq] at e3
        rw [e3]
        simp only [hubec, smul_comm (g _) z, ← Finset.smul_sum]
        rw [smul_comm a z, ← map_smul, ← hg, map_sum]
        simp only [map_smul]
      have key' : tcoord hx _ hwb = z • L v := smul_right_injective _ ha key
      apply tan_ext hx hwb (ReciprocityTheory.ChartRestriction.G.Chart.isTan_scale z hwt)
      rw [key', ReciprocityTheory.ChartRestriction.G.Chart.tcoord_scale hx z hwt, hwc]

    have htanw : IsTan (w : epsOver T.V T.V ⟶ C.I.G.G) := (isTan_iff' C.I.G _).2 hwt
    have heigw : IsEigV c io C.I.G τ (w : epsOver T.V T.V ⟶ C.I.G.G) := fun b z hz =>
      congrArg CommaMorphism.left (heig b z hz)
    obtain ⟨g', hg', _⟩ := C.I.basis τ w htanw heigw
    have hw' : w = prodPts g' ub := (isComb_iff' C.I.G _ _ _).1 hg'
    obtain ⟨hp', ep'⟩ := hcombub g'
    have : L v = L (∑ i, g' i • u i) := by
      rw [← hwc, ← ep']
      exact ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx hw' hwt hp'
    rw [hLinj this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨SatLin.exists_basis_of_saturated u hli hsat, hsat⟩

end Main

end Formalism.L2.Pj.SaturatedCharts
