import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.DetExtendZero

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

theorem dual_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (Chart.dualMapR (g.comp f)) = spMap (Chart.dualMapR g) ≫ spMap (Chart.dualMapR f) := by
  rw [← spMap_comp]
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR]

theorem dual_id (R : Type) [CommRing R] : spMap (Chart.dualMapR (RingHom.id R)) = 𝟙 _ := by
  rw [← spMap_id]
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR]

section Tangent

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R']

def epsMap (g : R →+* R') (x : Sp R ⟶ S) : FramedFlatCoordinates.epsAt (spMap g ≫ x) ⟶ FramedFlatCoordinates.epsAt x :=
  Over.homMk (spMap (Chart.dualMapR g)) (by
    have := LieCombBaseChange.dualMap_over g
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) this).trans (Category.assoc _ _ _)))

theorem comb_map (g : R →+* R') {x : Sp R ⟶ S} {x' : Sp R' ⟶ S} (hx : x' = spMap g ≫ x) {n : ℕ} {c : Fin n → R}
    {v : Fin n → (Sp (DualNumber R) ⟶ G.left)} {w : FramedFlatCoordinates.epsAt x ⟶ G} (h : FramedFlatCoordinates.IsCombination x c v w)
    {w' : FramedFlatCoordinates.epsAt x' ⟶ G} (hw : w'.left = spMap (Chart.dualMapR g) ≫ w.left) :
    FramedFlatCoordinates.IsCombination x' (fun i => g (c i)) (fun i => spMap (Chart.dualMapR g) ≫ v i) w' := by
  subst hx
  obtain ⟨u, hu, rfl⟩ := h
  let F : (FramedFlatCoordinates.epsAt x ⟶ G) →* (FramedFlatCoordinates.epsAt (spMap g ≫ x) ⟶ G) :=
    ⟨⟨fun u => epsMap g x ≫ u, MonObj.comp_one _⟩, fun a b => MonObj.comp_mul _ _ _⟩
  refine ⟨fun i => F (u i), fun i => ?_, ?_⟩
  · refine (congrArg (spMap (Chart.dualMapR g) ≫ ·) (hu i)).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ v i) (LieCombBaseChange.dualMap_epsScale g (c i))).trans (Category.assoc _ _ _))
  · have : w' = F (List.ofFn u).prod := Over.OverMorphism.ext hw
    rw [this, map_list_prod, List.map_ofFn]; rfl

theorem comb_one {x : Sp R ⟶ S} {n : ℕ} {v : Fin n → (FramedFlatCoordinates.epsAt x ⟶ G)}
    (hv : ∀ i, spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (v i).left = (1 : Over.mk x ⟶ G).left) (i : Fin n) :
    FramedFlatCoordinates.IsCombination x ((1 : Matrix (Fin n) (Fin n) R) i) (fun k => (v k).left) (v i) := by
  classical
  refine ⟨fun k => if k = i then v i else 1, fun k => ?_, ?_⟩
  · by_cases hk : k = i
    · subst hk
      have : epsScaleR (1 : R) = RingHom.id _ := by
        refine RingHom.ext fun x => ?_
        ext <;> simp [epsScaleR]
      simp only [if_true, Matrix.one_apply_eq, this, spMap_id]
      exact (Category.id_comp _).symm
    · have : epsScaleR (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
        refine RingHom.ext fun x => ?_
        ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
      simp only [if_neg hk, Matrix.one_apply_ne (Ne.symm hk), this, spMap_comp]
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (spMap (algebraMap R (DualNumber R)) ≫ ·) (hv k)).symm
      let D : FramedFlatCoordinates.epsAt x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R (DualNumber R))) rfl
      exact (congrArg CommaMorphism.left (MonObj.comp_one D)).symm
  · rw [List.ofFn_eq_map, List.prod_map_eq_pow_single i _ (fun a h _ => if_neg h)]
    simp

end Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem exists_basis {S : Scheme.{0}} {T : SAB H S} {c : Coeff l} (hT : EigStable T c) {R R' : Type} [CommRing R]
    [CommRing R'] (g : R →+* R') {j : c.F →+* R} {x : Sp R ⟶ S} {x' : Sp R' ⟶ S} (hx : x' = spMap g ≫ x)
    {τ : E →+* ℂ} {m : ℕ} {v : Fin m → (FramedFlatCoordinates.epsAt x ⟶ T.G)}
    (hv : FramedFlatCoordinates.IsEigenBasis T.act x (FramedFlatCoordinates.chr c τ j) v) :
    ∃ v' : Fin m → (FramedFlatCoordinates.epsAt x' ⟶ T.G), FramedFlatCoordinates.IsEigenBasis T.act x' (FramedFlatCoordinates.chr c τ (g.comp j)) v' ∧
      ∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left := by
  subst hx
  exact ⟨fun i => epsMap g x ≫ v i, hT R R' g j x τ m v _ hv fun _ => rfl, fun _ => rfl⟩

variable {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {U : (Xo.XF c).Opens} {τ : E →+* ℂ}

def toGen (Y : Model Xo c (RingHom.id c.F)) : Y.X ⟶ FramedFlatCoordinates.genFibre Y :=
  pullback.lift (𝟙 _) Y.s (by rw [spMap_id, Category.id_comp, Category.comp_id])

theorem toGen_fst : toGen Y ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _

theorem toGen_snd : toGen Y ≫ pullback.snd _ _ = Y.s := pullback.lift_snd _ _ _

theorem fst_toGen : pullback.fst _ _ ≫ toGen Y = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, toGen_fst, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, toGen_snd, Category.id_comp, pullback.condition]
    exact (congrArg (_ ≫ ·) (spMap_id _)).trans (Category.comp_id _)

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

def IsAbove (g : R →+* R') (φ : c.F →+* R) (x : Sp R ⟶ Y.X) (v : Fin Dw.p → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G))
    (w : Fin Dw.q → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)) {j : c.F →+* R'} (a : FramedFlatCoordinates.Framed Y U τ R' j) : Prop :=
  g.comp φ = j ∧ a.x = spMap g ≫ x ≫ toGen Y ∧ (∀ i, (a.v i).left = spMap (Chart.dualMapR g) ≫ (v i).left) ∧
    ∀ i, (a.w i).left = spMap (Chart.dualMapR g) ≫ (w i).left

def Misses (U : (Xo.XF c).Opens) (g : R →+* R') (x : Sp R ⟶ Y.X) : Prop :=
  ∀ z, (x ≫ toGen Y) (spMap g z) ∉ FramedFlatCoordinates.compactification Y U

theorem exists_above (hT : EigStable Y.t c) (g : R →+* R') {φ : c.F →+* R} {x : Sp R ⟶ Y.X}
    {v : Fin Dw.p → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)} {w : Fin Dw.q → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)}
    (h : RamifiedPlacesSplitEigen.IsFrame Y τ φ x v w) (hg : ∀ z, (x ≫ toGen Y) (spMap g z) ∈ FramedFlatCoordinates.compactification Y U) :
    ∃ a : FramedFlatCoordinates.Framed Y U τ R' (g.comp φ), IsAbove g φ x v w a := by
  have hx : (spMap g ≫ x ≫ toGen Y) ≫ pullback.fst _ _ = spMap g ≫ x := by
    rw [Category.assoc, Category.assoc, toGen_fst, Category.comp_id]
  obtain ⟨v', hv', ev⟩ := exists_basis hT g (j := φ) (τ := τ) hx h.2.1
  obtain ⟨w', hw', ew⟩ := exists_basis hT g (j := φ) (τ := conjEmb τ) hx h.2.2
  refine ⟨⟨spMap g ≫ x ≫ toGen Y, ?_, ?_, v', w', hv', hw'⟩, rfl, rfl, ev, ew⟩
  · rw [Category.assoc, Category.assoc, toGen_snd, h.1, spMap_comp φ g, RingHom.comp_id]
  · rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hg z

theorem exists_idem (hU : IsOpen (FramedFlatCoordinates.compactification Y U)) (x : Sp R ⟶ Y.X) :
    ∃ e : R, IsIdempotentElem e ∧
      ∀ z : PrimeSpectrum R, (x ≫ toGen Y) z ∈ FramedFlatCoordinates.compactification Y U ↔ e ∉ z.asIdeal := by
  have hc : IsClopen (FramedFlatCoordinates.compactification Y U) := ⟨isClosed_closure, hU⟩
  obtain ⟨e, he, h⟩ := PrimeSpectrum.isClopen_iff.1 (hc.preimage (x ≫ toGen Y).continuous)
  exact ⟨e, he, fun z => Set.ext_iff.1 h z⟩

theorem mem_of_one_sub {e : R} {g : R →+* R'} (hg : g (1 - e) = 0) (z : Sp R') :
    e ∉ PrimeSpectrum.asIdeal (R := R) (spMap g z) := fun h => by
  have h1 : g e ∈ PrimeSpectrum.asIdeal (R := R') z := h
  rw [map_sub, map_one, sub_eq_zero] at hg
  exact (PrimeSpectrum.isPrime (R := R') z).ne_top ((Ideal.eq_top_iff_one _).2 (hg ▸ h1))

theorem separate (hT : EigStable Y.t c) (hU : IsOpen (FramedFlatCoordinates.compactification Y U)) {φ : c.F →+* R} {x : Sp R ⟶ Y.X}
    {v : Fin Dw.p → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)} {w : Fin Dw.q → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)}
    (h : RamifiedPlacesSplitEigen.IsFrame Y τ φ x v w) {s t : R}
    (h₁ : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (a : FramedFlatCoordinates.Framed Y U τ R' (g.comp φ)),
      IsAbove g φ x v w a → g s = g t)
    (h₂ : ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Misses U g x → g s = g t) : s = t := by
  obtain ⟨e, he, hz⟩ := exists_idem hU x
  obtain ⟨a, ha⟩ := exists_above (U := U) hT (Ideal.Quotient.mk (Ideal.span {1 - e})) h fun z =>
    (hz _).2 (mem_of_one_sub (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)) z)
  have e₁ := h₁ _ _ a ha
  have e₂ := h₂ _ (Ideal.Quotient.mk (Ideal.span {e})) fun z hm => (hz _).1 hm (by
    change Ideal.Quotient.mk (Ideal.span {e}) e ∈ PrimeSpectrum.asIdeal (R := R ⧸ Ideal.span {e}) z
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
    exact zero_mem _)
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at e₁ e₂
  obtain ⟨b, hb⟩ := e₁
  obtain ⟨b', hb'⟩ := e₂
  have he' : e * e = e := he
  linear_combination (-e) * hb - (1 - e) * hb' - (b + b') * he'

def IsExtValue (sig : FramedFlatCoordinates.Rule Y U τ) (φ : c.F →+* R) (x : Sp R ⟶ Y.X)
    (v : Fin Dw.p → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)) (w : Fin Dw.q → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)) (r : R) : Prop :=
  (∀ (R' : Type) [CommRing R'] (g : R →+* R') (j : c.F →+* R') (a : FramedFlatCoordinates.Framed Y U τ R' j),
    IsAbove g φ x v w a → g r = sig R' j a) ∧
  ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Misses U g x → g r = 0

theorem exists_extValue (hT : EigStable Y.t c) (hU : IsOpen (FramedFlatCoordinates.compactification Y U))
    {sig : FramedFlatCoordinates.Rule Y U τ} (hs : sig ∈ FramedFlatCoordinates.sections Y U τ) {φ : c.F →+* R} {x : Sp R ⟶ Y.X}
    {v : Fin Dw.p → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)} {w : Fin Dw.q → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)}
    (h : RamifiedPlacesSplitEigen.IsFrame Y τ φ x v w) : ∃ r, IsExtValue sig φ x v w r := by
  obtain ⟨e, he, hz⟩ := exists_idem hU x
  obtain ⟨a, ha⟩ := exists_above (U := U) hT (Ideal.Quotient.mk (Ideal.span {1 - e})) h fun z =>
    (hz _).2 (mem_of_one_sub (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)) z)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (sig _ _ a)
  refine ⟨e * r, fun R' _ g j a' ha' => ?_, fun R' _ g hg => ?_⟩
  · have hu : IsUnit (g e) := by
      by_contra hn
      obtain ⟨m, hm, hem⟩ := exists_max_ideal_of_mem_nonunits (a := g e) hn
      let z : Sp R' := (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
      have := a'.x_mem ⟨z, rfl⟩
      rw [ha'.2.1, Scheme.Hom.comp_apply] at this
      exact (hz _).1 this hem
    have h1 : g e = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit hu).1 (he.map g)
    let g' : R ⧸ Ideal.span {1 - e} →+* R' := Ideal.Quotient.lift _ g fun b hb => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      simp [h1]
    have hg : g = g'.comp (Ideal.Quotient.mk _) := rfl
    have hc : FramedFlatCoordinates.IsChange a a' g' 1 1 := by
      refine ⟨ha'.1, ?_, fun i => ?_, fun i => ?_⟩
      · rw [ha'.2.1, ha.2.1, hg, spMap_comp, Category.assoc]
      · have := comb_one (fun k => (a'.v_basis.1 k).1) i
        convert this using 2 with k
        rw [ha'.2.2.1, ha.2.2.1, hg, dual_comp, Category.assoc]
      · have := comb_one (fun k => (a'.w_basis.1 k).1) i
        convert this using 2 with k
        rw [ha'.2.2.2, ha.2.2.2, hg, dual_comp, Category.assoc]
    have := hs _ _ _ _ a a' g' 1 1 hc
    simp only [Matrix.det_one, _root_.mul_one] at this
    rw [this, ← hr, map_mul, h1, _root_.one_mul]
    rfl
  · have hn : IsNilpotent (g e) := by
      rw [nilpotent_iff_mem_prime]
      intro J hJ
      by_contra hm
      exact hg (⟨J, hJ⟩ : PrimeSpectrum R') ((hz _).2 hm)
    rw [map_mul, (he.map g).eq_zero_of_isNilpotent hn, zero_mul]

theorem extValue_unique (hT : EigStable Y.t c) (hU : IsOpen (FramedFlatCoordinates.compactification Y U))
    {sig : FramedFlatCoordinates.Rule Y U τ} {φ : c.F →+* R} {x : Sp R ⟶ Y.X}
    {v : Fin Dw.p → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)} {w : Fin Dw.q → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)}
    (h : RamifiedPlacesSplitEigen.IsFrame Y τ φ x v w) {r r' : R} (hr : IsExtValue sig φ x v w r) (hr' : IsExtValue sig φ x v w r') :
    r = r' :=
  separate hT hU h (fun _ _ g a ha => (hr.1 _ g _ a ha).trans (hr'.1 _ g _ a ha).symm)
    fun _ _ g hg => (hr.2 _ g hg).trans (hr'.2 _ g hg).symm

theorem IsExtValue.map {sig : FramedFlatCoordinates.Rule Y U τ} {φ : c.F →+* R} {x : Sp R ⟶ Y.X}
    {v : Fin Dw.p → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)} {w : Fin Dw.q → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)} {r : R}
    (hr : IsExtValue sig φ x v w r) (g : R →+* R') {v' : Fin Dw.p → (FramedFlatCoordinates.epsAt (spMap g ≫ x) ⟶ Y.t.G)}
    {w' : Fin Dw.q → (FramedFlatCoordinates.epsAt (spMap g ≫ x) ⟶ Y.t.G)}
    (hv : ∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left)
    (hw : ∀ i, (w' i).left = spMap (Chart.dualMapR g) ≫ (w i).left) :
    IsExtValue sig (g.comp φ) (spMap g ≫ x) v' w' (g r) := by
  refine ⟨fun R'' _ g' j a ha => hr.1 _ (g'.comp g) j a ⟨ha.1, ?_, fun i => ?_, fun i => ?_⟩,
    fun R'' _ g' hg => hr.2 _ (g'.comp g) fun z => ?_⟩
  · rw [ha.2.1, spMap_comp, Category.assoc, Category.assoc]
  · rw [ha.2.2.1, hv, dual_comp, Category.assoc]
  · rw [ha.2.2.2, hw, dual_comp, Category.assoc]
  · have := hg z
    rw [Category.assoc, Scheme.Hom.comp_apply (spMap g)] at this
    rwa [spMap_comp, Scheme.Hom.comp_apply (spMap g')]

theorem IsExtValue.change (hT : EigStable Y.t c) (hU : IsOpen (FramedFlatCoordinates.compactification Y U))
    {sig : FramedFlatCoordinates.Rule Y U τ} (hs : sig ∈ FramedFlatCoordinates.sections Y U τ) {φ : c.F →+* R} {x : Sp R ⟶ Y.X}
    {v v' : Fin Dw.p → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)} {w w' : Fin Dw.q → (FramedFlatCoordinates.epsAt x ⟶ Y.t.G)}
    {M : Matrix (Fin Dw.p) (Fin Dw.p) R} {N : Matrix (Fin Dw.q) (Fin Dw.q) R}
    (h : RamifiedPlacesSplitEigen.IsFrame Y τ φ x v w) (h' : RamifiedPlacesSplitEigen.IsFrame Y τ φ x v' w') (hM : ∀ i, RamifiedPlacesSplitEigen.IsCombAt (M i) v (v' i))
    (hN : ∀ i, RamifiedPlacesSplitEigen.IsCombAt (N i) w (w' i)) {r r' : R} (hr : IsExtValue sig φ x v w r)
    (hr' : IsExtValue sig φ x v' w' r') : r * N.det = r' * M.det := by
  refine separate hT hU h (fun R' _ g a ha => ?_) fun R' _ g hg => by
    rw [map_mul, map_mul, hr.2 _ g hg, hr'.2 _ g hg, zero_mul, zero_mul]
  obtain ⟨a', ha'⟩ := exists_above (U := U) hT g h' fun z => by
    have := a.x_mem ⟨z, rfl⟩
    rwa [ha.2.1, Scheme.Hom.comp_apply] at this
  have hx : a'.x ≫ pullback.fst _ _ = spMap g ≫ x := by
    rw [ha'.2.1, Category.assoc, Category.assoc, toGen_fst, Category.comp_id]
  have hc : FramedFlatCoordinates.IsChange a a' (RingHom.id _) (g.mapMatrix M) (g.mapMatrix N) := by
    refine ⟨rfl, ?_, fun i => ?_, fun i => ?_⟩
    · rw [ha'.2.1, ha.2.1, spMap_id, Category.id_comp]
    · have := comb_map g hx (v := fun k => (v k).left) (hM i) (ha'.2.2.1 i)
      convert this using 2 with k k
      · rfl
      · rw [dual_id, ha.2.2.1]; exact Category.id_comp _
    · have := comb_map g hx (v := fun k => (w k).left) (hN i) (ha'.2.2.2 i)
      convert this using 2 with k k
      · rfl
      · rw [dual_id, ha.2.2.2]; exact Category.id_comp _
  have := hs _ _ _ _ a a' _ _ _ hc
  rw [map_mul, map_mul, hr.1 _ g _ a ha, hr'.1 _ g _ a' ha', RingHom.map_det, RingHom.map_det]
  exact this.symm

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ), EigStable Y.t c → IsOpen (FramedFlatCoordinates.compactification Y U) → ∀ sig ∈ FramedFlatCoordinates.sections Y U τ, ∃ f : RamifiedPlacesSplitEigen.Rule Y, RamifiedPlacesSplitEigen.IsDetSection Y τ f ∧ ∀ (R : Type) [CommRing R] (j : c.F →+* R) (a : FramedFlatCoordinates.Framed Y U τ R j), f R j (a.x ≫ pullback.fst _ _) a.v a.w = sig R j a := by
  intro E _ _ _ H Dw l Xo c Y U τ hT hU sig hs
  let f : RamifiedPlacesSplitEigen.Rule Y := fun R _ φ x v w => @Classical.epsilon R ⟨0⟩ (IsExtValue sig φ x v w)
  have hf : ∀ (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Y.X) v w, RamifiedPlacesSplitEigen.IsFrame Y τ φ x v w →
      IsExtValue sig φ x v w (f R φ x v w) := fun R _ φ x v w h =>
    Classical.epsilon_spec_aux ⟨0⟩ _ (exists_extValue hT hU hs h)
  refine ⟨f, ⟨fun R _ φ x v v' w w' M N h h' hM hN => ?_, fun R R' _ _ g φ x v w v' w' h h' hv hw => ?_⟩,
    fun R _ j a => ?_⟩
  · exact IsExtValue.change hT hU hs h h' hM hN (hf _ _ _ _ _ h) (hf _ _ _ _ _ h')
  · exact extValue_unique hT hU h' (hf _ _ _ _ _ h') ((hf _ _ _ _ _ h).map g hv hw)
  · have h : RamifiedPlacesSplitEigen.IsFrame Y τ j (a.x ≫ pullback.fst _ _) a.v a.w := by
      refine ⟨?_, a.v_basis, a.w_basis⟩
      rw [Category.assoc, pullback.condition, ← Category.assoc, a.x_over, spMap_comp]
    refine (hf _ _ _ _ _ h).1 R (RingHom.id R) j a ⟨rfl, ?_, fun i => ?_, fun i => ?_⟩
    · rw [spMap_id R, Category.id_comp, Category.assoc, fst_toGen, Category.comp_id]
    · rw [dual_id]; exact (Category.id_comp _).symm
    · rw [dual_id]; exact (Category.id_comp _).symm

end GlobalTheory.DetExtendZero
