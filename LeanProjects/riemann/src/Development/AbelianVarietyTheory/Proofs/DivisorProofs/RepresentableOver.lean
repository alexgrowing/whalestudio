import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentableOfZariskiSheafOpenChartsLargeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.RepOver

noncomputable def coverOf {T : Scheme.{0}} {J : Type} (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T)
    (hz : ∀ i, IsOpenImmersion (z i)) (hc : ∀ p : T, ∃ i, p ∈ Set.range (z i)) : T.OpenCover :=
  Scheme.Cover.mkOfCovers J Z z (fun p => hc p) hz

theorem hom_eq_of_local {T S : Scheme.{0}} (t t' : T ⟶ S)
    (h : ∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧
      z ≫ t = z ≫ t') : t = t' := by
  choose Z z hz hp he using h
  exact Scheme.Cover.hom_ext (coverOf Z z hz (fun p => ⟨p, hp p⟩)) t t' he

theorem exists_glue {T S : Scheme.{0}} {J : Type} (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T)
    (hz : ∀ i, IsOpenImmersion (z i)) (hc : ∀ p : T, ∃ i, p ∈ Set.range (z i))
    (t : ∀ i, Z i ⟶ S)
    (ht : ∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k →
      a ≫ t i = b ≫ t k) : ∃ t₀ : T ⟶ S, ∀ i, z i ≫ t₀ = t i :=
  ⟨Scheme.Cover.glueMorphisms (coverOf Z z hz hc) t
      (fun i k => ht i k _ _ _ pullback.condition),
    fun i => Scheme.Cover.ι_glueMorphisms (coverOf Z z hz hc) t _ i⟩

variable {S : Scheme.{0}} (F : (Over S)ᵒᵖ ⥤ Type 1)

theorem map_map {X Y Z : Over S} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a.left ≫ b.left = c.left)
    (d : F.obj (op Z)) : F.map a.op (F.map b.op d) = F.map c.op d := by
  have : c = a ≫ b := Over.OverMorphism.ext (by simpa using h.symm)
  subst this
  simp

theorem sig_eq {Y : Scheme.{0}} (r r' : Y ⟶ S) (h : r = r') (e : F.obj (op (Over.mk r)))
    (e' : F.obj (op (Over.mk r'))) (c : Over.mk r ⟶ Over.mk r') (hc : c.left = 𝟙 Y)
    (he : F.map c.op e' = e) :
    (⟨r, e⟩ : Σ t : Y ⟶ S, F.obj (op (Over.mk t))) = ⟨r', e'⟩ := by
  subst h
  have : c = 𝟙 _ := Over.OverMorphism.ext hc
  subst this
  subst he
  simp

noncomputable def tot : Scheme.{0}ᵒᵖ ⥤ Type 1 where
  obj X := Σ t : X.unop ⟶ S, F.obj (op (Over.mk t))
  map {X Y} f := TypeCat.ofHom fun y =>
    ⟨f.unop ≫ y.1, F.map (Over.homMk f.unop rfl : Over.mk (f.unop ≫ y.1) ⟶ Over.mk y.1).op y.2⟩
  map_id X := by
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    exact sig_eq F _ _ (Category.id_comp _) _ _ _ rfl rfl
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    refine sig_eq F _ _ (Category.assoc _ _ _) _ _ (Over.homMk (𝟙 _) (by simp)) rfl ?_
    refine (map_map F _ _ (Over.homMk g.unop (Category.assoc _ _ _).symm) (by simp) _).trans ?_
    exact map_map F _ _ _ (by simp) _

def el {V : Over S} (v : F.obj (op V)) : (tot F).obj (op V.left) := ⟨V.hom, v⟩

theorem el_inj {V : Over S} {v v' : F.obj (op V)} (h : el F v = el F v') : v = v' :=
  eq_of_heq (Sigma.mk.inj h).2

theorem map_el {Y V : Over S} (a : Y ⟶ V) (v : F.obj (op V)) :
    (tot F).map a.left.op (el F v) = el F (F.map a.op v) :=
  sig_eq F (a.left ≫ V.hom) Y.hom (Over.w a) _ _ (Over.homMk (𝟙 _) (by simp)) rfl
    (map_map F _ _ _ (by simp) _)

theorem w_of_map_el {Y V : Over S} {a : Y.left ⟶ V.left} {v : F.obj (op V)} {y : F.obj (op Y)}
    (h : (tot F).map a.op (el F v) = el F y) : a ≫ V.hom = Y.hom :=
  congrArg Sigma.fst h

theorem w_of_map_eq {Y : Scheme.{0}} {V V' : Over S} {a : Y ⟶ V.left} {b : Y ⟶ V'.left}
    {v : F.obj (op V)} {v' : F.obj (op V')}
    (h : (tot F).map a.op (el F v) = (tot F).map b.op (el F v')) : a ≫ V.hom = b ≫ V'.hom :=
  congrArg Sigma.fst h

theorem map_eq_iff {Y V V' : Over S} (a : Y ⟶ V) (b : Y ⟶ V')
    (v : F.obj (op V)) (v' : F.obj (op V')) :
    (tot F).map a.left.op (el F v) = (tot F).map b.left.op (el F v') ↔
      F.map a.op v = F.map b.op v' := by
  rw [map_el, map_el]
  exact ⟨el_inj F, fun h => by rw [h]⟩

end GlobalTheory.RepOver

open GlobalTheory.RepOver in

theorem GlobalTheory.RepOver.representable_over : ∀ (S : Scheme.{0}) (F : (Over S)ᵒᵖ ⥤ Type 1), (∀ (T : Over S) (y y' : F.obj (op T)), (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Over S) (J : Type) (Z : J → Over S) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i).left) → (∀ p : T.left, ∃ i, p ∈ Set.range (z i).left) → (∀ (i k : J) (Y : Over S) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Over S) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Over S) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Over S) (y : F.obj (op T)), ∃ W : T.left.Opens, ∀ (Y : Over S) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a.left q ∈ W) → (∀ (T : Over S) (y : F.obj (op T)) (p : T.left), ∃ (i : Ix) (Y : Over S) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a.left ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Over S) (x₀ : F.obj (op B)), (∀ (T : Over S) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) ∧ ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro S F hsep hglue Ix U x hmono hopen hcov
  refine Exists.elim (GlobalTheory.T.representable_of_zariski_sheaf_open_charts_large (tot F) ?_ ?_ Ix (fun i => (U i).left)
    (fun i => el F (x i)) ?_ ?_ ?_) ?_
  rotate_right
  · rintro B ⟨⟨tB, dB⟩, huniv, j, hj, hc, hx⟩
    refine ⟨Over.mk tB, dB, fun T y => ?_, fun i => Over.homMk (j i)
      (w_of_map_el F (V := Over.mk tB) (hx i)), hj, hc, fun i => ?_⟩
    · obtain ⟨g, hg, hu⟩ := huniv T.left (el F y)
      refine ⟨Over.homMk g (w_of_map_el F (V := Over.mk tB) hg), ?_, fun g' hg' => ?_⟩
      · exact el_inj F ((map_el F _ dB).symm.trans hg)
      · exact Over.OverMorphism.ext (hu g'.left ((map_el F g' dB).trans (congrArg (el F) hg')))
    · exact el_inj F ((map_el F _ dB).symm.trans (hx i))
  · rintro T ⟨t, d⟩ ⟨t', d'⟩ h
    obtain rfl : t = t' := hom_eq_of_local t t' fun p => by
      obtain ⟨Z, z, hz, hp, he⟩ := h p
      exact ⟨Z, z, hz, hp, congrArg Sigma.fst he⟩
    obtain rfl : d = d' := hsep (Over.mk t) d d' fun p => by
      obtain ⟨Z, z, hz, hp, he⟩ := h p
      exact ⟨Over.mk (z ≫ t), Over.homMk z rfl, hz, hp, (map_eq_iff F _ _ d d').1 he⟩
    rfl
  · intro T J Z z y hz hc hy
    obtain ⟨t, ht⟩ := exists_glue Z z hz hc (fun i => (y i).1)
      (fun i k Y a b hab => congrArg Sigma.fst (hy i k Y a b hab))
    obtain ⟨d, hd⟩ := hglue (Over.mk t) J (fun i => Over.mk (y i).1)
      (fun i => Over.homMk (z i) (ht i)) (fun i => (y i).2) hz hc
      (fun i k Y a b hab => (map_eq_iff F a b _ _).1
        (hy i k Y.left a.left b.left (congrArg (fun c => c.left) hab)))
    exact ⟨⟨t, d⟩, fun i => (map_el F (Y := Over.mk (y i).1) (V := Over.mk t)
      (Over.homMk (z i) (ht i)) d).trans (congrArg (el F) (hd i))⟩
  · intro i Y u u' h
    have := hmono i (Over.mk (u ≫ (U i).hom)) (Over.homMk u rfl)
      (Over.homMk u' (w_of_map_eq F h).symm) ((map_eq_iff F _ _ _ _).1 h)
    exact congrArg (fun c => c.left) this
  · rintro i T ⟨t, d⟩
    obtain ⟨W, hW⟩ := hopen i (Over.mk t) d
    refine ⟨W, fun Y a => Iff.trans ?_ (hW (Over.mk (a ≫ t)) (Over.homMk a rfl))⟩
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨Over.homMk u (w_of_map_eq F (V := Over.mk t) hu).symm, (map_eq_iff F _ _ _ _).1 hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨u.left, (map_eq_iff F _ _ _ _).2 hu⟩
  · rintro T ⟨t, d⟩ p
    obtain ⟨i, Y, a, u, hp, h⟩ := hcov (Over.mk t) d p
    exact ⟨i, Y.left, a.left, u.left, hp, (map_eq_iff F _ _ _ _).2 h⟩
