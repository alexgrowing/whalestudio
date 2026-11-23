import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabGroupIsoOfGeneric

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem sabMap_exists_iso_pullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {j : S' ⟶ S} (m : SABMap s' s j) :
    ∃ e : s'.G ≅ (Over.pullback j).obj s.G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst s.G.hom j = m.φ ∧
      ∀ a, s'.act.act a ≫ e.hom = e.hom ≫ (Over.pullback j).map (s.act.act a) := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso m.cart (isGrpPullback_pullback s.G _)
  have hφ' : e.hom.left ≫ pullback.fst s.G.hom j = m.φ := hφ
  refine ⟨e, he, hφ', fun a => ?_⟩
  have A : ((Over.pullback j).map (s.act.act a)).left ≫ pullback.fst s.G.hom _ =
        pullback.fst s.G.hom _ ≫ (s.act.act a).left := pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, A]
    rw [reassoc_of% hφ', hφ', m.act a]
  · exact (Over.w _).trans (Over.w _).symm

theorem conj_comp_eq_id_pow {S : Scheme.{0}} {A B A' B' : Over S} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
    (u : A ≅ B) (u' : A' ≅ B') [IsMonHom u.hom] (f : B ⟶ B') (f' : B' ⟶ B) (N : ℕ) (h : f ≫ f' = 𝟙 B ^ N) :
    (u.hom ≫ f ≫ u'.inv) ≫ (u'.hom ≫ f' ≫ u.inv) = 𝟙 A ^ N := by
  have : IsMonHom u.inv := inferInstance
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h, MonObj.pow_comp, MonObj.comp_pow]
  simp

theorem pullback_map_id_pow {S S' : Scheme.{0}} (j : S' ⟶ S) (A : Over S) [GrpObj A] (N : ℕ) :
    (Over.pullback j).map (𝟙 A ^ N) = 𝟙 ((Over.pullback j).obj A) ^ N := by
  induction N with
  | zero => simpa using Functor.map_one (Over.pullback j)
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih]; simp

theorem ext_of_map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {T : CDVR} {x x' : Sp T.Fr ⟶ Xo.X} {G G' : SAB H (Sp T.V)} {t t' : SAB H (Sp T.Fr)}
    (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr)))
    (f : Fib Xo x ⟶ Fib Xo x') [IsMonHom f] (F : G.G ⟶ G'.G)
    (d : t.G ≅ Fib Xo x) (d' : t'.G ≅ Fib Xo x') [IsMonHom d.hom] [IsMonHom d'.hom]
    (e : t.G ≅ (Over.pullback (spMap (algebraMap T.V T.Fr))).obj G.G)
    (e' : t'.G ≅ (Over.pullback (spMap (algebraMap T.V T.Fr))).obj G'.G)
    (hd : d.hom.left ≫ pullback.fst _ _ = m₁.φ) (hd' : d'.hom.left ≫ pullback.fst _ _ = n₁.φ)
    (he : e.hom.left ≫ pullback.fst _ _ = m₂.φ) (he' : e'.hom.left ≫ pullback.fst _ _ = n₂.φ)
    (hF : (Over.pullback (spMap (algebraMap T.V T.Fr))).map F = (e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) :
    Ext m₁ m₂ n₁ n₂ f F := by
  have A : ((Over.pullback (spMap (algebraMap T.V T.Fr))).map F).left ≫ pullback.fst G'.G.hom _ =
        pullback.fst G.G.hom _ ≫ F.left := pullback.lift_fst _ _ _
  have B : (d.hom ≫ f ≫ d'.inv) ≫ e'.hom = e.hom ≫ (Over.pullback (spMap (algebraMap T.V T.Fr))).map F := by
    rw [hF]; simp
  refine ⟨d.hom ≫ f ≫ d'.inv, inferInstance, ?_, fun g g' h1 h2 h3 h4 => ?_⟩
  · rw [← he', ← he, Category.assoc, ← A, ← Category.assoc, ← Category.assoc e.hom.left, ← Over.comp_left,
      ← Over.comp_left, B]
  · obtain rfl : g = d.hom.left := pullback.hom_ext (h1.trans hd.symm) (h2.trans (Over.w d.hom).symm)
    obtain rfl : g' = d'.hom.left := pullback.hom_ext (h3.trans hd'.symm) (h4.trans (Over.w d'.hom).symm)
    have C : d.hom ≫ f = (d.hom ≫ f ≫ d'.inv) ≫ d'.hom := by simp
    exact congrArg (fun k => k.left) C

theorem conj_comm {C : Type*} [Category C] {A B P A' B' P' : C} (e : A ≅ P) (d : A ≅ B) (e' : A' ≅ P') (d' : A' ≅ B')
    (f : B ⟶ B') (a : A ⟶ A) (b : B ⟶ B) (p : P ⟶ P) (a' : A' ⟶ A') (b' : B' ⟶ B') (p' : P' ⟶ P')
    (hd : a ≫ d.hom = d.hom ≫ b) (he : a ≫ e.hom = e.hom ≫ p) (hd' : a' ≫ d'.hom = d'.hom ≫ b')
    (he' : a' ≫ e'.hom = e'.hom ≫ p') (h : b ≫ f = f ≫ b') :
    p ≫ (e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv = ((e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) ≫ p' := by
  have h1 : p ≫ e.inv = e.inv ≫ a := by rw [Iso.eq_inv_comp, ← reassoc_of% he]; simp
  have h2 : b' ≫ d'.inv = d'.inv ≫ a' := by rw [Iso.eq_inv_comp, ← reassoc_of% hd']; simp
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% hd, reassoc_of% h, reassoc_of% h2, he']

theorem exists_ext_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x), IsMonHom f → IsMonHom f' → ∃ (F : G.G ⟶ G'.G) (F' : G'.G ⟶ G.G), IsMonHom F ∧ IsMonHom F' ∧ Ext m₁ m₂ n₁ n₂ f F ∧ Ext n₁ n₂ m₁ m₂ f' F' ∧ (∀ N : ℕ, f ≫ f' = 𝟙 _ ^ N → F ≫ F' = 𝟙 _ ^ N) ∧ (∀ N : ℕ, f' ≫ f = 𝟙 _ ^ N → F' ≫ F = 𝟙 _ ^ N) ∧ (Lin f → ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) ∧ (Lin f' → ∀ a, G'.act.act a ≫ F' = F' ≫ G.act.act a) := by
  intro E _ _ _ H Dw l Xo T x x' G G' t t' m₁ m₂ n₁ n₂ f f' hf hf'
  have hx := semiAbelian_hom_extends_uniquely_dvr T.V T.Fr
  have inj : ∀ (s s' : SAB H (Sp T.V)) (F F' : s.G ⟶ s'.G), IsMonHom F → IsMonHom F' →
      (Over.pullback (spMap (algebraMap T.V T.Fr))).map F = (Over.pullback (spMap (algebraMap T.V T.Fr))).map F' →
        F = F' := by
    intro s s' F F' hF hF' h
    exact (hx s.G s'.G s.semi s'.semi _ inferInstance).unique ⟨hF, rfl⟩ ⟨hF', h.symm⟩
  have hpow : ∀ (s : SAB H (Sp T.V)) (N : ℕ), IsMonHom (𝟙 s.G ^ N) := by
    intro s N
    induction N with
    | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMonHom (toUnit s.G ≫ η[s.G]))
    | succ n ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 s.G ^ n) (𝟙 s.G) ≫ μ[s.G]))
  obtain ⟨d, hd, hdφ, hda⟩ := sabMap_exists_iso_pullback m₁
  obtain ⟨e, he, heφ, hea⟩ := sabMap_exists_iso_pullback m₂
  obtain ⟨d', hd', hdφ', hda'⟩ := sabMap_exists_iso_pullback n₁
  obtain ⟨e', he', heφ', hea'⟩ := sabMap_exists_iso_pullback n₂
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := hx G.G G'.G G.semi G'.semi
    ((e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) (by dsimp; infer_instance)
  obtain ⟨F', ⟨hF', hFf'⟩, -⟩ := hx G'.G G.G G'.semi G.semi
    ((e'.symm ≪≫ d').hom ≫ f' ≫ (e.symm ≪≫ d).inv) (by dsimp; infer_instance)
  have : IsMonHom (e.symm ≪≫ d).hom := by dsimp; infer_instance
  have : IsMonHom (e'.symm ≪≫ d').hom := by dsimp; infer_instance
  refine ⟨F, F', hF, hF', ext_of_map_eq m₁ m₂ n₁ n₂ f F d d' e e' hdφ hdφ' heφ heφ' hFf,
    ext_of_map_eq n₁ n₂ m₁ m₂ f' F' d' d e' e hdφ' hdφ heφ' heφ hFf', fun N h => ?_, fun N h => ?_,
    fun h a => ?_, fun h a => ?_⟩
  · refine inj _ _ _ _ inferInstance (hpow G N) ?_
    rw [Functor.map_comp, hFf, hFf', pullback_map_id_pow]
    exact conj_comp_eq_id_pow _ _ f f' N h
  · refine inj _ _ _ _ inferInstance (hpow G' N) ?_
    rw [Functor.map_comp, hFf, hFf', pullback_map_id_pow]
    exact conj_comp_eq_id_pow _ _ f' f N h
  · have := G.act.hom a
    have := G'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [Functor.map_comp, Functor.map_comp, hFf]
    exact conj_comm e d e' d' f _ _ _ _ _ _ (hda a) (hea a) (hda' a) (hea' a) (h a)
  · have := G.act.hom a
    have := G'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [Functor.map_comp, Functor.map_comp, hFf']
    exact conj_comm e' d' e d f' _ _ _ _ _ _ (hda' a) (hea' a) (hda a) (hea a) (h a)

end GlobalTheory.HkIntegral
