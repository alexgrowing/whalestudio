import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsMono

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
open GlobalTheory.TorusModel GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.TorsionFormCompare

theorem hom_ext_of_isFinite {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (T : Over (Sp R))
    [IsFinite T.hom] {X : Scheme.{0}} [IsAffine X] {f g : T.left ⟶ X}
    (h : ∀ e, thickι (maximalIdeal R) e T ≫ f = thickι (maximalIdeal R) e T ≫ g) : f = g := by
  have : IsAffine T.left := isAffine_of_isAffineHom T.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ T.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  letI : Algebra R Γ(T.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(T.left, ⊤) := hf
  obtain ⟨a, ha⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ f ≫ X.isoSpec.hom)
  obtain ⟨b, hb⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ g ≫ X.isoSpec.hom)
  suffices a = b by
    rw [this, hb, cancel_epi, cancel_mono] at ha
    exact ha.symm
  ext s
  rw [← sub_eq_zero, ← Submodule.mem_bot R, ← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := Γ(T.left, ⊤))
    (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top, Submodule.mem_iInf]
  intro e
  let J : Ideal Γ(T.left, ⊤) := (maximalIdeal R ^ (e + 1)).map φ.hom
  let q : Γ(T.left, ⊤) ⟶ CommRingCat.of (Γ(T.left, ⊤) ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let σ : CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)) ⟶ CommRingCat.of (Γ(T.left, ⊤) ⧸ J) :=
    CommRingCat.ofHom (Ideal.quotientMap J φ.hom Ideal.le_comap_map)
  have w : (Spec.map q ≫ T.left.isoSpec.inv) ≫ T.hom = Spec.map σ ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    exact (congrArg Spec.map (by ext x; rfl)).trans (Spec.map_comp _ _)
  have hl : pullback.lift _ _ w ≫ thickι (maximalIdeal R) e T = Spec.map q ≫ T.left.isoSpec.inv :=
    pullback.lift_fst _ _ _
  have e₁ : a ≫ q = b ≫ q := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ha, hb, ← reassoc_of% hl, ← reassoc_of% hl, reassoc_of% h e]
  have e₂ : a.hom s - b.hom s ∈ J := Ideal.Quotient.eq.1 (congrArg (fun u => u.hom s) e₁)
  refine Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ e)) ?_
  rw [Ideal.smul_top_eq_map]
  exact e₂

theorem mono_torsion : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinite N.hom → GtTors k g₀ → (∀ (T : Over (Sp R)) (g : GtPt P.D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) → FormalEq P.U.toUnifPre x₀ g₀ → Mono x₀ := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ _ ψW k _ N g₀ x₀ hN hg hu hF
  have := hR.1
  obtain ⟨Gt, _, _, Φ, hΦ, -⟩ := exists_represents P.D.toPre
  obtain ⟨c₀, rfl⟩ := (Φ N).surjective g₀
  have hc₀ := (tors_iff hΦ k c₀).1 hg
  have hp := (formalEq_iff _ _ _).1 hF
  have univ : ∀ {T} (x : T ⟶ Gt), x ^ k = 1 → ∃! h : T ⟶ N, h ≫ c₀ = x := fun {T} x hx =>
    (existsUnique_congr fun h => isPull_iff_comp hΦ h c₀ x).1 (hu T _ ((tors_iff hΦ k x).2 hx))
  have tz : ∀ {T} (h : T ⟶ N), (h ≫ c₀) ^ k = 1 := fun h => by rw [← MonObj.comp_pow, hc₀, MonObj.comp_one]
  have canc : ∀ {T} {h h' : T ⟶ N}, h ≫ c₀ = h' ≫ c₀ → h = h' := fun {T h h'} e => (univ _ (tz h')).unique e rfl
  have pt : ∀ {T} (h : T ⟶ N), IsPointOf P.U.toUnifPre (Φ T (h ≫ c₀)) (h ≫ x₀) := fun h => hp.pull h (hΦ.1 _ _ h c₀)
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  have : IsSeparated t.G.hom := t.semi.separated
  have : IsFinite x₀.left := by
    have : IsFinite (x₀.left ≫ t.G.hom) := by rw [Over.w]; exact hN
    exact IsFinite.of_comp _ t.G.hom
  let Q : Over (Sp R) := Over.mk (pullback.fst x₀.left x₀.left ≫ N.hom)
  have : IsFinite Q.hom := inferInstanceAs (IsFinite (pullback.fst x₀.left x₀.left ≫ N.hom))
  let p₁ : Q ⟶ N := Over.homMk (pullback.fst x₀.left x₀.left) rfl
  let p₂ : Q ⟶ N := Over.homMk (pullback.snd x₀.left x₀.left) (by
    show _ = pullback.fst x₀.left x₀.left ≫ N.hom
    rw [← Over.w x₀, pullback.condition_assoc])
  have hx : p₁ ≫ x₀ = p₂ ≫ x₀ := Over.OverMorphism.ext pullback.condition
  have key : p₁.left = p₂.left := hom_ext_of_isFinite Q fun e => by
    have pl : ∀ w : Q ⟶ N, HasCoords P.U.toUnifPre e (Φ _ (fstG (maximalIdeal R) e Q ≫ w ≫ c₀)) (𝟙 _)
        (thickHom (maximalIdeal R) e (w ≫ x₀)) := fun w => by
      rw [← hasCoords_pull (hΦ.1 _ _ (fstG (maximalIdeal R) e Q) (w ≫ c₀)), Category.id_comp]
      exact (isPointOf_iff_thick _ _ _).1 (pt w) e
    have e₁ := (Φ _).injective (eq_of_hasCoords (pl p₁) (hx ▸ pl p₂))
    rw [← Category.assoc, ← Category.assoc] at e₁
    exact congrArg (·.left) (canc e₁)
  have key' : pullback.fst x₀.left x₀.left = pullback.snd x₀.left x₀.left := key
  refine ⟨fun h h' e => Over.OverMorphism.ext ?_⟩
  have e' : h.left ≫ x₀.left = h'.left ≫ x₀.left := congrArg (·.left) e
  rw [← pullback.lift_fst _ _ e', key', pullback.lift_snd]

end GlobalTheory.TorsMono
