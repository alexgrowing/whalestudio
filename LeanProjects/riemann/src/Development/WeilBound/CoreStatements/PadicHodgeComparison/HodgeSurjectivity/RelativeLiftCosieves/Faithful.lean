import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto.EquivalenceOnIso

open Pb HT

variable {K : Type} [CommRing K] {W Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}

theorem obj_ext {C : Type 1} [Category.{0} C] {P : ObjectProperty C} (a b : P.FullSubcategory) (h : a.obj = b.obj) :
    a = b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  subst h
  rfl

def preim [Mono i] {T₁ T₂ : Thick (smFun W (i ≫ q))}
    (g : (smS (p := q) i rfl).G.obj T₁ ⟶ (smS (p := q) i rfl).G.obj T₂) : T₁ ⟶ T₂ :=
  mkH (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) g.φ (fun r => g.comm r) g.dp g.hle (by
    have e := g.pt
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : PtOver Z q (Ideal.Quotient.mk (⊥ : Ideal K)) (T₂.B ⧸ T₂.J) => z.1.1) e
    · apply (cancel_mono i).1
      exact (Category.assoc _ _ _).trans
        (congrArg (fun z : PtOver Z q (Ideal.Quotient.mk (⊥ : Ideal K)) (T₂.B ⧸ T₂.J) => z.1.2) e))

def lift (T : Thick (smFun Z q)) (w : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ W)
    (hw : w ≫ i = pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T) :
    Thick (smFun W (i ≫ q)) :=
  mkT (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) T.B T.i T.J T.δ T.adm T.compat
    ⟨((show PtOver Z q (Ideal.Quotient.mk (⊥ : Ideal K)) (T.B ⧸ T.J) from T.y).1.1, w),
      (Category.assoc w i q).symm.trans ((congrArg (· ≫ q) hw).trans
        (show PtOver Z q (Ideal.Quotient.mk (⊥ : Ideal K)) (T.B ⧸ T.J) from T.y).2)⟩
    T.w

theorem G_lift (T : Thick (smFun Z q)) (w : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ W)
    (hw : w ≫ i = pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T) :
    (smS (p := q) i rfl).G.obj (lift T w hw) = T := by
  have hs1 := s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T
  obtain ⟨B, i₀, J, δ, adm, compat, α, y, inα, w₀, x, v, s, hx, hs, hv⟩ := T
  change Thick.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
  congr 1
  all_goals first
    | exact RingHom.comp_id _
    | (funext j; exact (j : Empty).elim)
    | (apply Subtype.ext; apply Prod.ext; rfl; exact hw)
    | (have h1 : s = 1 := hs1
       refine Eq.trans ?_ h1.symm
       show (1 : Bˣ) ^ 1 * (Units.map _ (1 : Kˣ))⁻¹ = 1
       simp)

theorem essSurj [Mono i] (U : ObjectProperty (Thick (smFun Z q))) (U' : ObjectProperty (Thick (smFun W (i ≫ q))))
    (h : ∀ T, U' T → (U ⊓ On q i) ((smS i rfl).G.obj T)) (hU : ∀ T, U ((smS i rfl).G.obj T) → U' T) (a : ℕ) :
    (morV i rfl a h).G.EssSurj where
  mem_essImage Y := by
    have hY : (U ⊓ On q i) Y.obj := Y.property
    obtain ⟨w, hw⟩ := hY.2
    have hY' : U' (lift Y.obj w hw) := hU _ (by rw [G_lift]; exact hY.1)
    exact ⟨⟨lift Y.obj w hw, hY'⟩, ⟨eqToIso (obj_ext _ _ (G_lift Y.obj w hw))⟩⟩

theorem full [Mono i] {U : ObjectProperty (Thick (smFun Z q))} {U' : ObjectProperty (Thick (smFun W (i ≫ q)))}
    (h : ∀ T, U' T → (U ⊓ On q i) ((smS i rfl).G.obj T)) (a : ℕ) : (morV i rfl a h).G.Full where
  map_surjective {X Y} g := ⟨ObjectProperty.homMk (preim (T₁ := X.obj) (T₂ := Y.obj) g.hom),
    ObjectProperty.hom_ext _ (hom_ext rfl)⟩

theorem faithful {U : ObjectProperty (Thick (smFun Z q))} {U' : ObjectProperty (Thick (smFun W (i ≫ q)))}
    (h : ∀ T, U' T → (U ⊓ On q i) ((smS i rfl).G.obj T)) (a : ℕ) : (morV i rfl a h).G.Faithful where
  map_injective {X Y} {f g} e := ObjectProperty.hom_ext _ (hom_ext (congrArg (fun k => k.hom.φ) e))

theorem tau_bij {U : ObjectProperty (Thick (smFun Z q))} {U' : ObjectProperty (Thick (smFun W (i ≫ q)))}
    (h : ∀ T, U' T → (U ⊓ On q i) ((smS i rfl).G.obj T)) (a : ℕ) (T : U'.FullSubcategory) :
    Function.Bijective ((morV i rfl a h).τ T) := by
  have hτ : ∀ x, ((morV i rfl a h).τ T x).1 = x.1 := by
    intro x
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  exact ⟨fun x y e => Subtype.ext ((hτ x).symm.trans ((congrArg Subtype.val e).trans (hτ y))),
    fun y => ⟨y, Subtype.ext (hτ y)⟩⟩

end CrystallineSemistableComparison.Onto.EquivalenceOnIso

namespace CrystallineSemistableComparison.Onto

open EquivalenceOnIso in

theorem onIso_pf : OnIso := by
  intro K _ W Z q i _ U U' h hU a n
  have := faithful h a
  have := full h a
  have := essSurj U U' h hU a
  have : (morV i rfl a h).G.IsEquivalence := {}
  exact CrystallineSemistableComparison.P.adj_mor (morV i rfl a h) (tau_bij h a) n

end CrystallineSemistableComparison.Onto

end
