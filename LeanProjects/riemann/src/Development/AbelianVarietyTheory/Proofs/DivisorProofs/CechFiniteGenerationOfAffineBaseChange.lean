import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem cechFG_of_transfer {Z Z' : Scheme.{0}} {J : Type} (W : J → Z.Opens) (W' : J → Z'.Opens)
    (R : Type) [CommRing R]
    (act : ∀ i i' : J, R →+* Γ(Z, W i ⊓ W i')) (act' : ∀ i i' : J, R →+* Γ(Z', W' i ⊓ W' i'))
    (φ1 : ∀ i, Γ(Z, W i) →+* Γ(Z', W' i))
    (φ2 : ∀ i i', Γ(Z, W i ⊓ W i') →+* Γ(Z', W' i ⊓ W' i'))
    (φ3 : ∀ i i' i'', Γ(Z, W i ⊓ W i' ⊓ W i'') →+* Γ(Z', W' i ⊓ W' i' ⊓ W' i''))
    (h1 : ∀ i, Function.Surjective (φ1 i))
    (h2 : ∀ i i', Function.Bijective (φ2 i i'))
    (h3 : ∀ i i' i'', Function.Injective (φ3 i i' i''))
    (hl : ∀ i i' x, φ2 i i' (resG Z inf_le_left x) = resG Z' inf_le_left (φ1 i x))
    (hr : ∀ i i' x, φ2 i i' (resG Z inf_le_right x) = resG Z' inf_le_right (φ1 i' x))
    (ha : ∀ i i' i'' x, φ3 i i' i'' (resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') x) =
      resG Z' (inf_le_left : W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i') (φ2 i i' x))
    (hb : ∀ i i' i'' x, φ3 i i' i'' (resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') x) =
      resG Z' (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W' i ⊓ W' i' ⊓ W' i'' ≤ W' i' ⊓ W' i'') (φ2 i' i'' x))
    (hc : ∀ i i' i'' x, φ3 i i' i'' (resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') x) =
      resG Z' (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i'') (φ2 i i'' x))
    (hact : ∀ i i' r, φ2 i i' (act i i' r) = act' i i' r) :
    CechFG W' R act' → CechFG W R act := by
  rintro ⟨N, e', he', hc'⟩
  choose g hg using fun (k : Fin N) (i i' : J) => (h2 i i').2 (e' k i i')
  refine ⟨N, g, ?_, ?_⟩
  · intro k i i' i''
    apply h3 i i' i''
    have := he' k i i' i''
    rw [map_add, ha, hb, hc, hg, hg, hg]
    exact this
  · intro c hcoc
    obtain ⟨r, h', hh⟩ := hc' (fun i i' => φ2 i i' (c i i')) (by
      intro i i' i''
      have := congrArg (φ3 i i' i'') (hcoc i i' i'')
      rw [map_add, ha, hb, hc] at this
      exact this)
    choose h hh1 using fun i => h1 i (h' i)
    refine ⟨r, h, fun i i' => (h2 i i').1 ?_⟩
    have e1 := hh i i'
    rw [map_add, map_sub, map_sum, hl, hr, hh1, hh1]
    simp only [map_mul, hact, hg]
    exact e1

theorem appLE_resG {X Y : Scheme.{0}} (f : X ⟶ Y) {O₁ O₂ : Y.Opens} {V₁ V₂ : X.Opens} (hO : O₂ ≤ O₁)
    (hV : V₂ ≤ V₁) (e₁ : V₁ ≤ f ⁻¹ᵁ O₁) (e₂ : V₂ ≤ f ⁻¹ᵁ O₂) (x : Γ(Y, O₁)) :
    (f.appLE O₂ V₂ e₂).hom (resG Y hO x) = resG X hV ((f.appLE O₁ V₁ e₁).hom x) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_bijective {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] {O : Y.Opens}
    (hO : O ≤ f.opensRange) {V : X.Opens} (hV : V = f ⁻¹ᵁ O) (e : V ≤ f ⁻¹ᵁ O) :
    Function.Bijective (f.appLE O V e).hom := by
  subst hV
  rw [Scheme.Hom.appLE_eq_app]
  haveI := f.isIso_app O hO
  exact (asIso (f.app O)).commRingCatIsoToRingEquiv.bijective

end GlobalTheory.CechTr

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem preimage_inf' {X Y : Scheme.{0}} (f : X ⟶ Y) (A B : Y.Opens) :
    f ⁻¹ᵁ (A ⊓ B) = f ⁻¹ᵁ A ⊓ f ⁻¹ᵁ B := by
  ext x; simp

theorem appLE_act {G X : Scheme.{0}} (p : G ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (O : G.Opens)
    (V : (pullback p hU.fromSpec).Opens) (hO : O ≤ p ⁻¹ᵁ U)
    (e : V ≤ pullback.fst p hU.fromSpec ⁻¹ᵁ O) (r : Γ(X, U)) :
    ((pullback.fst p hU.fromSpec).appLE O V e).hom ((p.appLE U O hO).hom r) =
      (secMap (R := Γ(X, U)) (pullback.snd p hU.fromSpec) V).hom r := by
  have e' : V ≤ (pullback.snd p hU.fromSpec ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [← pullback.condition]; exact e.trans (Scheme.Hom.preimage_mono _ hO)
  have key : (pullback.snd p hU.fromSpec ≫ hU.fromSpec).appLE U V e' =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (pullback.snd p hU.fromSpec).appLE ⊤ V le_top := by
    rw [Scheme.Hom.comp_appLE, hU.fromSpec_app_self, Category.assoc]
    exact congrArg ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ ·) (Scheme.Hom.map_appLE _ _ _)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq pullback.condition _ _ _ e', key]
  rfl

end GlobalTheory.CechTr

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem cechFG_of_baseChange_affineOpen (G X : Scheme.{0}) (p : G ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U) :
    CechFG (fun i => pullback.fst p hU.fromSpec ⁻¹ᵁ W i) Γ(X, U)
        (fun i i' => (secMap (R := Γ(X, U)) (pullback.snd p hU.fromSpec) _).hom) →
      CechFG W Γ(X, U) (fun i i' => (p.appLE U (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  have hR : ∀ O : G.Opens, O ≤ p ⁻¹ᵁ U → O ≤ (pullback.fst p hU.fromSpec).opensRange := by
    intro O hO
    rw [Scheme.Hom.opensRange_pullbackFst, IsAffineOpen.opensRange_fromSpec]
    exact hO
  have h2e : ∀ A B : G.Opens, pullback.fst p hU.fromSpec ⁻¹ᵁ A ⊓ pullback.fst p hU.fromSpec ⁻¹ᵁ B =
      pullback.fst p hU.fromSpec ⁻¹ᵁ (A ⊓ B) := fun A B => (preimage_inf' _ A B).symm
  refine cechFG_of_transfer W _ _ _ _
    (fun i => ((pullback.fst p hU.fromSpec).appLE (W i) _ le_rfl).hom)
    (fun i i' => ((pullback.fst p hU.fromSpec).appLE (W i ⊓ W i') _ (h2e _ _).le).hom)
    (fun i i' i'' => ((pullback.fst p hU.fromSpec).appLE (W i ⊓ W i' ⊓ W i'') _
      (by rw [h2e, h2e])).hom)
    (fun i => (appLE_bijective _ (hR _ (hWU i)) rfl _).2)
    (fun i i' => appLE_bijective _ (hR _ (inf_le_left.trans (hWU i))) (h2e _ _) _)
    (fun i i' i'' => (appLE_bijective _ (hR _ (inf_le_left.trans (inf_le_left.trans (hWU i))))
      (by rw [h2e, h2e]) _).1)
    (fun i i' x => appLE_resG _ _ _ _ _ x)
    (fun i i' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' r => appLE_act p U hU _ _ _ _ r)

theorem cechFG_of_baseChange_affine (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type)
    (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1) :
    CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1)
        (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) →
      CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) :=
  cechFG_of_baseChange_affineOpen G X p U.1 U.2 J W hWU

end GlobalTheory.CechTr
