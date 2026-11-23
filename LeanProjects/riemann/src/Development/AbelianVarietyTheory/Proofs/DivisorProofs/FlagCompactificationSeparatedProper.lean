import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointLiftValuationRingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFramesSpecialiseFlagComponentLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationPointExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeCriterionExtensionStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagClsLoc

theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f g : R →+* R'} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_eq_spMap {R R' : Type} [CommRing R] [CommRing R'] (f : Sp R' ⟶ Sp R) : ∃ χ : R →+* R', f = spMap χ :=
  ⟨(Spec.preimage f).hom, (Spec.map_preimage f).symm⟩

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

theorem spMap_residue_apply {V : Type} [CommRing V] [IsLocalRing V] (t : Sp (IsLocalRing.ResidueField V)) :
    spMap (IsLocalRing.residue V) t = IsLocalRing.closedPoint V := by
  have ht : t = IsLocalRing.closedPoint (IsLocalRing.ResidueField V) :=
    Subsingleton.elim (α := PrimeSpectrum (IsLocalRing.ResidueField V)) _ _
  subst ht
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue V)

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)
  {G : Scheme.{0}} (γ : G ⟶ gen Z)
  (Br : ∀ (K : Type) [CommRing K], (Sp K ⟶ G) → ∀ (χ : c.F →+* K) (x : Sp K ⟶ Z.X), EigFrame Z χ x → Prop)
  (h1 : ∀ (K : Type) [CommRing K] (z : Sp K ⟶ G) (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z χ x),
    Br K z χ x g → x = z ≫ γ ≫ genι Z ∧ z ≫ γ ≫ genStr Z = spMap χ)
  (h3 : ∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z χ x)
    (K' : Type) [CommRing K'] (ψ : K →+* K') (χ' : c.F →+* K') (x' : Sp K' ⟶ Z.X) (g' : EigFrame Z χ' x')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K'ˣ), Br K z χ x g → g.Tri ψ g' t → Br K' (spMap ψ ≫ z) χ' x' g')
  (h4 : ∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : c.F →+* K) (x : Sp K ⟶ Z.X)
    (g g' : EigFrame Z χ x), Br K z χ x g → Br K z χ x g' →
      ∃ t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ, g.Tri (RingHom.id K) g' t)

include h1 h3 h4 in

theorem carries_of_bears {K K' : Type} [Field K] [Field K'] (ψ : K →+* K') {z : Sp K ⟶ G} {χ : c.F →+* K}
    {x : Sp K ⟶ Z.X} {g : EigFrame Z χ x} (hg : Br K z χ x g) {z' : Sp K' ⟶ G} (hz : z' = spMap ψ ≫ z)
    {χ' : c.F →+* K'} {x' : Sp K' ⟶ Z.X} {g' : EigFrame Z χ' x'} (hg' : Br K' z' χ' x' g') {p : Sp K ⟶ C.Y.X}
    (hp : p ≫ C.π = z ≫ γ) (hc : C.Carries p g) : C.Carries (spMap ψ ≫ p) g' := by
  subst hz
  obtain ⟨a1, a2⟩ := h1 _ _ _ _ _ hg
  obtain ⟨b1, b2⟩ := h1 _ _ _ _ _ hg'
  have hχ : χ' = ψ.comp χ := spMap_inj (by rw [← b2, GlobalTheory.CarrySpec.spMap_comp, ← a2, Category.assoc])
  have hx : x' = spMap ψ ≫ x := by rw [b1, a1, Category.assoc]
  obtain ⟨g₁, hg₁⟩ := g.exists_isMap ψ hχ hx
  have ht := EigFrame.IsMap.tri hg₁ hχ hx
  have c1 : x = p ≫ C.π ≫ genι Z := by rw [a1, ← Category.assoc p, hp, Category.assoc]
  have c2 : p ≫ C.π ≫ genStr Z = spMap χ := by rw [← a2, ← Category.assoc p, hp, Category.assoc]
  have hc₁ := (GlobalTheory.T.flag_compactification_point_extension E H Dw l Xo c Oz β Z F e C K χ x g K' ψ χ' x' g₁ 1 p c1 c2 ht).2 hc
  obtain ⟨t, ht'⟩ := h4 _ _ _ _ g₁ g' (h3 _ _ _ _ _ _ _ _ _ _ _ hg ht) hg'
  have := (GlobalTheory.T.flag_compactification_point_extension E H Dw l Xo c Oz β Z F e C K' χ' x' g₁ K' (RingHom.id K') χ' x' g' t (spMap ψ ≫ p)
    (by rw [hx, c1, Category.assoc]) (by rw [hχ, GlobalTheory.CarrySpec.spMap_comp, ← c2, Category.assoc]) ht').2 hc₁
  rwa [spMap_id, Category.id_comp] at this

include h1 h3 h4 in

theorem exists_ext
    (hl : ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ →
      Set.range x ⊆ Set.range C.π → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ C.π = x ∧ C.Carries p g)
    (h2 : ∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : c.F →+* K), z ≫ γ ≫ genStr Z = spMap χ →
      ∃ g : EigFrame Z χ (z ≫ γ ≫ genι Z), Br K z χ _ g)
    (hr : Set.range γ ⊆ Set.range C.π)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (K : Type) [Field K] [Algebra R K]
    [IsFractionRing R K] (s : Sp R ⟶ G) {η : Sp K ⟶ G} (hη : η = spMap (algebraMap R K) ≫ s) (p : Sp K ⟶ C.Y.X)
    {χ : c.F →+* K} {x : Sp K ⟶ Z.X} {g : EigFrame Z χ x} (hg : Br K η χ x g) (hp : p ≫ C.π = η ≫ γ)
    (hc : C.Carries p g) : ∃ q : Sp R ⟶ C.Y.X, spMap (algebraMap R K) ≫ q = p := by

  have hu : ∀ (k : Type) [Field k] (z : Sp k ⟶ G) (χ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z χ x),
      Br k z χ x g → ∃! p : Sp k ⟶ C.Y.X, p ≫ C.π = z ≫ γ ∧ C.Carries p g := by
    intro k _ z χ x g hb
    obtain ⟨a1, a2⟩ := h1 _ _ _ _ _ hb
    rw [← Category.assoc] at a1 a2
    subst a1
    refine hl k χ (z ≫ γ) a2 ?_ g
    rintro _ ⟨t, rfl⟩
    exact hr ⟨z t, by simp⟩
  obtain ⟨χ₀, hχ₀⟩ := exists_eq_spMap ((spMap (IsLocalRing.residue R) ≫ s) ≫ γ ≫ genStr Z)
  obtain ⟨g₀, hg₀⟩ := h2 _ _ _ hχ₀
  obtain ⟨p₀, ⟨hp₀, hc₀⟩, -⟩ := hu _ _ _ _ _ hg₀
  refine GlobalTheory.T.valuative_criterion_extension R K C.Y.X p (p₀ (IsLocalRing.closedPoint _)) fun V ρ hρ hV => ?_
  have hη' : η = spMap V.subtype ≫ spMap ρ ≫ s := by
    rw [hη, ← hV, GlobalTheory.CarrySpec.spMap_comp, Category.assoc]
  obtain ⟨q, hq, hqp⟩ := GlobalTheory.T.exists_flagComponent_point_lift_valuationRing E H Dw l Xo c Oz β Z F e C V K ((spMap ρ ≫ s) ≫ γ) p
    (by rw [hp, hη', Category.assoc]; rfl)
  have hqp' : spMap V.subtype ≫ q = p := hqp
  refine ⟨q, hqp', ?_⟩
  obtain ⟨χV, hχV⟩ := exists_eq_spMap ((spMap ρ ≫ s) ≫ γ ≫ genStr Z)
  obtain ⟨gV, hgV⟩ := h2 _ _ _ hχV
  obtain ⟨gL, hgL⟩ := gV.exists_isMap V.subtype rfl rfl
  have tL := EigFrame.IsMap.tri hgL rfl rfl
  obtain ⟨gk, hgk⟩ := gV.exists_isMap (IsLocalRing.residue V) rfl rfl
  have tk := EigFrame.IsMap.tri hgk rfl rfl
  have bL := h3 _ _ _ _ _ _ _ _ _ _ _ hgV tL
  have bk := h3 _ _ _ _ _ _ _ _ _ _ _ hgV tk
  have cL := carries_of_bears C γ Br h1 h3 h4 (RingHom.id K) hg (by rw [spMap_id, Category.id_comp, hη']) bL hp hc
  rw [spMap_id, Category.id_comp, ← hqp'] at cL
  have ck := GlobalTheory.T.carriedFrames_specialise_flagComponent_localRing E H Dw l Xo c Oz β Z F e C V K V.subtype Subtype.val_injective _ (IsLocalRing.residue V)
    IsLocalRing.ker_residue q χV _ (by rw [← Category.assoc q, hq]; simp only [Category.assoc]) gV _ _ gL 1 tL cL _ _ gk 1 tk
  have hz : spMap (IsLocalRing.residue V) ≫ spMap ρ ≫ s =
      spMap (IsLocalRing.ResidueField.map ρ) ≫ spMap (IsLocalRing.residue R) ≫ s := by
    rw [← Category.assoc, ← Category.assoc, ← GlobalTheory.CarrySpec.spMap_comp, ← GlobalTheory.CarrySpec.spMap_comp,
      IsLocalRing.ResidueField.map_comp_residue]
  have ck' := carries_of_bears C γ Br h1 h3 h4 (IsLocalRing.ResidueField.map ρ) hg₀ hz bk hp₀ hc₀
  have heq : spMap (IsLocalRing.residue V) ≫ q = spMap (IsLocalRing.ResidueField.map ρ) ≫ p₀ :=
    (hu _ _ _ _ _ bk).unique ⟨by rw [Category.assoc, hq]; simp only [Category.assoc], ck⟩
      ⟨by rw [Category.assoc, hp₀, hz]; simp only [Category.assoc], ck'⟩
  obtain ⟨t⟩ : Nonempty (Sp (IsLocalRing.ResidueField V)) := ⟨IsLocalRing.closedPoint _⟩
  have := congrArg (fun f : Sp (IsLocalRing.ResidueField V) ⟶ C.Y.X => f t) heq
  simp only [Scheme.Hom.comp_apply] at this
  rw [spMap_residue_apply] at this
  exact this.trans (congrArg p₀ (Subsingleton.elim (α := PrimeSpectrum (IsLocalRing.ResidueField R)) _ _))

end

set_option backward.isDefEq.respectTransparency false in

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e), IsSeparated (genStr Z) → (∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ → Set.range x ⊆ Set.range C.π → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ C.π = x ∧ C.Carries p g) → ∀ (G : Scheme.{0}) [IsIntegral G] (γ : G ⟶ gen Z) (Br : ∀ (K : Type) [CommRing K], (Sp K ⟶ G) → ∀ (χ : c.F →+* K) (x : Sp K ⟶ Z.X), EigFrame Z χ x → Prop), (∀ (K : Type) [CommRing K] (z : Sp K ⟶ G) (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z χ x), Br K z χ x g → x = z ≫ γ ≫ genι Z ∧ z ≫ γ ≫ genStr Z = spMap χ) → (∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : c.F →+* K), z ≫ γ ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (z ≫ γ ≫ genι Z), Br K z χ _ g) → (∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z χ x) (K' : Type) [CommRing K'] (ψ : K →+* K') (χ' : c.F →+* K') (x' : Sp K' ⟶ Z.X) (g' : EigFrame Z χ' x') (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K'ˣ), Br K z χ x g → g.Tri ψ g' t → Br K' (spMap ψ ≫ z) χ' x' g') → (∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g g' : EigFrame Z χ x), Br K z χ x g → Br K z χ x g' → ∃ t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ, g.Tri (RingHom.id K) g' t) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G → Set.range γ ⊆ Set.range C.π → ∀ (p : Sp G.functionField ⟶ C.Y.X) (χ : c.F →+* G.functionField) (g : EigFrame Z χ (GlobalTheory.FlagCov.genPt G ≫ γ ≫ genι Z)), Br _ (GlobalTheory.FlagCov.genPt G) χ _ g → p ≫ C.π = GlobalTheory.FlagCov.genPt G ≫ γ → C.Carries p g → ∀ z : G, ∃ q : Sp (G.presheaf.stalk z) ⟶ C.Y.X, spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ q = p ∧ q ≫ C.π = G.fromSpecStalk z ≫ γ := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ e C hs hl G _ γ Br h1 h2 h3 h4 hn hr p χ g hg hp hc z
  haveI := (hn z).1
  haveI := (hn z).2
  have hη : GlobalTheory.FlagCov.genPt G = spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ G.fromSpecStalk z :=
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec G).specializes (Set.mem_univ z))).symm
  obtain ⟨q, hq⟩ := exists_ext C γ Br h1 h3 h4 hl h2 hr (G.presheaf.stalk z) G.functionField (G.fromSpecStalk z) hη p
    hg hp hc
  refine ⟨q, hq, ?_⟩
  have hi : Function.Injective (algebraMap (G.presheaf.stalk z) G.functionField) := IsFractionRing.injective _ _
  have he : spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ q ≫ C.π =
      spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ G.fromSpecStalk z ≫ γ := by
    rw [← Category.assoc, hq, hp, hη, Category.assoc]
  haveI : IsDominant (spMap (algebraMap (G.presheaf.stalk z) G.functionField)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 hi).le.trans bot_le)⟩
  refine ext_of_isDominant_of_isSeparated (genStr Z) ?_ _ he
  obtain ⟨a, ha⟩ := exists_eq_spMap ((q ≫ C.π) ≫ genStr Z)
  obtain ⟨b, hb⟩ := exists_eq_spMap ((G.fromSpecStalk z ≫ γ : Sp (G.presheaf.stalk z) ⟶ _) ≫ genStr Z)
  have hab : (algebraMap _ G.functionField).comp a = (algebraMap _ G.functionField).comp b := spMap_inj (by
    rw [GlobalTheory.CarrySpec.spMap_comp, GlobalTheory.CarrySpec.spMap_comp, ← ha, ← hb, ← Category.assoc, he, Category.assoc])
  have : a = b := RingHom.ext fun r => hi (RingHom.congr_fun hab r)
  exact ha.trans (this ▸ hb.symm)

end GlobalTheory.FlagClsLoc

end
