import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationPointExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFramesSpecialiseFlagComponentLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

theorem exists_tri_baseChange {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {A B : Type} [CommRing A] [CommRing B]
    {φ : c.F →+* A} {x : Sp A ⟶ Z.X} (f : EigFrame Z φ x) (ψ : A →+* B) {φ' : c.F →+* B} {x' : Sp B ⟶ Z.X}
    (hx : x' = spMap ψ ≫ x) (hφ : φ' = ψ.comp φ) : ∃ g : EigFrame Z φ' x', f.Tri ψ g 1 := by
  subst hx hφ
  obtain ⟨g, hg⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c Oz β Z A B φ x f ψ
  refine ⟨g, rfl, rfl, fun τ i => ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
  simp only [← hg]
  exact isCombAtG_single Z.t _ (g.tan τ) i

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem carries_of_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (G : Scheme.{0}) [IsIntegral G] (γ : G ⟶ gen Z) (Br : ∀ (K : Type) [CommRing K], (Sp K ⟶ G) → ∀ (χ : c.F →+* K) (x : Sp K ⟶ Z.X), EigFrame Z χ x → Prop), (∀ (K : Type) [CommRing K] (z : Sp K ⟶ G) (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z χ x), Br K z χ x g → x = z ≫ γ ≫ genι Z ∧ z ≫ γ ≫ genStr Z = spMap χ) → (∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : c.F →+* K), z ≫ γ ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (z ≫ γ ≫ genι Z), Br K z χ _ g) → (∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z χ x) (K' : Type) [CommRing K'] (ψ : K →+* K') (χ' : c.F →+* K') (x' : Sp K' ⟶ Z.X) (g' : EigFrame Z χ' x') (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K'ˣ), Br K z χ x g → g.Tri ψ g' t → Br K' (spMap ψ ≫ z) χ' x' g') → (∀ (K : Type) [CommRing K] [IsLocalRing K] (z : Sp K ⟶ G) (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g g' : EigFrame Z χ x), Br K z χ x g → Br K z χ x g' → ∃ t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ, g.Tri (RingHom.id K) g' t) → ∀ (πG : G ⟶ C.Y.X) (χ : c.F →+* G.functionField) (g : EigFrame Z χ (GlobalTheory.FlagCov.genPt G ≫ γ ≫ genι Z)), Br _ (GlobalTheory.FlagCov.genPt G) χ _ g → πG ≫ C.π = γ → C.Carries (GlobalTheory.FlagCov.genPt G ≫ πG) g → ∀ (K : Type) [Field K] (z : Sp K ⟶ G) (χ' : c.F →+* K) (x : Sp K ⟶ Z.X) (g' : EigFrame Z χ' x), Br K z χ' x g' → C.Carries (z ≫ πG) g' := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ e C G _ γ Br h1 h2 h3 h4 πG χ g hg hπ hc K _ z χ' x g' hg'
  obtain ⟨⟨y, r, hr⟩, rfl⟩ := (SpecToEquivOfLocalRing G (CommRingCat.of K)).symm.surjective z
  have hz : (SpecToEquivOfLocalRing G (CommRingCat.of K)).symm ⟨y, r, hr⟩ =
    spMap r.hom ≫ (show Sp (G.presheaf.stalk y) ⟶ G from G.fromSpecStalk y) := rfl
  rw [hz] at hg' ⊢
  set s : Sp (G.presheaf.stalk y) ⟶ G := G.fromSpecStalk y with hs
  obtain ⟨χV, hχV⟩ : ∃ χV : c.F →+* G.presheaf.stalk y, s ≫ γ ≫ genStr Z = spMap χV :=
    ⟨(Spec.preimage (s ≫ γ ≫ genStr Z)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨gV, hgV⟩ := h2 _ s χV hχV
  let ν : G.presheaf.stalk y →+* G.functionField := algebraMap _ _
  have hν : spMap ν ≫ s = GlobalTheory.FlagCov.genPt G := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
  have hcomp : ∀ {R : Type} [CommRing R] (ψ : G.presheaf.stalk y →+* R) (χ₁ : c.F →+* R),
      (spMap ψ ≫ s) ≫ γ ≫ genStr Z = spMap χ₁ → χ₁ = ψ.comp χV := fun ψ χ₁ h => by
    apply spMap_inj
    rw [← h, Category.assoc, hχV, ← Spec.map_comp]
    rfl
  have hid : ∀ (R : Type) [CommRing R], spMap (RingHom.id R) = 𝟙 _ := fun R _ => Spec.map_id _
  obtain ⟨gL, hgL⟩ := exists_tri_baseChange gV ν (φ' := χ) (x' := GlobalTheory.FlagCov.genPt G ≫ γ ≫ genι Z)
    (by rw [← hν, Category.assoc]) (hcomp ν χ (by rw [hν]; exact (h1 _ _ _ _ _ hg).2))
  have hbL := h3 _ _ _ _ _ _ _ _ _ _ _ hgV hgL
  rw [hν] at hbL
  obtain ⟨tL, htL⟩ := h4 _ _ _ _ _ _ hg hbL
  have hcL := (GlobalTheory.T.flag_compactification_point_extension E H Dw l Xo c Oz β Z F e C _ _ _ g _ _ _ _ gL tL (GlobalTheory.FlagCov.genPt G ≫ πG)
    (by rw [← hπ]; simp only [Category.assoc])
    (by rw [← (h1 _ _ _ _ _ hg).2, ← hπ]; simp only [Category.assoc]) htL).2 hc
  rw [hid, Category.id_comp, show GlobalTheory.FlagCov.genPt G ≫ πG = spMap ν ≫ s ≫ πG by rw [← hν, Category.assoc]] at hcL
  obtain ⟨gK, hgK⟩ := exists_tri_baseChange gV r.hom (φ' := χ') (x' := x)
    (by rw [(h1 _ _ _ _ _ hg').1, Category.assoc]) (hcomp r.hom χ' (h1 _ _ _ _ _ hg').2)
  have hbK := h3 _ _ _ _ _ _ _ _ _ _ _ hgV hgK
  obtain ⟨tK, htK⟩ := h4 _ _ _ _ _ _ hbK hg'
  have hker : RingHom.ker r.hom = IsLocalRing.maximalIdeal (G.presheaf.stalk y) := by
    ext a
    rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff r.hom a, isUnit_iff_ne_zero,
      not_not]
  have hcK := GlobalTheory.CarrySpec.carries_spec E H Dw l Xo c Oz β Z F e C _ _ ν (IsFractionRing.injective _ _) K r.hom hker
    (s ≫ πG) χV _ (by rw [← hπ]; simp only [Category.assoc]) gV _ _ gL _ hgL hcL _ _ gK _ hgK
  have := (GlobalTheory.T.flag_compactification_point_extension E H Dw l Xo c Oz β Z F e C _ _ _ gK _ _ _ _ g' tK (spMap r.hom ≫ s ≫ πG)
    (by rw [(h1 _ _ _ _ _ hg').1, ← hπ]; simp only [Category.assoc])
    (by rw [← (h1 _ _ _ _ _ hg').2, ← hπ]; simp only [Category.assoc]) htK).2 hcK
  rwa [hid, Category.id_comp, ← Category.assoc] at this

end GlobalTheory.FlagCls

end
