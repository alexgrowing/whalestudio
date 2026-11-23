import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFramesTriangularComponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

namespace GlobalTheory.ShFam.GalCarry.RelBwd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem ptRel_mk {Z : Model Xo c β} (T : Tw Z) {F : Type} [Field F] {e : F ≃+* c.F} (C C' : FlagCpt Z e) {K : Type}
    [Field K] (p : Sp K ⟶ C.Y.X) (p' : Sp K ⟶ C'.Y.X) (χ : c.F →+* K) {y y' : Sp K ⟶ Z.X}
    (hy : y = p ≫ C.π ≫ genι Z) (hy' : y' = p' ≫ C'.π ≫ genι Z) (f : EigFrame Z χ y) (f' : EigFrame Z χ y')
    (h1 : p' ≫ C'.π = p ≫ C.π ≫ T.g.hom) (hs : p ≫ C.π ≫ genStr Z = spMap χ) (hP : T.Push f f')
    (hc : C.Carries p f) (hc' : C'.Carries p' f') : T.PtRel C C' p p' := by
  subst hy hy'
  exact ⟨h1, χ, f, f', hs, hP, hc, hc'⟩

theorem carries_of_tri {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {K : Type} [Field K]
    {φ φ' : c.F →+* K} {x x' : Sp K ⟶ Z.X} {g : EigFrame Z φ x} {g' : EigFrame Z φ' x'}
    {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ} (h : g.Tri (RingHom.id K) g' d) {p : Sp K ⟶ C.Y.X}
    (hp : C.Carries p g) : C.Carries p g' := by
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hp
  exact ⟨y, ψ, φ₁, f, t, _, h1, h2, GlobalTheory.ShFam.FlatSec.tri_trans h3 h⟩

theorem existsUnique_source : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (K : Type) [Field K] [IsAlgClosed K] (i' : U.Comp) (p' : Sp K ⟶ (Φ.C i').Y.X), ∃! q : Σ i : U.Comp, (Sp K ⟶ (Φ.C i).Y.X), T.PtRel (Φ.C q.1) (Φ.C i') q.2 p' := by
  intro E _ _ _ H Dw l Xo c O _ β Z T F _ e σ N U Φ K _ _ i' p'

  let χ : c.F →+* K := (Spec.preimage (p' ≫ (Φ.C i').π ≫ genStr Z)).hom
  have hχ : p' ≫ (Φ.C i').π ≫ genStr Z = spMap χ := (Spec.map_preimage _).symm
  obtain ⟨f', hf'⟩ := GlobalTheory.CarryAll.carry_some E H Dw l Xo c O β Z F e (Φ.C i') K χ p' hχ

  let x : Sp K ⟶ gen Z := p' ≫ (Φ.C i').π ≫ T.g.inv
  have hginv : T.g.inv ≫ genStr Z = genStr Z := (Iso.inv_comp_eq _).2 T.g_str.symm
  have hx : x ≫ genStr Z = spMap χ := by
    simp only [x, Category.assoc, hginv]; exact hχ
  have hpull : p' ≫ (Φ.C i').π ≫ genι Z = (x ≫ genι Z) ≫ T.ρ.hom := by
    simp only [x, Category.assoc, ← T.g_ι, Iso.inv_hom_id_assoc]
  obtain ⟨f, hP⟩ := T.exists_pull f' rfl hpull
  obtain ⟨q, ⟨hq1, hq2⟩, hqu⟩ := Φ.lifts K χ x hx f
  refine ⟨q, ?_, fun r hr => hqu r ?_⟩
  · refine ptRel_mk T (Φ.C q.1) (Φ.C i') q.2 p' χ (by rw [← Category.assoc, hq1]) rfl f f' ?_ ?_ hP hq2 hf'
    · rw [← Category.assoc, hq1]; simp only [x, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [← Category.assoc, hq1]; exact hx
  · obtain ⟨h1, χ₁, f₁, f₁', hs₁, hP₁, hc₁, hc₁'⟩ := hr
    have hr1 : r.2 ≫ (Φ.C r.1).π = x := by
      show _ = (p' ≫ (Φ.C i').π) ≫ T.g.inv
      rw [h1, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    obtain ⟨t', ht'⟩ := GlobalTheory.VarFlag.tri_of_carries (Φ.C i') hc₁' hf'
    obtain ⟨t, ht⟩ := T.exists_relab t'
    have htri : f₁.Tri (RingHom.id K) f t := (Tw.Push.tri_iff hP₁ hP ht).2 ht'
    exact ⟨hr1, carries_of_tri (Φ.C r.1) htri hc₁⟩

end GlobalTheory.ShFam.GalCarry.RelBwd
