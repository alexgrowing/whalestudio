import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

theorem UpperTheory.transition_local_frame :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : LocM.Mdl Y i₀) (a : Fin Z.m) (τ : (Y Z.i).X ⟶ (Y i₀).X) (mu : SABMap (Y Z.i).t (Y i₀).t τ), LocM.IsTrans i₀ Z.i τ mu → ∀ (R : Type) [CommRing R] (φ : Γ(Z.X, (Z.U a).1) →+* R) (y : Sp R ⟶ (Xo i₀.l).XF i₀.c) (f : i₀.c.F →+* R), y ≫ (Y i₀).j = (spMap φ ≫ Z.chart a) ≫ Z.π ≫ τ → y ≫ pullback.snd _ _ = spMap f → LocM.IsFrame (Dw := Dw) (Y i₀).t f (y ≫ (Y i₀).j) (fun σ m => (Z.fr a).bc φ σ m ≫ mu.φ) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z a τ mu hT R _ φ y f hy hf
  have key : f = (φ.comp (Z.alg a)).comp (IntermediateField.inclusion Z.le).toRingHom := by
    obtain ⟨b, π', -, hb, h₁, h₂, -⟩ := hT
    have e : τ ≫ (Y i₀).s = (Y Z.i).s ≫ spMap b := by
      rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]
    have js : (Y i₀).j ≫ (Y i₀).s = pullback.snd _ _ ≫ spMap (i₀.c.V W).subtype := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, Category.assoc, pullback.condition, ← Category.assoc, (Y i₀).jQ_over]
    have := mono_spMap_subtype (i₀.c.V W)
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) ?_)
    have cs := Pull.affineOpenChart_comp_structure_eq_spMap Z (a := a) (φ := φ) rfl
    have e2 : spMap f ≫ spMap (i₀.c.V W).subtype =
        (spMap (φ.comp (Z.alg a)) ≫ spMap (Z.i.c.V W).subtype) ≫ spMap b := by
      rw [← cs, ← hf]
      refine (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) js.symm).trans ?_)
      rw [← Category.assoc, hy]
      simp only [Category.assoc, e]
    rw [← cancel_mono (spMap (i₀.c.V W).subtype)]
    refine e2.trans ?_
    rw [ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp]
    congr 1
    ext x
    exact congrArg (φ.comp (Z.alg a)) (Subtype.ext (hb x))
  exact Pull.frame_push mu (by rw [hy, Category.assoc]) (fun σ x => by rw [key]; rfl)
    (Pull.chart_frame Z (a := a) (φ := φ) rfl)
