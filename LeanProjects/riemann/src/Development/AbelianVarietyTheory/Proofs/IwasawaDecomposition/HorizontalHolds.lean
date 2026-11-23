import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrArcOutsideAbelianLocusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionUniqueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionOfMonoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcDataClosedPointStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef

namespace GlobalTheory.HorizProof

theorem exists_frac_map {T T' : CDVR} (g : T.V →+* T'.V) (hi : Function.Injective g) :
    ∃ f : T.Fr →+* T'.Fr, f.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp g := by
  have hj : Function.Injective ((algebraMap T'.V T'.Fr).comp g) := (IsFractionRing.injective T'.V T'.Fr).comp hi
  obtain ⟨f, hf⟩ : ∃ f : T.Fr →+* T'.Fr, ∀ v, f (algebraMap T.V T.Fr v) = algebraMap T'.V T'.Fr (g v) :=
    ⟨IsFractionRing.lift hj, IsFractionRing.lift_algebraMap hj⟩
  exact ⟨f, RingHom.ext hf⟩

theorem closed_comp {T T' : CDVR} (g : T.V →+* T'.V) [IsLocalHom g] {X : Scheme.{0}} (y : Sp T.V ⟶ X) :
    (spMap g ≫ y) (closedPoint T'.V) = y (closedPoint T.V) :=
  (Scheme.Hom.comp_apply _ _ _).trans (congrArg y (IsLocalRing.comap_closedPoint g))

theorem horizSt : HorizSt := by
  intro E _ _ _ H D l Xo c Z h4 x hx
  obtain ⟨T, b, io, y, z, h1, h2, h3, h5, rfl⟩ := GlobalTheory.T.exists_dvr_arc_outside_abelian_locus E H D l Xo c Z x hx
  obtain ⟨T₁, g₁, t, m, P, hi₁, hl₁, hP⟩ := GlobalTheory.T.dvr_arc_extension_unique E H D l Xo c _ _ Z T io b y z h1 h2 h3 h5
  obtain ⟨f₁, hf₁⟩ := exists_frac_map g₁ hi₁
  have e₁ : spMap (algebraMap T₁.V T₁.Fr) ≫ spMap g₁ = spMap f₁ ≫ spMap (algebraMap T.V T.Fr) := by
    rw [← spMap_comp, ← spMap_comp, hf₁]
  have k₁ : (algebraMap T₁.V T₁.Fr).comp (g₁.comp b) = (f₁.comp io).comp (algebraMap (𝓞 c.F) c.F) := by
    rw [← RingHom.comp_assoc, ← hf₁, RingHom.comp_assoc, h1, RingHom.comp_assoc]
  have k₂ : (spMap g₁ ≫ y) ≫ Z.s = spMap (g₁.comp b) := by
    rw [Category.assoc, h2]; exact (spMap_comp b g₁).symm
  have k₃ : (spMap f₁ ≫ z) ≫ pullback.snd _ _ = spMap (f₁.comp io) := by
    rw [Category.assoc, h3]; exact (spMap_comp io f₁).symm
  have k₅ : (spMap f₁ ≫ z) ≫ Z.j = spMap (algebraMap T₁.V T₁.Fr) ≫ spMap g₁ ≫ y := by
    rw [Category.assoc, h5, ← Category.assoc, ← Category.assoc, e₁]
  have hc₁ : (spMap g₁ ≫ y) (closedPoint T₁.V) ∉ abLocus Z.t.G := by
    rw [closed_comp]; exact hx
  obtain ⟨T', g, ϖ, a, hi, hl, hϖ, hA⟩ := GlobalTheory.T.dvr_arc_extension_of_mono E H D l Xo c _ _ Z
    (by have : Epi (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F)) := IsLocalization.epi (nonZeroDivisors (𝓞 c.F)) c.F; exact Scheme.Spec.map_mono (CommRingCat.ofHom _).op)
    T₁ (f₁.comp io) (g₁.comp b) (spMap g₁ ≫ y)
    (spMap f₁ ≫ z) k₁ k₂ k₃ k₅ t m P hP hc₁
  obtain ⟨f, hf⟩ := exists_frac_map g hi
  have e₂ : spMap (algebraMap T'.V T'.Fr) ≫ spMap g = spMap f ≫ spMap (algebraMap T₁.V T₁.Fr) := by
    rw [← spMap_comp, ← spMap_comp, hf]
  have hr : Set.range (jK T'.V ≫ spMap g ≫ spMap g₁ ≫ y) ⊆ Set.range Z.j := by
    have : jK T'.V ≫ spMap g ≫ spMap g₁ ≫ y = (spMap f ≫ spMap f₁ ≫ z) ≫ Z.j := by
      show spMap (algebraMap T'.V T'.Fr) ≫ spMap g ≫ spMap g₁ ≫ y = _
      rw [← Category.assoc, e₂, Category.assoc, ← k₅]
      simp only [Category.assoc]
    rw [this]
    rintro _ ⟨p, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  have hs : (spMap g ≫ spMap g₁ ≫ y) ≫ Z.s = spMap (g.comp (g₁.comp b)) := by
    rw [Category.assoc, k₂]; exact (spMap_comp (g₁.comp b) g).symm
  have := GlobalTheory.T.arc_data_closed_point E H D l Xo c Z h4 T' (g.comp (g₁.comp b)) ϖ a _ hϖ hs hr hA
  rwa [closed_comp g, closed_comp g₁] at this

end GlobalTheory.HorizProof
