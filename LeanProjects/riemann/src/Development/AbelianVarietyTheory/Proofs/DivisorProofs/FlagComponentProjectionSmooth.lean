import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyQuasiFiniteOfUniqueGeomPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIsoOfBijectiveGeomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalSmoothLocalModelStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.FlagSmooth

theorem isIso_of_bijective_geomPts : ∀ (K : Type) [Field K] [CharZero K] (X T : Scheme.{0}) [IsIntegral X] [IsIntegral T] (f : X ⟶ T) (q : T ⟶ Spec (.of K)), LocallyOfFiniteType f → IsSeparated f → QuasiCompact f → (∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t)) → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T), ∃! x : Spec (.of Ω) ⟶ X, x ≫ f = t) → IsIso f := by
  intro K _ _ X T _ _ f q hl hs hq hN hb
  have hqf := GlobalTheory.T.locallyQuasiFinite_of_unique_geom_points X T f hl hb
  obtain ⟨U, hU, hiso⟩ := GlobalTheory.T.exists_open_iso_of_bijective_geom K X T f q hl hqf hs hq hb
  have hsurj : Surjective f := by
    constructor
    intro t
    let t' : Spec (.of (AlgebraicClosure (T.residueField t))) ⟶ T :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) (AlgebraicClosure (T.residueField t)))) ≫
        T.fromSpecResidueField t
    obtain ⟨x, hx, -⟩ := hb _ t'
    obtain ⟨s⟩ : Nonempty (Spec (.of (AlgebraicClosure (T.residueField t)))) := inferInstance
    refine ⟨x s, ?_⟩
    have e : (x ≫ f) s = t' s := by rw [hx]
    rw [Scheme.Hom.comp_apply] at e
    rw [e]
    exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
  have hoi := (GlobalTheory.isOpenImmersion_and_isIso_of_quasiFinite_of_birational f hN U hU).1
  exact (isIso_iff_isOpenImmersion_and_surjective f).2 ⟨hoi, hsurj⟩

theorem smooth_π : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp), Smooth (Φ.C k).π := by
  intro D A N j S κ s Φ k
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  choose W T h g hy hg hgl hT hN he hb using GlobalTheory.T.exists_normal_smooth_local_model D A N j S κ s Φ k
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩) fun y => ?_
  have := hT y
  have := hg y
  have : Nonempty (W y).toScheme := ⟨⟨y, hy y⟩⟩
  have : IsIntegral (W y).toScheme := inferInstance
  have hc : h y ≫ g y ≫ genStr s.T.Z ≫ spMap κ.e.toRingHom = (W y).ι ≫ (Φ.C k).Y.str := by
    rw [← (Φ.C k).π_str, ← Category.assoc, he y, Category.assoc]
  have : IsSeparated (h y ≫ g y ≫ genStr s.T.Z ≫ spMap κ.e.toRingHom) := by rw [hc]; infer_instance
  have : LocallyOfFiniteType (h y ≫ g y ≫ genStr s.T.Z ≫ spMap κ.e.toRingHom) := by rw [hc]; infer_instance
  have h1 : IsSeparated (h y) := IsSeparated.of_comp (h y) (g y ≫ genStr s.T.Z ≫ spMap κ.e.toRingHom)
  have h2 : LocallyOfFiniteType (h y) := locallyOfFiniteType_of_comp (h y) (g y ≫ genStr s.T.Z ≫ spMap κ.e.toRingHom)
  have : IsNoetherian (Φ.C k).Y.X := {}
  have : TopologicalSpace.NoetherianSpace (W y).toScheme := TopologicalSpace.NoetherianSpace.set _
  have h3 : QuasiCompact (h y) := quasiCompact_of_noetherianSpace_source _
  have := isIso_of_bijective_geomPts _ _ _ (h y) (g y ≫ genStr s.T.Z ≫ spMap κ.e.toRingHom) h2 h1 h3 (hN y) (hb y)
  rw [← he y]
  infer_instance

end GlobalTheory.FlagSmooth
