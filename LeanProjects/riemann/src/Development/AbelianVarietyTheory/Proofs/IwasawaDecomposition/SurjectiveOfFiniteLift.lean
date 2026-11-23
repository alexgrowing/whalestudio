import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ModelSurj

theorem surjective_of_finite_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (Z : GMod Xo c) (Z' : GMod Xo' c') (b : 𝓞 c.F →+* 𝓞 c'.F)
    (r : Xo'.XF c' ⟶ Xo.XF c) (π : Z'.X ⟶ Z.X) (hπ : π ≫ Z.s = Z'.s ≫ spMap b), b.Finite →
    IsFinite (pullback.lift π Z'.s hπ) → Z'.j ≫ π = r ≫ Z.j → Function.Surjective r → Function.Surjective π := by
  intro E _ _ _ H D l l' Xo Xo' c c' Z Z' b r π hπ hb hfin hj hr

  have hsp : IsFinite (spMap b) := (IsFinite.SpecMap_iff _).mpr hb
  have hfst : IsFinite (pullback.fst Z.s (spMap b)) :=
    by haveI := hsp; infer_instance
  have hfac : π = pullback.lift π Z'.s hπ ≫ pullback.fst Z.s (spMap b) := (pullback.lift_fst _ _ _).symm
  have hπf : IsFinite π := by rw [hfac]; infer_instance
  have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range

  obtain ⟨⟨_, _⟩, -, _⟩ := (CoeffRings.coeff_isDedFrac E H l c).1
  have hdom := (GlobalTheory.genericPart_dense_proOpen (𝓞 c.F) c.F Z.X _ Z.s Z.jQ Z.flat Z.proj Z.jQ_open Z.jQ_dense).2.2.2.2.2.1
  have hd : Dense (Set.range Z.j) := hdom.denseRange

  have hsub : Set.range Z.j ⊆ Set.range π := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hr x
    refine ⟨Z'.j y, ?_⟩
    rw [← Scheme.Hom.comp_apply, hj, Scheme.Hom.comp_apply]
  have huniv : Set.range π = Set.univ := by
    rw [← hcl.closure_eq]; exact (hd.mono hsub).closure_eq
  exact Set.range_eq_univ.mp huniv

end GlobalTheory.ModelSurj
