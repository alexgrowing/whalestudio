import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatExtensionRegularSequenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFibreRegularLocalRingStatement
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.SncPull

theorem lsncAt_preimage : ∀ (k : Type) [Field k] [CharZero k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) [Smooth p] (π : Y ⟶ X) [Smooth π] (m : ℕ) (C : Fin m → Closeds X) (y : Y), LSncAt X C (π y) → LSncAt Y (fun i => (C i).preimage π.continuous) y := by
  intro k _ _ X Y p _ π _ m C y ⟨_, n, r, e, hr, hst⟩
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (π ≫ p)
  obtain ⟨g, s, hs⟩ := GlobalTheory.T.flat_extension_regular_sequence _ _ (π.stalkMap y).hom (Flat.stalkMap π y) (GlobalTheory.T.smooth_fibre_regular_local_ring X Y π y) n r hr
  haveI : IsRegularLocalRing (Y.presheaf.stalk y) := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
    rw [← hs.2, ← hs.1]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite
      (R := Y.presheaf.stalk y) (Set.finite_range (Fin.append (fun i => (π.stalkMap y).hom (r i)) s))
    have h2 : (Set.range (Fin.append (fun i => (π.stalkMap y).hom (r i)) s)).ncard ≤ n + g := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
    exact_mod_cast h1.trans h2
  refine ⟨inferInstance, n + g, Fin.append (fun i => (π.stalkMap y).hom (r i)) s,
    ⟨fun i => Fin.castAdd g (e ⟨i.1, i.2⟩), fun a b h => ?_⟩, hs, fun i => ?_⟩
  · have h' := e.injective (Fin.castAdd_injective _ _ h)
    exact Subtype.ext (congrArg Subtype.val h')
  · have hp := ReciprocityTheory.AnForm.R.prime_of_regular_params _ hs.1 hs.2 (Fin.castAdd g (e ⟨i.1, i.2⟩))
    rw [Fin.append_left] at hp
    change stalkId (Scheme.IdealSheafData.vanishingIdeal (GlobalTheory.TorRef.pre π (C i.1))) y = _
    rw [GlobalTheory.VanStalk.van_pre, hst ⟨i.1, i.2⟩, Ideal.map_span, Set.image_singleton]
    show _ = Ideal.span {Fin.append (fun i => (π.stalkMap y).hom (r i)) s (Fin.castAdd g (e ⟨i.1, i.2⟩))}
    rw [Fin.append_left]
    exact ((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical

end GlobalTheory.SncPull
