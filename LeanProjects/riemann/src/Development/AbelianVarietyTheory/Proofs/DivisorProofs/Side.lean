import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option autoImplicit false

namespace GlobalTheory.ShFam.GalCarry.Corr

def Side {F : Type} [Field F] {I I' : Type} (Y : I → Var F) (Y' : I' → Var F)
    (Rel : ∀ (K : Type) [Field K] (i : I) (i' : I'), (Sp K ⟶ (Y i).X) → (Sp K ⟶ (Y' i').X) → Prop) : Prop :=
  (∀ (K : Type) [Field K] i i' p p', Rel K i i' p p' → p' ≫ (Y' i').str = p ≫ (Y i).str) ∧
  (∀ (K K' : Type) [Field K] [Field K'] (ν : K →+* K') i i' p p', Rel K i i' p p' →
      Rel K' i i' (spMap ν ≫ p) (spMap ν ≫ p')) ∧
  (∀ (K : Type) [Field K] [IsAlgClosed K] i p, ∃! q : Σ i', (Sp K ⟶ (Y' i').X), Rel K i q.1 p q.2) ∧
  (∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (L : Type) [Field L] (ν : V →+* L) (k : Type) [Field k]
      (r : V →+* k) i i' (q : Sp V ⟶ (Y i).X) (q' : Sp V ⟶ (Y' i').X), Function.Injective ν →
      RingHom.ker r = IsLocalRing.maximalIdeal V → Rel L i i' (spMap ν ≫ q) (spMap ν ≫ q') →
      Rel k i i' (spMap r ≫ q) (spMap r ≫ q'))

end GlobalTheory.ShFam.GalCarry.Corr
