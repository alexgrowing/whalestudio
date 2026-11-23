import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SymbolRealisableBound
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeLatticeMulOfWeightSum

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

def EdgeFamOf : Prop :=
  ∀ (D : Formalism.BasicNotions.D7), tableLineDegreeFive.LevelPrimesProviso D → BePerfect → DualHeightInclusion →
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
  ∀ (m r : ℕ) (fl rest lam0 : Fin n' → Fin (m + 1) → ℤ) (hnu : lam0 = fl + rest) (h1 : IsDominant fl)
    (h2 : IsDominant rest) (e : Edge W Qq (m + 1)), IsEdge p n' r e →
  ∀ (nb n2 T oS tT D1 cStar c' : ℕ), cStar + oS ≤ c' → 2 * (D1 + 1) ≤ c' →
  ∀ (Fvb Sy : Fin nb → Vsp Kf fl) (sh : Fin n2 → Vsp Kf rest),
    (∀ b, Fvb b ∈ scale (algebraMap O Kf w ^ (-(T : ℤ))) (HL (O := O) ι σ fl e.src)) →
    (∀ b, Fvb b - Sy b ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r fl e)) →
    (∀ b, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.src = e.src → e' ≠ e →
      Fvb b ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r fl e')) →
    (∀ b, Sy b ∈ Re p ι σ w r fl e) →
    (∀ i, sh i ∈ Re p ι σ w r rest e ∧
      sh i ∈ scale (algebraMap O Kf w ^ (-(oS : ℤ))) (HL (O := O) ι σ rest e.src)) →
    (∀ c : Fin nb × Fin n2 → O, (∃ x, IsUnit (c x)) →
      ∃ G : Module.Dual Kf (Vsp Kf lam0),
        G ∈ scale (algebraMap O Kf w ^ (-(tT : ℤ))) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)) ∧
        G ∈ Re' p ι σ w r lam0 e ∧
        (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
          G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
        ValLe (p : O) D1 (be p r lam0 (∑ x, c x • mulV hnu h1 h2 (Sy x.1) (sh x.2)) G)) →
    EdgeFam (W := W) (O := O) p n' ι σ w r lam0 (T + oS) tT D1 cStar e (nb * n2)

end Formalism.MainNotions.Pf14
