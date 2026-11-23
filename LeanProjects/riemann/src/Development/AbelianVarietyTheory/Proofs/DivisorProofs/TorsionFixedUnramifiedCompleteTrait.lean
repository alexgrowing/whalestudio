import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedOfQuotientClassesFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointsFirstCoordinateUnramifiedSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairsFixedOverUnramifiedExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnramTorsPull

theorem torsion_fixed_unramified : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → ∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hR D A G _ _ hG U W hW V _ _ _ φ hV hφ hcl n hn hnu j
  obtain ⟨hdvr, -, -⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  letI : Algebra (FractionRing R) (AlgebraicClosure (FractionRing V)) :=
    ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (IsLocalization.map (FractionRing V) φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ) :
        FractionRing R →+* FractionRing V)).toAlgebra
  have hc : ∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r)) := fun r => by
    show algebraMap (FractionRing V) _ (IsLocalization.map _ _ _ (algebraMap R _ r)) = _
    rw [IsLocalization.map_eq]
  have hk : IsUnit ((n ^ j : ℕ) : V) := by rw [Nat.cast_pow]; exact hnu.pow j
  obtain ⟨T₁, h₁, hb⟩ := GlobalTheory.T.quotientPoints_firstCoordinate_unramified_subring R D.toPre V φ hV hc (n ^ j) hk
  obtain ⟨T', h₂, hQ⟩ := GlobalTheory.T.torsionPairs_fixed_over_unramified_extension R hR D W hW V φ hV hφ hcl hc (n ^ j) hk T₁ h₁ hb
  have hT := h₁.trans h₂
  have hmem := hT.mem
  obtain ⟨hdvr', f, hf, hirr⟩ := hT
  refine ⟨T', hdvr', f, hf, hirr, fun σ hσ x hx => ?_⟩
  exact GlobalTheory.T.torsion_fixed_of_quotientClasses_fixed R hR D A G hG U V φ hc (n ^ j) (Nat.one_le_pow _ _ (by omega)) σ (fun v => hσ _ (hmem v)) (hQ σ hσ) x hx

end GlobalTheory.UnramTorsPull
