import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisFixesQuotientPointsOfRational
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelTorsionPointOfComesFromBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQkPointExtensionOfDividedDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DivGalFix

open GlobalTheory.TorusExt

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qkPt_rational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ q : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ q₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) q₀ q := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD q
  have hB := P.D.tau_bimult
  have ha : (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp
      (algebraMap (FractionRing R) (FractionRing R)) = algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R)) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p₀, hy⟩ := GlobalTheory.T.exists_levelTorsionPoint_of_comesFromBase L R hR t P iw s ε e hε hs hD q.y
  set p₁ := qkExt hB (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ha p₀ with hp₁
  have h0 : l.M' • (q.g - p₁.g) = iota hB (AlgebraicClosure (FractionRing R)) 0 := by
    rw [smul_sub, qk_nsmul hB, qk_nsmul hB, map_zero]
    show iota hB _ q.y - iota hB _ p₀.y = 0
    rw [hy, sub_self]
  obtain ⟨r₀, hr⟩ := GlobalTheory.T.exists_qkPoint_extension_of_divided_data L R hR t P iw s ε e hε hs hD (qkMk hB 0 (q.g - p₁.g) h0) rfl
  rw [qkExt_iff hB _ ha] at hr
  refine ⟨qkAdd hB p₀ r₀, ?_⟩
  rw [qkExt_iff hB _ ha, qkExt_qkAdd, ← hr, ← hp₁]
  apply qk_ext
  · show q.y = p₀.y + 0
    rw [hy, add_zero]
  · show q.g = p₁.g + (q.g - p₁.g)
    abel

theorem qkExt_equiv_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p p' : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M'), QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv P.D.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD σ p p' hpp'
  refine GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational R P.D l.M' (fun q => ?_) σ.toAlgHom p p' hpp'
  obtain ⟨q₀, hq⟩ := qkPt_rational L R hR t P iw s ε e hε hs hD q
  exact ⟨q₀, q, hq, qk_equiv_refl P.D.tau_bimult q⟩

end GlobalTheory.DivGalFix
