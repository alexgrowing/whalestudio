import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieOcExistsSpMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomAtIffOfSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersionOfAffinePointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionRestrictClopenFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorPreObjectOfSiegelPullbackStatement

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem lieGeom_locus_closed : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), (∃ z : T ⟶ Z, z ≫ j = g) ↔ ((∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ g ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ g)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (β : R →+* k), x ≫ g ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ g)) := by
  intro p _ D R _ b N hN3 hNp h M B _ ζ S s₁ t c e he hK X _ πX AX _ _ φX φ₂X actX ηX hpb hsq hros heta
  have hab : IsAbelianScheme AX := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab hpb
  obtain ⟨Z₁, i₁, hi₁, hZ₁⟩ := lieHer_closed b (πX ≫ t) AX hab.smooth actX
  obtain ⟨o, ho⟩ := GlobalTheory.T.exists_harrisTaylorPreObject_of_siegelPullback p D R b N h M B ζ S s₁ t c e he hK X πX AX φX φ₂X actX ηX hpb hsq hros heta
  obtain ⟨U, hU, hUx⟩ := PreEta.exists_clopen_geomAt p D R b N hN3 hNp X (πX ≫ t) o
  obtain ⟨Z, j, hj, hZ⟩ := GlobalTheory.T.closedImmersion_restrict_clopen_factorization i₁ hi₁ U hU
  refine ⟨Z, j, hj, fun T g => ?_⟩
  rw [hZ T g]
  apply and_congr
  · constructor
    · rintro ⟨y, rfl⟩ R' _ β x hx
      exact (hZ₁ R' β (x ≫ y ≫ i₁) (by simpa only [Category.assoc] using hx)).1 ⟨x ≫ y, by simp⟩
    · intro H
      refine GlobalTheory.T.exists_factor_closedImmersion_of_affine_points i₁ hi₁ g fun R' _ x => ?_
      obtain ⟨β, hβ⟩ := lieOc_exists_spMap (x ≫ g ≫ πX ≫ t)
      exact (hZ₁ R' β (x ≫ g) (by simpa only [Category.assoc] using hβ)).2 (H R' β x hβ)
  · constructor
    · intro hg k _ _ x β _
      refine (ho k (x ≫ g)).1 ((hUx k (x ≫ g)).1 ?_)
      rintro _ ⟨u, rfl⟩
      exact hg ⟨x.base u, by simp⟩
    · intro H
      rintro _ ⟨τ, rfl⟩
      obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point T τ
      obtain ⟨β, hβ⟩ := lieOc_exists_spMap (x ≫ g ≫ πX ≫ t)
      have hG := (hUx k (x ≫ g)).2 ((ho k (x ≫ g)).2 (H k x β hβ))
      obtain ⟨u, hu⟩ : τ ∈ Set.range x.base := by rw [hx]; rfl
      exact hG ⟨u, by simp [hu]⟩

end GlobalTheory.UPel.HT
