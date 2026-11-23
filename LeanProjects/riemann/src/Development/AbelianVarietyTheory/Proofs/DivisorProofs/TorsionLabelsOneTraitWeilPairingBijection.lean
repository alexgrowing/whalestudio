import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabTors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsIffPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LabTorsTrait

open GlobalTheory.ArcPull GlobalTheory.Mum.Recog

theorem labTors_of_oneTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A),
    OneTrait D.toPre A lab → ∀ k : ℕ, 1 ≤ k → LabTors D.toPre A k (lab k) := by
  intro R _ _ _ hR D A lab hT k hk
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, iφ, _, hG, ha, c, H⟩ := hT
  have := hR.2
  have : CharZero W := (RingHom.charZero_iff iφ).1 inferInstance
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB' := D'.tau_bimult
  have c' : Compat φ (Kb W) := c
  obtain ⟨f', hf'⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws W (maximalIdeal W) bW D' A' G' hG U' (Kb W) k hk
  obtain ⟨ε, hε, iε, oε, wε⟩ := exists_ptHom ha c' em
  have e : ∀ p, f' (tr hD c' em hB' p) = ε (lab k p) := fun p => by
    obtain ⟨p₁, h₁, h₂, h₃⟩ := (lies_iff hD c' em hB' p (tr hD c' em hB' p)).2 rfl
    exact ((hf'.1 _ _).1 (H k hk p p₁ _ _ h₁ h₂ h₃ ((hε _ _).1 rfl))).symm
  have pw : ∀ x : TFK (R := R) (Kb R) ⟶ A.A, ε x ^ k = 1 ↔ x ^ k = 1 := fun x => by
    rw [← map_pow, ← map_one ε, iε.eq_iff]
  have hp : ∀ p, lab k p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U'.ext
    rw [← pw, ← e]
    exact (((hf'.1 _ _).2 rfl) w hw).1
  refine ⟨fun y hy => ?_, hp, fun p q => ?_, fun p q r h => ?_, fun p q z => ?_⟩
  · obtain ⟨p', hp'⟩ := hf'.2.1 (ε y) ((pw y).2 hy)
    obtain ⟨p, rfl⟩ := (tr_bij hD c' em hB' hk).2 p'
    exact ⟨p, iε (by rw [← e, hp'])⟩
  · rw [← iε.eq_iff, ← e, ← e, hf'.2.2.1, tr_equiv]
  · apply iε
    rw [map_mul, ← e, ← e, ← e]
    exact hf'.2.2.2.1 _ _ _ ((tr_add hD c' em hB' p q r).2 h)
  · rw [← tr_weil hD c' em hB' hk p q z, wε k _ _ (hp p) (hp q) z, ← e, ← e]
    exact hf'.2.2.2.2 _ _ (Units.map em.toRingHom.toMonoidHom z)

end GlobalTheory.Mum.LabTorsTrait
