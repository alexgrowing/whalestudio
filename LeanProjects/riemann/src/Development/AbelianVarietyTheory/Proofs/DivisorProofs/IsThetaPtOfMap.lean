import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaDown

theorem isThetaPt_of_map : ∀ (B : Scheme.{0}) [IsLocallyNoetherian B] (P : PolAV B) (K C : Type) [Field K] [Field C] (j : K →+* C) (s : Sp K ⟶ B) (x : Sp C ⟶ B) (hx : spMap j ≫ s = x) (k : ℕ) (J : Type) (p : J → (Over.mk s ⟶ P.A)) (w : J → K), (∀ i, p i ^ k ^ 2 = 1) → IsThetaPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (j (w i))) → IsThetaPt P k p (fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (w i)) := by
  intro B _ P K C _ _ j s x hx k J p w hp H
  have h₁ : Laws := GlobalTheory.firstFiveLaws.1
  have h₂ : Laws2 := GlobalTheory.firstFiveLaws.2.1
  have hk : Odd k := H.1
  let eC : Γ(Sp C, ⊤) ≃+* C := (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv
  have hkC : (k : C) ≠ 0 := by
    have := H.2.1.map eC.toRingHom
    rw [map_natCast] at this
    exact this.ne_zero
  have hkK : IsUnit (k : K) := IsUnit.mk0 _ fun h0 => hkC (by rw [← map_natCast j, h0, map_zero])
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.Ex.Specialise.exists_isThetaPt_local h₁ h₂ P s hk hkK p hp
  have hC := GlobalTheory.Ex.Specialise.isThetaPt_map h₂ P j hx hw₀
  haveI : IsLocalRing Γ((Over.mk x).left, ⊤) := eC.symm.isLocalRing
  obtain ⟨u, hu⟩ := GlobalTheory.ThetaUniq.exists_unit_over h₁.globalFns P hk
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local _ x hC) (GlobalTheory.ThetaUniq.isThetaPtOver_of_local _ x H)
  set c : C := eC (u : Γ((Over.mk x).left, ⊤)) with hcdef
  have hc : ∀ i, j (w i) = c * j (w₀ i) := fun i => by
    have q := (congrArg eC (hu i)).trans (map_mul eC _ _)
    exact (eC.apply_symm_apply (j (w i))).symm.trans (q.trans (congrArg (_ * ·) (eC.apply_symm_apply (j (w₀ i)))))
  have hu0 : c ≠ 0 := fun h0 => (u.isUnit.map eC.toRingHom).ne_zero h0
  by_cases hz : ∀ i, w₀ i = 0
  · have e : w = w₀ := funext fun i => j.injective (by rw [hc, hz, map_zero, MulZeroClass.mul_zero])
    subst e
    exact hw₀
  · push_neg at hz
    obtain ⟨i₀, hi₀⟩ := hz
    have hd : j (w i₀ / w₀ i₀) = c := by
      rw [map_div₀, hc, mul_div_assoc, div_self ((map_ne_zero j).2 hi₀), _root_.mul_one]
    have hd0 : w i₀ / w₀ i₀ ≠ 0 := fun h0 => hu0 (by rw [← hd, h0, map_zero])
    have e : ∀ i, w i = (w i₀ / w₀ i₀) * w₀ i := fun i => j.injective (by rw [map_mul, hd, hc])
    have := GlobalTheory.Ex.Specialise.isThetaPt_mul P hw₀ hd0
    convert this using 2 with i
    rw [e i]

end GlobalTheory.Mum.ThetaDown
