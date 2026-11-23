import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Definitions.Degenerations.MemOfIsIntegralElem
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.values_galois_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ m : ℕ, Odd m → IsUnit (m : R) → ∀ v : QkPt D.toPre (Kb R) (m ^ 2) → Kb R, (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) (m ^ 2) → QkPt D.toPre C (m ^ 2)) (q : QkPt D.toPre (Kb R) (m ^ 2) → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i)) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) (m ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p' := by
  intro R _ _ _ hR D A lab hT m hm hmu v H σ
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em₀, hW, hφ, hloc, -, -, -, -⟩ := hT
  obtain ⟨C, _, _, _, _, _, _, hC⟩ := GlobalTheory.Ex.StepInh.exists_cExt W hW
  have hg : Function.Injective ((algebraMap (FractionRing W) C).comp ((algebraMap W (FractionRing W)).comp φ)) :=
    (algebraMap (FractionRing W) C).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  letI : Algebra (FractionRing R) C := (IsFractionRing.lift hg).toAlgebra
  have hA : ∀ r : R, algebraMap (FractionRing R) C (algebraMap R _ r) =
      algebraMap (FractionRing W) C (algebraMap W _ (φ r)) := fun r => IsFractionRing.lift_algebraMap hg r
  haveI := hloc
  have hCR : GlobalTheory.Ex.CExt R (maximalIdeal R) C :=
    ⟨fun r => by rw [hA]; exact hC.1 _, fun r hr => by rw [hA]; exact hC.2 _ (map_nonunit φ r hr)⟩
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, nu, -⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.firstFiveLaws.1 R D.toPre D.psi_even D.tau_bimult C ⊤
    (fun _ => trivial)
  have hB := D.tau_bimult
  let em : Kb R →ₐ[FractionRing R] C := IsAlgClosed.lift
  have hq := ((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult C N nu).2.2.2.2 (m ^ 2)).1
  choose e₁ he₁ using fun i => GlobalTheory.LabTrans.exists_ext hB em i
  choose e₂ he₂ using fun i => GlobalTheory.LabTrans.exists_ext hB σ i
  choose qq hqq using fun x : QkPt D.toPre C (m ^ 2) => (hq x).exists
  obtain ⟨s, hs⟩ := H C hCR em N nu e₁ (fun i => qq (e₁ i)) he₁ (fun i => hqq _)
  obtain ⟨s', hs'⟩ := H C hCR (em.comp σ) N nu (fun i => e₁ (e₂ i)) (fun i => qq (e₁ (e₂ i)))
    (fun i => GlobalTheory.LabTrans.qkExt_trans (he₂ i) (he₁ (e₂ i))) (fun i => hqq _)
  have key : ∀ p p', QkExt σ.toRingHom p p' → em (σ (v p)) = ((s' * s⁻¹ : Cˣ) : C) * em (v p') := by
    intro p p' h
    obtain rfl : e₂ p = p' := GlobalTheory.LabTrans.ext_unique hB σ (he₂ p) h
    have h1 := hs' p
    have h2 := hs (e₂ p)
    rw [AlgHom.comp_apply] at h1
    rw [h1, h2, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left]
  have emi : Function.Injective em := em.toRingHom.injective
  by_cases hex : ∃ p p', QkExt σ.toRingHom p p' ∧ v p' ≠ 0
  · obtain ⟨p₀, p₀', h₀, hv₀⟩ := hex
    have hσ0 : σ (v p₀) ≠ 0 := by
      intro h0
      have k0 := key p₀ p₀' h₀
      rw [h0, map_zero] at k0
      exact hv₀ ((map_eq_zero em).1 ((mul_eq_zero.1 k0.symm).resolve_left (Units.ne_zero _)))
    refine ⟨Units.mk0 (σ (v p₀) / v p₀') (div_ne_zero hσ0 hv₀), fun p p' h => emi ?_⟩
    have hne : em (v p₀') ≠ 0 := (map_ne_zero em).2 hv₀
    rw [Units.val_mk0, map_mul, map_div₀, key p p' h, key p₀ p₀' h₀]
    field_simp
  · push_neg at hex
    refine ⟨1, fun p p' h => ?_⟩
    have k := key p p' h
    rw [hex p p' h, map_zero, mul_zero] at k
    rw [hex p p' h, mul_zero]
    exact (map_eq_zero em).1 k
