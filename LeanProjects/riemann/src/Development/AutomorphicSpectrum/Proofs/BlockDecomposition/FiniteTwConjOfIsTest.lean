import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Matrix Topology Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.KerTwFin

section Rational

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem discreteTopology_range : DiscreteTopology (ratGL E n).range :=
  GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n

theorem isClosed_range : IsClosed ((ratGL E n).range : Set (GA E n)) :=
  GroundTheory.Automorphic.AdelicGLn.isClosed_rationalGL E n

theorem injective_ratGL : Function.Injective (ratGL E n) :=
  GroundTheory.Automorphic.AdelicGLn.diagonal_injective E n

theorem finite_ratGL_mem {K : Set (GA E n)} (hK : IsCompact K) : {d : GL (Fin n) E | ratGL E n d ∈ K}.Finite := by
  have hcomp : IsCompact (K ∩ ((ratGL E n).range : Set (GA E n))) := hK.inter_right isClosed_range
  have hdisc : DiscreteTopology ↥(K ∩ ((ratGL E n).range : Set (GA E n))) :=
    DiscreteTopology.of_subset (s := ((ratGL E n).range : Set (GA E n))) discreteTopology_range inter_subset_right
  have hfin := hcomp.finite ⟨hdisc⟩
  refine (hfin.preimage (f := ratGL E n) injective_ratGL.injOn).subset fun d hd => ?_
  exact ⟨hd, d, rfl⟩

end Rational

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_thetaA : Continuous (thetaA E n) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h0 : Continuous fun g : GA E n => ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) :=
      Units.continuous_coe_inv
    exact (h0.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose
  · have h0 : Continuous fun g : GA E n => (g : Matrix (Fin n) (Fin n) (Ad E)) := Units.continuous_val
    exact (h0.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose

theorem finite_kernel {φ : GA E n → ℂ} (hφ : HasCompactSupport φ) {C C' : Set (GA E n)} (hC : IsCompact C)
    (hC' : IsCompact C') :
    {d : GL (Fin n) E | ∃ x ∈ C, ∃ y ∈ C', φ (x⁻¹ * ratGL E n d * thetaA E n y) ≠ 0}.Finite := by
  have hK : IsCompact (C * tsupport φ * (thetaA E n '' C')⁻¹) :=
    (hC.mul hφ).mul (hC'.image continuous_thetaA).inv
  refine (finite_ratGL_mem hK).subset ?_
  rintro d ⟨x, hx, y, hy, h⟩
  have hd : ratGL E n d =
      x * (x⁻¹ * ratGL E n d * thetaA E n y) * (thetaA E n y)⁻¹ := by group
  change ratGL E n d ∈ C * tsupport φ * (thetaA E n '' C')⁻¹
  rw [hd]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx (subset_tsupport _ h))
    (Set.inv_mem_inv.2 (mem_image_of_mem _ hy))

theorem finite_twConj {φ : GA E n → ℂ} (hφ : HasCompactSupport φ) {C : Set (GA E n)} (hC : IsCompact C) :
    {d : GL (Fin n) E | ∃ x ∈ C, φ (twConj (thetaA E n) x (ratGL E n d)) ≠ 0}.Finite :=
  (finite_kernel hφ hC hC).subset fun _ ⟨x, hx, h⟩ => ⟨x, hx, x, hx, h⟩

theorem finite_twConj_of_isTest {φ : GA E n → ℂ} (hφ : IsTest φ) {C : Set (GA E n)} (hC : IsCompact C) :
    {d : GL (Fin n) E | ∃ x ∈ C, φ (twConj (thetaA E n) x (ratGL E n d)) ≠ 0}.Finite :=
  finite_twConj hφ.supp hC

theorem kerFin : PositivityTheory.Rg.BcB.D4.KerFin := fun _ _ _ _ _ _ hφ _ hC => finite_twConj_of_isTest hφ hC

end GlobalTheory.CompanionTheory.KerTwFin

end
