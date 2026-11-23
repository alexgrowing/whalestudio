import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralAdeleIdealOfIdealPrincipalAndInterStatement
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev.DualIdeal

theorem smul_dual_iff {A V : Type} [CommRing A] [AddCommGroup V] [Module A V] (S : Subring A)
    (L : Submodule S V) (h : V → V → A) (hs : ∀ (a : A) x y, h x (a • y) = a * h x y)
    (hd : ∀ y, y ∈ L ↔ ∀ y' ∈ L, h y' y ∈ S) (t : S) (ht : IsUnit (t : A)) (y : V) :
    y ∈ (Ideal.span {t} : Ideal S) • L ↔ ∀ y' ∈ L, ∃ z ∈ (Ideal.span {t} : Ideal S), (z : A) = h y' y := by
  obtain ⟨u, hu⟩ := ht
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩ y' hy'
    refine ⟨t * ⟨_, (hd x).1 hx y' hy'⟩, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t), ?_⟩
    exact (hs t y' x).symm
  · intro H
    refine ⟨((u⁻¹ : Aˣ) : A) • y, (hd _).2 fun y' hy' => ?_, ?_⟩
    · obtain ⟨z, hz, e⟩ := H y' hy'
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      rw [hs, ← e, Subring.coe_mul, ← hu, mul_comm (w : A), Units.inv_mul_cancel_left]
      exact w.2
    · show (t : A) • _ = y
      rw [← hu, smul_smul, Units.mul_inv, one_smul]

theorem hAf_smul (I : AutInst) (a : I.E ⊗[I.F] Af I.F) (x y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I x (a • y) = a * hAf I x y := by
  unfold hAf Formalism.UG.hform
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

theorem mem_extId_smul_iff : ∀ (I : AutInst) (𝔞 : Ideal (𝓞 I.E)), 𝔞 ≠ ⊥ → ∀ y : Fin I.n → (I.E ⊗[I.F] Af I.F), y ∈ extId I 𝔞 • I.Lf ↔ ∀ y' ∈ I.Lf, ∃ z ∈ extId I 𝔞, (z : (I.E ⊗[I.F] Af I.F)) = hAf I y' y := by
  intro I 𝔞 h𝔞 y
  obtain ⟨⟨t, ht, e⟩, -⟩ := GlobalTheory.T.integralAdeleIdealOfIdeal_principal_and_inter I 𝔞 h𝔞
  rw [e]
  exact smul_dual_iff (IntAf I.F I.E) I.Lf (hAf I) (hAf_smul I) (GlobalTheory.T.adelicLattice_selfDual_hermitian I) t ht y

end GlobalTheory.RowLev.DualIdeal
