import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairingStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCosetStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

theorem GlobalTheory.Ex.OneGen.thG_val_of_prim : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → (∀ x (c : F), ThG A.A A.L ρ m th x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG A.A A.L ρ m th x (fnOf c) ∧ v c = 0 := by
  rintro ⟨hLL, h₁, h₂, h₃, h₄⟩ V _ _ _ _ hV ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hw th ϑ hex hprim m hmo hmu hm
  have hAdm : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨f, hf, hfs, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hLL V _ hAdm D A G hG U F (m ^ 2) (pow_pos hmo.pos 2)
  obtain ⟨ua, ub⟩ := GlobalTheory.T.theta_constant_valuations_units_every_coset hLL h₁ h₂ h₃ h₄ V hV ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hw th ϑ hex hprim m hmo hmu
  refine ⟨fun x c H => ?_, ?_⟩
  · obtain ⟨hx, t, ht⟩ := (thG_iff A ρ m th x c).1 H
    obtain ⟨p, hp⟩ := hfs x hx
    refine (ua p x t c ((hf p x).2 hp.symm) ht).1 0 fun χ => div_nonneg ?_ (Nat.cast_nonneg _)
    by_cases h : m • χ + p.y = 0
    · rw [h, QForm.Q_zero hϖ D hQ]; simp
    · exact_mod_cast zero_le_one.trans (QForm.Q_pos hϖ D hQ h)
  · obtain ⟨p', x', t, c, -, hx', -, hc, hz⟩ := ub m (by omega) dvd_rfl (TorusExt.qkZero D.tau_bimult F _) _ rfl
      ((hf _ _).2 rfl)
    exact ⟨x', c, (thG_iff A ρ m th x' c).2 ⟨(hx' w₀ hw.1).1, t, hc⟩, hz⟩
