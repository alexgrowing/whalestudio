import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEvenCubicalValuesNotMemMaximalIdealPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInIffScalarMem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitsK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataScalarsMemMaximalIdealTendstoZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodScalarCoordinatePolarisedDataLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodScalarCoordinatesSymmBimultUpToUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiScalarEqUnitMulProdPeriodsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPol

theorem psi_pos_tendsto : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Q.IsPos (maximalIdeal R) → (∀ χ : D'.X, χ ≠ 0 → D'.PsiIn χ (maximalIdeal R)) ∧ ∀ n : ℕ, {χ : D'.X | ¬ D'.PsiIn χ (maximalIdeal R ^ n)}.Finite := by
  intro R _ _ _ hR Q D' r W pr hpr hlim xe hc w hw hψ hW hQ
  obtain ⟨hN, hI, -, -⟩ := hR
  have hk0 : ∀ a b, ∃ k, Q.TauCoord a b k ∧
      (a = b → a ≠ 0 → ∃ s ∈ maximalIdeal R, (k : FractionRing R) = algebraMap R _ s) := by
    intro a b
    by_cases h : a = b ∧ a ≠ 0
    · obtain ⟨rfl, ha⟩ := h
      obtain ⟨s, hs, k, hk, hc⟩ := hQ a ha
      exact ⟨k, hc, fun _ _ => ⟨s, hs, hk⟩⟩
    · obtain ⟨k, hk⟩ := GlobalTheory.T.exists_periodScalarCoordinate_polarisedData_local R Q a b
      exact ⟨k, hk, fun e ne => (h ⟨e, ne⟩).elim⟩
  choose k hk hkp using hk0
  obtain ⟨hs, ha⟩ := GlobalTheory.T.periodScalarCoordinates_symm_bimult_up_to_units R Q k hk
  obtain ⟨ga', a', h'⟩ := GlobalTheory.exists_psiScal R D'
  obtain ⟨hp, ht⟩ := GlobalTheory.T.tensorData_scalars_mem_maximalIdeal_tendsto_zero R Q.X k hs ha (fun y hy => hkp y y rfl hy) W hW (fun z => a' (xe.symm z))
    (fun z => by simpa only [AddEquiv.apply_symm_apply] using GlobalTheory.T.tensorData_psiScalar_eq_unit_mul_prod_periods R Q D' W pr xe w hψ k hk ga' a' h' (xe.symm z))
  refine ⟨fun χ hχ => ?_, fun n => ((ht n).preimage xe.injective.injOn).subset fun χ hχ hm => hχ ?_⟩
  · obtain ⟨s, hs, e⟩ := hp (xe χ) (fun h0 => hχ (xe.map_eq_zero_iff.1 h0))
    rw [AddEquiv.symm_apply_apply] at e
    exact (GlobalTheory.PsiScalIn.main_local D' ga' a' h' χ _).2 ⟨s, hs, e.symm⟩
  · obtain ⟨s, hs, e⟩ := hm
    rw [AddEquiv.symm_apply_apply] at e
    exact (GlobalTheory.PsiScalIn.main_local D' ga' a' h' χ _).2 ⟨s, hs, e.symm⟩

end GlobalTheory.Mum.TensPol
