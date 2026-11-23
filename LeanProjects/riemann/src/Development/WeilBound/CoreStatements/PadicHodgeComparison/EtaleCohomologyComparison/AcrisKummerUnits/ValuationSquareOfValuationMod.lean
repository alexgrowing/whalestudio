import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparableQuotientOfValuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectivePreservesClosednessComparabilityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalInductionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIdempotentComplementIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationDichotomyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationOfLocalDichotomyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparableModSquareLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DichotomyOfComparableModSquareStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialRootsOfClosedQuotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedPolynomialSplitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedUnitCoefficientRootStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonPolygonSlopeExistenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationOfDichotomyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationLocalToGlobalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowerDivisibilityRootExtractionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyIntegrallyClosedOfNewtonStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLocalizationAwayInRingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalizationPreservesClosednessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationPowerIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleSurjectiveLocalSectionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOverIdempotentPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOrthogonalIdempotentSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerIdealTorsionFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerQuotientExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerMorphismCompatibleStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem CrystallineSemistableComparison.RL.surj_pass : ∀ {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T), Function.Surjective φ → (Aic S → Aic T) ∧ (Val0 S → Val0 T) := GlobalTheory.T.surjective_preserves_closedness_comparability

theorem CrystallineSemistableComparison.RL.glue : ∀ {S : Type} [CommRing S] (Q : S → Prop), Q 0 → (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → Q e → Q (e * e')) → (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → Q e → Q e' → Q (e + e')) → (∀ m : Ideal S, m.IsMaximal → ∃ e, IsIdempotentElem e ∧ e ∉ m ∧ Q e) → Q 1 := GlobalTheory.T.idempotent_local_induction

theorem CrystallineSemistableComparison.RL.dich_comp : ∀ {S : Type} [CommRing S] (ϖ : S) (P : Ideal S), P.IsPrime → (Val ϖ → Dich (Ideal.Quotient.mk (compI P) ϖ)) ∧ (ϖ ∈ nonZeroDivisors S → Ideal.Quotient.mk (compI P) ϖ ∈ nonZeroDivisors (S ⧸ compI P)) := GlobalTheory.T.idempotent_localization_dichotomy

theorem CrystallineSemistableComparison.RL.val_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S), (∀ m : Ideal S, m.IsMaximal → Dich (Ideal.Quotient.mk (compI m) ϖ)) → Val ϖ := GlobalTheory.T.valuation_of_local_dichotomy

theorem CrystallineSemistableComparison.RL.valuation_square_of_valuation_mod : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Val0 (S ⧸ Ideal.span {ϖ ^ 2}) → ∀ P : Ideal S, P.IsPrime → ∀ f g : S ⧸ compI P, f ∈ Ideal.span {g, Ideal.Quotient.mk (compI P) ϖ ^ 2} ∨ g ∈ Ideal.span {f, Ideal.Quotient.mk (compI P) ϖ ^ 2} := GlobalTheory.T.comparable_mod_square_localization

theorem CrystallineSemistableComparison.RL.dich_of_mod : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := GlobalTheory.T.dichotomy_of_comparable_mod_square

theorem CrystallineSemistableComparison.RL.step_comp : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S ⧸ Ideal.span {ϖ ^ 2}) → Step ϖ := GlobalTheory.T.newton_approximation_of_dichotomy

theorem CrystallineSemistableComparison.RL.step_glob : ∀ {S : Type} [CommRing S] (ϖ : S), (∀ m : Ideal S, m.IsMaximal → Step (Ideal.Quotient.mk (compI m) ϖ)) → Step ϖ := GlobalTheory.T.newton_approximation_local_to_global

theorem CrystallineSemistableComparison.RL.pow_dvd : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z := GlobalTheory.T.power_divisibility_root_extraction

theorem CrystallineSemistableComparison.RL.aic_limit : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Step ϖ → (∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z) → Aic S := GlobalTheory.T.absolutely_integrally_closed_of_newton

theorem CrystallineSemistableComparison.RL.int_closed : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ x : Localization.Away ϖ, IsIntegral S x → ∃ y : S, algebraMap S (Localization.Away ϖ) y = x := GlobalTheory.T.integral_localization_away_in_ring

theorem CrystallineSemistableComparison.RL.loc_aic : ∀ {S : Type} [CommRing S] (ϖ : S), (Val ϖ → Loc S ∧ Loc (Localization.Away ϖ)) ∧ (Aic S → Aic (Localization.Away ϖ)) := GlobalTheory.T.localization_preserves_closedness

theorem CrystallineSemistableComparison.RL.val_pow : ∀ {S : Type} [CommRing S] (ϖ : S) (k : ℕ), k ≠ 0 → (Val (ϖ ^ k) ↔ Val ϖ) ∧ (IsAdicComplete (Ideal.span {ϖ ^ k}) S → IsAdicComplete (Ideal.span {ϖ}) S) := GlobalTheory.T.valuation_power_iff

theorem CrystallineSemistableComparison.RL.split_pt : ∀ {S : Type} [CommRing S] , Aic S → Loc S → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), Etale f → Surjective f → ∀ m : Ideal S, m.IsMaximal → ∃ e : S, IsIdempotentElem e ∧ e ∉ m ∧ SecOn f e := GlobalTheory.T.etale_surjective_local_section

theorem CrystallineSemistableComparison.RL.sec_rules : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), SecOn f 0 ∧ (∀ e e' : S, SecOn f e → SecOn f (e * e')) ∧ (SecOn f 1 → ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _) := GlobalTheory.T.section_over_idempotent_properties

theorem CrystallineSemistableComparison.RL.sec_add : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)) (e e' : S), IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → SecOn f e → SecOn f e' → SecOn f (e + e') := GlobalTheory.T.section_orthogonal_idempotent_sum

theorem CrystallineSemistableComparison.RL.pd_quot : ∀ {S : Type} [CommRing S] , TF S → ∀ I J : Ideal S, PdI I → (∀ x ∈ I, x ∈ J → ∀ k : ℕ, k ≠ 0 → ∀ y : S, (k.factorial : S) * y = x ^ k → y ∈ J) → ∃ δ : DividedPowers (I.map (Ideal.Quotient.mk J)), IsPd (Ideal.Quotient.mk J) I δ := GlobalTheory.T.divided_power_quotient_exists

theorem CrystallineSemistableComparison.RL.pd_mor : ∀ {S : Type} [CommRing S] {S' E E' : Type} [CommRing S'] [CommRing E] [CommRing E'] (π : S →+* E) (π' : S' →+* E') (I : Ideal S) (I' : Ideal S') {J : Ideal E} {J' : Ideal E'} (δ : DividedPowers J) (δ' : DividedPowers J') (F₀ : S →+* S') (F : E →+* E'), Function.Surjective π → PdI I → IsPd π I δ → IsPd π' I' δ' → (∀ x ∈ I, F₀ x ∈ I') → (∀ x, F (π x) = π' (F₀ x)) → DividedPowers.IsDPMorphism δ δ' F := GlobalTheory.T.divided_power_morphism_compatible
