import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DividedPowersValuationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearsIdempotentConductorIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearsIdempotentOfExponentBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearsIdempotentOfTraceDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfTraceDualElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDifferentExponentDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValVpNatCastPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFourthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFifthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodDenominatorBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodValuationBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodConjugateIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodProductIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledRestrictionEndomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodTraceIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodNormIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodGaloisIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowersPrimeUniqueStatement

noncomputable section

open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.CMLatticeRow

theorem qt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (l : ℕ), l.Prime → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O, ClearsIdem K (condQ 𝔣 Q) D ↔ ClearsIdem K 𝔣 D :=
  GlobalTheory.T.clears_idempotent_conductor_iff

theorem condT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)), 𝔣 ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ k : ℕ, (∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O, ClearsIdem K (⊤ : Ideal (OF E)) D → ClearsIdem K 𝔣 ((l : O) ^ k * D) :=
  GlobalTheory.T.clears_idempotent_of_exponent_bound

theorem dualCrit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], Nat.card (E →+* K) = Module.finrank ℚ E → ∀ D : O, (∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y) → ClearsIdem K (⊤ : Ideal (OF E)) D :=
  GlobalTheory.T.clears_idempotent_of_trace_dual

theorem unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ discr E → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = σ y :=
  GlobalTheory.T.exists_lift_of_trace_dual_element

theorem diffEx : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∃ D : O, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → val_vp O l (algebraMap O K D) = ((diffExp_vp l P : ℚ) : WithTop ℚ)) ∧ ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y :=
  GlobalTheory.T.exists_different_exponent_denominator

theorem valPow : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], ∀ (l : ℕ), l ≠ 0 → (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ k : ℕ, val_vp O l (algebraMap O K ((l : O) ^ k)) = ((k : ℚ) : WithTop ℚ) :=
  GlobalTheory.T.valuation_pow_eq_alt

theorem a1 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) :=
  GlobalTheory.T.cm_type_period_integral_first

theorem a2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ σ : E →+* K, IsSat (eigLat ρ σ) ∧ (∃ g : H, g ≠ 0 ∧ eigLat ρ σ = O ∙ g) ∧ Module.Free O (eigLat ρ σ) ∧ Module.finrank O (eigLat ρ σ) = 1 ∧ ∃ C : Submodule O H, IsCompl (eigLat ρ σ) C :=
  GlobalTheory.T.cm_type_period_integral_second

theorem a3 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) → iSupIndep (fun σ : E →+* K => eigLat ρ σ) ∧ ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ :=
  GlobalTheory.T.cm_type_period_integral_third

theorem a4 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ i, Fil ⊓ eigLat ρ (φ i) = eigLat ρ (φ i) :=
  GlobalTheory.T.cm_type_period_integral_fourth

theorem a5 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0 :=
  GlobalTheory.T.cm_type_period_integral_fifth

theorem pb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧ val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D) :=
  GlobalTheory.T.cm_type_period_denominator_bound

theorem la : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ i, ∃! N, IsLower ρ (φ i) (e i) (f i) N :=
  GlobalTheory.T.cm_type_period_valuation_bound

theorem lb1 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → ∀ i, ∃! M : Module.End O H, IsScaledRestr D (N i) M :=
  GlobalTheory.T.cm_type_period_integrality

theorem lb2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) ∧ ∀ i j, N i * N j = 0 :=
  GlobalTheory.T.cm_type_period_conjugate_integral

theorem lb3 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) ∧ ∀ i j x y, B.baseChange K (N i x) (N j y) = 0 :=
  GlobalTheory.T.eigen_line_bilinear

theorem lc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (O : Type) [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H], Module.Free O H → ∀ (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) (I : Type) [Fintype I] (N : I → Module.End K (K ⊗[O] H)) (D : O) (M : I → Module.End O H), (∀ i, IsScaledRestr D (N i) (M i)) → (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) → (∀ i j, N i * N j = 0) → (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) → (∀ i j x y, B.baseChange K (N i x) (N j y) = 0) → ∀ (l : ℕ) (R : Type) [CommRing R] [Algebra O R] (t : I → R), (∀ x : R ⊗[O] H, ∃ y : R ⊗[O] H, (1 + nilPart l M R t) x = x + (lPrime l : R) • y) ∧ ((1 + nilPart l M R t) * (1 - nilPart l M R t) = 1 ∧ (1 - nilPart l M R t) * (1 + nilPart l M R t) = 1) ∧ (∀ a : OF E, Commute (1 + nilPart l M R t) ((ρ (ofF c a)).baseChange R)) ∧ ∀ x y : R ⊗[O] H, B.baseChange R ((1 + nilPart l M R t) x) ((1 + nilPart l M R t) y) = B.baseChange R x y :=
  GlobalTheory.T.scaled_restriction_endomorphisms

theorem det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → DetClaims K l Fil D e :=
  GlobalTheory.T.cm_type_period_trace_integral

theorem fa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) :=
  GlobalTheory.T.cm_type_period_norm_integral

theorem fb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → (∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧ val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D)) → (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) → FormClaims l φ ρ B D e f :=
  GlobalTheory.T.cm_type_period_galois_integral

theorem dp0 : ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R], (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) → ∃ γ₀ : DividedPowers (Ideal.span {(l : R)}), ∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)}, (m.factorial : R) * γ₀.dpow m y = y ^ m :=
  GlobalTheory.T.exists_divided_powers_prime

theorem dp1 : ∀ (l : ℕ), l.Prime → (∀ m : ℕ, (1 ≤ m → lPrimeExp l + padicValNat l m.factorial ≤ lPrimeExp l * m) ∧ m + 2 * padicValNat l m.factorial ≤ 2 * (lPrimeExp l * m)) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R], (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) → ∀ γ₀ : DividedPowers (Ideal.span {(l : R)}), (∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)}, (m.factorial : R) * γ₀.dpow m y = y ^ m) → ∃ γ : DividedPowers (Ideal.span {(lPrime l : R)}), (∀ m : ℕ, ∃ q : O, (m.factorial : O) * q = (lPrime l : O) ^ m ∧ ∀ x : R, γ.dpow m ((lPrime l : R) * x) = algebraMap O R q * x ^ m) ∧ (∀ (m : ℕ), ∀ y ∈ Ideal.span {(lPrime l : R)}, γ.dpow m y = γ₀.dpow m y) ∧ ∀ n : ℕ, 1 ≤ n → γ.IsSubDPIdeal (Ideal.span {(lPrime l : R) ^ n}) ∧ ∀ (r : ℕ) (m : Fin r → ℕ) (x : Fin r → R), (∀ i, x i ∈ Ideal.span {(lPrime l : R)}) → 2 * n * lPrimeExp l ≤ ∑ i, m i → ∏ i, γ.dpow (m i) (x i) ∈ Ideal.span {(lPrime l : R) ^ n} :=
  GlobalTheory.T.divided_powers_prime_unique

theorem statement : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro E _ _ _ _ 𝔣 h𝔣 l hl O _ _ _ _ K _ _ _ hlO hcard
    refine ⟨?_, fun Q _ hQl D => qt E 𝔣 Q l hl hQl O K hlO D⟩
    by_cases hdiv : ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal
    · obtain ⟨v, hv𝔣, hvl⟩ := hdiv
      have hl' : ¬ (l : ℤ) ∣ discr E := by
        obtain ⟨_, _, l', hl'p, _, hl'v, hdisc, _⟩ := h𝔣.2.2 v hv𝔣
        have hll : l' = l := by
          by_contra hne
          have hcop : IsCoprime ((l' : ℤ) : OF E) ((l : ℤ) : OF E) :=
            (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hl'p hl).2 hne)).intCast
          obtain ⟨a, b, hab⟩ := hcop
          have h1 : (1 : OF E) ∈ v.asIdeal := by
            rw [← hab]
            push_cast
            exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hl'v) (v.asIdeal.mul_mem_left _ hvl)
          exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
        exact hll ▸ hdisc
      refine ⟨(l : O) ^ condExp 𝔣 l, fun P _ => ?_, ?_⟩
      · rw [cNum_vp, if_pos ⟨v, hv𝔣, hvl⟩]
        exact valPow O K l hl.ne_zero hlO _
      · have h1 : ClearsIdem K (⊤ : Ideal (OF E)) (1 : O) := dualCrit E O K hcard 1 (fun σ y hy => by
          obtain ⟨z, hz⟩ := unram E l hl hl' O K hlO σ y hy
          exact ⟨z, by rw [hz, map_one, one_mul]⟩)
        have := condT E 𝔣 h𝔣.1 l hl (condExp 𝔣 l)
          (fun w hw => le_csSup (condExp_bdd 𝔣 hl.ne_zero) ⟨w, hw, rfl⟩) O K hlO 1 h1
        rwa [mul_one] at this
    · obtain ⟨D, hv, hD⟩ := diffEx E l hl O K hlO hcard
      refine ⟨D, fun P hP => ?_, ?_⟩
      · rw [cNum_vp, if_neg hdiv]
        exact hv P hP
      · have hz : ∀ w : HeightOneSpectrum (OF E), (l : OF E) ∈ w.asIdeal → expIn 𝔣 w ≤ 0 := by
          intro w hw
          have : ¬ w.asIdeal ∣ 𝔣 := fun h => hdiv ⟨w, h, hw⟩
          exact le_of_eq (multiplicity_eq_zero.2 this)
        have := condT E 𝔣 h𝔣.1 l hl 0 hz O K hlO D (dualCrit E O K hcard D hD)
        rwa [pow_zero, one_mul] at this
  · intro E _ _ _ 𝔣 h𝔣 l hl Q _ hQl O _ _ _ _ K _ _ _ hlO hcard D hD0 hD I _ φ hφ H _ _ ρ Fil B hL
    have hc : condQ 𝔣 Q ≠ ⊥ := by
      unfold condQ
      rw [Ne, Ideal.mul_eq_bot, not_or]
      refine ⟨h𝔣.1, ?_⟩
      rw [← Ne, ← Ideal.zero_eq_bot]
      exact Finset.prod_ne_zero_iff.2 fun q _ => by rw [Ideal.zero_eq_bot]; exact q.ne_bot
    have hDc : ClearsIdem K (condQ 𝔣 Q) D := (qt E 𝔣 Q l hl hQl O K hlO D).2 hD
    have hE : EigenClaims φ ρ Fil B D := by
      have hI := a1 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL
      exact ⟨hI, a2 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL,
        a3 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hI,
        a4 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL,
        a5 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL⟩
    refine ⟨hE, fun e f hg => ?_⟩
    have hP := pb E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg
    refine ⟨hP, ⟨la E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg, fun N hN => ?_⟩,
      det E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg,
      fb E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg hP
        (fa E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE)⟩
    obtain ⟨h1, h2⟩ := lb2 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg N hN
    obtain ⟨h3, h4⟩ := lb3 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg N hN
    exact ⟨lb1 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg N hN, h1, h2, h3, h4,
      fun M hM R _ _ t => lc E _ O K H hL.1 ρ B I N D M hM h1 h2 h3 h4 l R t⟩
  · intro l hl
    have hnum : ∀ m : ℕ, (1 ≤ m → lPrimeExp l + padicValNat l m.factorial ≤ lPrimeExp l * m) ∧
        m + 2 * padicValNat l m.factorial ≤ 2 * (lPrimeExp l * m) := by
      obtain ⟨h1, h2, _⟩ := GlobalTheory.T.divided_powers_valuations
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      by_cases h2l : l = 2
      · subst h2l
        have := h2 m hm
        rw [show lPrimeExp 2 = 2 from rfl]
        omega
      · have := h1 l m hl h2l hm
        rw [show lPrimeExp l = 1 from if_neg h2l]
        omega
    refine ⟨hnum, fun O _ _ _ _ hlO R _ _ htf => ?_⟩
    obtain ⟨γ₀, hγ₀⟩ := dp0 l hl O hlO R htf
    obtain ⟨γ, hγ⟩ := dp1 l hl hnum O hlO R htf γ₀ hγ₀
    exact ⟨γ, γ₀, hγ.1, hγ₀, hγ.2⟩

end GlobalTheory.CMLatticeRow
