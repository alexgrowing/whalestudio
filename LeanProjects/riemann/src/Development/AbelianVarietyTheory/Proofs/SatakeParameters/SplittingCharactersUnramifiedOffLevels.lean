import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOffLevels

open GlobalTheory.IdemSupport GlobalTheory.ResLoc Formalism.L2.JoinChr

theorem exists_glue {A : Type} [CommRing A] {e : A} (he : e * e = e) (x : Aˣ) :
    ∃ y : Aˣ, (y : A) = e * (x : A) + (1 - e) ∧ e * ((y : A) - 1) = (y : A) - 1 := by
  have hxx : (x : A) * ((x⁻¹ : Aˣ) : A) = 1 := Units.mul_inv x
  refine ⟨⟨e * (x : A) + (1 - e), e * ((x⁻¹ : Aˣ) : A) + (1 - e), ?_, ?_⟩, rfl, ?_⟩
  · linear_combination (e * e) * hxx + (2 - (x : A) - ((x⁻¹ : Aˣ) : A)) * he
  · linear_combination (e * e) * hxx + (2 - (x : A) - ((x⁻¹ : Aˣ) : A)) * he
  · change e * (e * (x : A) + (1 - e) - 1) = e * (x : A) + (1 - e) - 1
    linear_combination ((x : A) - 1) * he

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem exists_part {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) {P : Pl D.host.E} (hu : χ.UnrAt P)
    {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {e : AE D} (hd : IsDelta Φ P e) (hpl : IsPlIdem D e P)
    (x : (AE D)ˣ) (h1 : finPart D (x : AE D) ∈ intAE D) (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) :
    ∃ y : (AE D)ˣ, (y : AE D) = e * (x : AE D) + (1 - e) ∧ c y = 1 := by
  obtain ⟨d0, d1, d2⟩ := id hd
  have he : e * e = e := hpl.1
  obtain ⟨N, hN, hker⟩ := exists_modulus hΦ c hc.1.1
  obtain ⟨y, hy, hsupp⟩ := exists_glue he x
  have hyP : Φ (y : AE D) P = Φ (x : AE D) P := by
    rw [hy, ev_add, ev_mul, d1, one_mul, ev_sub, ev_one, d1, sub_self, add_zero]
  have hv : Valued.v (Φ (x : AE D) P) = 1 := by
    have a : Valued.v (Φ (x : AE D) P) ≤ 1 := (hΦ.int _).1 h1 P
    have b : Valued.v (Φ ((x⁻¹ : (AE D)ˣ) : AE D) P) ≤ 1 := (hΦ.int _).1 h2 P
    have ab : Valued.v (Φ (x : AE D) P) * Valued.v (Φ ((x⁻¹ : (AE D)ˣ) : AE D) P) = 1 := by
      rw [← map_mul, ← ev_mul, Units.mul_inv, ev_one, map_one]
    refine le_antisymm a ?_
    rw [← ab]
    exact mul_le_of_le_one_right' b
  have hy1 : Valued.v (Φ (y : AE D) P) = 1 := by rw [hyP, hv]
  obtain ⟨k, k1, k2, k3⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P (Φ (y : AE D) P) (fun h => by
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1)
  rw [hy1] at k1
  rw [← k1, mul_one] at k2 k3
  obtain ⟨l, hl⟩ : ∃ l : (AE D)ˣ, (l : AE D) = 1 + e * (incA D (k : D.host.E) - 1) := ⟨locU hpl.1 k, rfl⟩
  obtain ⟨z, hz, hz'⟩ := exists_units_quot y l hl
  have hyz : Φ (y : AE D) P = Φ (z : AE D) P * algebraMap D.host.E _ (k : D.host.E) := by
    rw [← ev_inc hΦ]
    exact map_eq_mul_of_supp (evAt Φ P) d1 hz'
  have hcz : c z = 1 := by
    refine hker P z (map_eq_one_of_supp (infPart D) d0 hsupp hz')
      (fun Q hQ => map_eq_one_of_supp (evAt Φ Q) (d2 Q hQ) hsupp hz') ?_ ?_
    · rwa [hyz, map_mul, val_alg, ← k1, mul_one] at hy1
    · rwa [hyz, ← sub_one_mul, map_mul, val_alg, ← k1, mul_one] at k2
  have hcl : c l = 1 := by
    have e1 := hc.2 P e hpl k l hl
    have e2 : χ.locK P k = 1 := by
      refine hu (Formalism.L2.Host.atFin P k) ?_
      change Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1
      rw [val_alg]
      exact k1.symm
    rw [e2, Units.val_one] at e1
    exact Circle.ext e1
  exact ⟨y, hy, by rw [hz, map_mul, hcz, hcl, one_mul]⟩

theorem unrPl_of_chrEq {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) {P : Pl D.host.E} (h : χ.UnrAt P)
    (h' : χ.UnrAt (Formalism.DivisionValues.conjPl P)) : UnrPl P c := by
  intro e f hp x hx h1 h2
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd : IsDelta Φ P e := (of_isPrimeIdem hΦ hp).1
  rcases hp with ⟨hi, rfl⟩ | ⟨rfl, ⟨v, ε, hε, he⟩, ht⟩
  · have hc' : Formalism.IndefR.Lev.IsConjPl P (Formalism.DivisionValues.conjPl P) := GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl
    have hi' : Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl P) :=
      (supported_group_and_prime_idempotents (D.sp.V 0)).2.2.2 P _ e hi hc'
    have hd' : IsDelta Φ (Formalism.DivisionValues.conjPl P) (cA D e) := delta_of_isIdemAt hΦ hi'
    have pl : ∀ {w : Pl D.host.E} {a : AE D}, Formalism.L2.NTheta.IsIdemAt a w → IsPlIdem D a w := fun ha => by
      obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := ha
      exact ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
    obtain ⟨y, hy, hy1⟩ := exists_part hc h hΦ hd (pl hi) x h1 h2
    obtain ⟨z, hz, hz1⟩ := exists_part hc h' hΦ hd' (pl hi') x h1 h2
    have ho : e * cA D e = 0 := hi.1.2.1
    have e1 : x = y * z := Units.ext (by
      rw [Units.val_mul, hy, hz]
      linear_combination (-1 : AE D) * hx - ((x : AE D) - 1) ^ 2 * ho)
    rw [e1, map_mul, hy1, hz1, one_mul]
  · obtain ⟨y, hy, hy1⟩ := exists_part hc h hΦ hd ⟨delta_idem hΦ hd, ⟨v, ε, hε, Or.inr he⟩, ht⟩ x h1 h2
    have e1 : x = y := Units.ext (by rw [hy]; linear_combination (-1 : AE D) * hx)
    rw [e1, hy1]

theorem unrPl_of_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → ∀ t P, Good R t P → UnrPl P R.eta ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → UnrPl P (R.toLevCh.mu t j) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL t P hP
  obtain ⟨hg, hc, -⟩ := (GlobalTheory.GoodPrimes.good_primes R F hL).2.1 t P hP
  have hg' := (GlobalTheory.GoodPrimes.good_primes R F hL).2.1 t _ hc
  have hμ : ∀ w, Good R t w → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → ∀ k, (hk : k < D.R.m) →
      (R.C.mu0 ⟨k, hk⟩).UnrAt w ∧ (R.xiH t).UnrAt w := fun w hw hgw k hk => by
    refine ⟨(R.C.isMu0 _).unr w fun i hi => ?_, ?_⟩
    · have hi' : ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := hi
      refine hgw ?_
      rw [Nat.cast_mul]
      fin_cases i
      · exact Ideal.mul_mem_right _ _ hi'
      · exact Ideal.mul_mem_left _ _ hi'
    · by_contra h
      rcases (hL.Q_ram t w).1 h with h | ⟨PP, h, hc⟩
      · exact (hw w (Or.inr h)).1 rfl
      · exact (hw PP (Or.inr h)).2 hc
  refine ⟨unrPl_of_chrEq hL.eta (R.C.isEta.unr _) (R.C.isEta.unr _), fun j h1 h2 => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have a := unrPl_of_chrEq (hL.mu0 ⟨k, h2⟩) (hμ P hP hg k h2).1 (hμ _ hc hg'.1 k h2).1
  have b := unrPl_of_chrEq (hL.xi t) (hμ P hP hg k h2).2 (hμ _ hc hg'.1 k h2).2
  intro e f h x x1 x2 x3
  show R.mu0 (k + 1) x * R.xi t x = 1
  rw [a e f h x x1 x2 x3, b e f h x x1 x2 x3, one_mul]

end GlobalTheory.UnrOffLevels
