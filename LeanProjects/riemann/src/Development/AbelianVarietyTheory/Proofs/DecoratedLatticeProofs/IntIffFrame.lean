import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompIncAAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAtTypeAndOrd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAMulMemIntAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemUnderSq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointHeckeComponentTameAndResidualStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LevelData

open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge GlobalTheory.LocMod
open Formalism.L2.Col (IntAt redP qOf)

section Gen

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def reFrame {N n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (M : Matrix (Fin N) (Fin n) k) (M' : Matrix (Fin n) (Fin N) k)
    (h : M * M' = 1) (h' : M' * M = 1) (e : Y ≃ Fin n) : Frame k N Y :=
  ⟨M.submatrix id e, M'.submatrix e id, by rw [submatrix_mul_equiv, h, submatrix_id_id],
    by rw [← Equiv.coe_refl, submatrix_mul_equiv, h', submatrix_one_equiv]⟩

variable {u : D.what₂.Word}

end Gen

section Chain

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_iff {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}
    (hi : ∀ x, ι x ∈ 𝒪[k] ↔ IntAt P x) (a : E) : valuation k (ι a) < 1 ↔ P.valuation E a < 1 := by
  by_cases ha : a = 0
  · simp [ha]
  have h := hi a⁻¹
  rw [GlobalTheory.AtTypeExists.intAt_iff, Valuation.mem_integer_iff, map_inv₀, map_inv₀, map_inv₀,
    inv_le_one₀ (zero_lt_iff.2 (by simpa using ha)), inv_le_one₀ (zero_lt_iff.2 (by simpa using ha))] at h
  rw [← not_le, ← not_le, h]

theorem exists_unif {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}
    (hi : ∀ x, ι x ∈ 𝒪[k] ↔ IntAt P x) (hd : DenseRange ι) (h : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    ∃ ϖ : kˣ, (ϖ : k) = ι (qOf P : E) ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ := by
  have hq := GlobalTheory.AtTypeExists.valuation_norm P h
  have h0 : ((qOf P : ℕ) : E) ≠ 0 := fun e => by
    rw [e, map_zero] at hq
    exact WithZero.exp_ne_zero hq.symm
  have h1 : valuation k (ι (qOf P : E)) < 1 := by
    rw [val_lt_one_iff hi, hq, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  refine ⟨Units.mk0 _ ((map_ne_zero ι).2 h0), rfl, fun x => ⟨fun hx => ?_, fun hx => lt_of_le_of_lt hx h1⟩⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  have h2 : {y : k | valuation k (y - x) < valuation k x} ∈ nhds x := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨Units.mk0 (valuation k x) (by simpa using hx0), by simp⟩
  obtain ⟨a, ha⟩ := hd.mem_nhds h2
  have h3 : valuation k (ι a) = valuation k x := by simpa using Valuation.map_add_eq_of_lt_right (valuation k) ha
  have h4 : P.valuation E a < 1 := (val_lt_one_iff hi a).1 (h3 ▸ hx)
  have h5 : IntAt P (a / (qOf P : E)) := by
    rw [GlobalTheory.AtTypeExists.intAt_iff, map_div₀, hq, div_le_one₀ WithZero.exp_pos]
    by_cases ha0 : P.valuation E a = 0
    · simp [ha0]
    · rw [← WithZero.exp_log ha0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h4
      rw [← WithZero.exp_log ha0, WithZero.exp_le_exp]
      omega
  have h6 := (hi _).2 h5
  rw [Valuation.mem_integer_iff, map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 ((map_ne_zero ι).2 h0))), h3] at h6
  exact h6

theorem mul_sec (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (y : k) : x * q.sec y = q.sec (q.pr x * y) := by
  have h := q.sec_pr (x * q.sec y)
  have h' := q.sec_pr (q.sec y)
  rw [map_mul, q.pr_sec] at h
  rw [q.pr_sec] at h'
  rw [h, mul_left_comm, ← h']

end Chain

section Place

end Place

section World

variable {B : Base} {X : PreX B.toPre}

theorem type_prime {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ (B.primes X).vGs) :
    ∃ i, qOf P = B.host.g i ∧ (B.host.g i).Prime ∧ ((B.host.g i : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal ∧
      ((B.host.g i : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal ^ 2 ∧ B.host.g i ∉ B.host.small ∧ B.host.g i ≠ B.host.q ∧ B.host.g i ≠ B.host.d ∧
      B.fields.conjO (X.piG i) ∈ P.asIdeal ∧ X.piG i ∉ P.asIdeal ∧ ∀ v, X.piT v - 1 ∈ P.asIdeal := by
  classical
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨i, hi⟩ : ∃ i, P ∈ (B.primes X).vG i := by
    unfold Formalism.L2.Col.Primes.vGs at hP
    rcases Finset.mem_union.1 hP with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  obtain ⟨h1, h2⟩ := GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi
  have hp : (B.host.g i).Prime := hPr.g_prime i
  have key : ¬ B.host.g i ∣ B.host.QS * B.host.q * B.host.d := fun h => by
    have h3 : B.host.g i ≡ 1 [MOD B.host.g i] := (hPr.g_cong i).of_dvd h
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.modEq_zero_iff_dvd).1 (h3.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))))
  have hc : B.fields.conjO (X.piG i) ∈ P.asIdeal := by
    unfold Formalism.L2.Col.Primes.vG Formalism.L2.Col.divs at hi
    split_ifs at hi with h
    · exact h.mem_toFinset.1 hi
    · simp at hi
  refine ⟨i, hPr.vG_norm i P hi, hp, h1, h2, B.host.toHostRaw.notMem_small_of_not_dvd key,
    B.host.toHostRaw.ne_q_of_not_dvd key, B.host.toHostRaw.ne_d_of_not_dvd key, hc, fun h => ?_, fun v => ?_⟩
  · obtain ⟨x, y, e⟩ := hPr.piG_cop i
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hc)))
  · refine Ideal.mem_of_dvd _ (dvd_trans ?_ (hPr.piT_cong v)) h1
    refine Nat.cast_dvd_cast (Dvd.dvd.mul_left (Dvd.dvd.pow ?_ two_ne_zero) _)
    fin_cases i
    exacts [dvd_mul_right _ _, dvd_mul_left _ _]

end World

end GlobalTheory.SeeSaw.LevelData

end
