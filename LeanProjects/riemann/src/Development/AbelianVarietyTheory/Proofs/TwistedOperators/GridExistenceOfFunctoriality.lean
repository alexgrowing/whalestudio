import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOverOfClauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyVertices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeOfMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAtOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyGridDataIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.RowEx.GridExPf

open Formalism.L2.Col GlobalTheory.GridPlaces

variable {D : D7}

theorem under_conjugatePrime_ne_of_class {p : ℕ} (hp : p.Prime) (hcl : D.host.cls p = .splitK) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : (p : 𝓞 D.host.E) ∈ P.asIdeal) : (conjPrime₂ P).under (𝓞 D.host.K) ≠ P.under (𝓞 D.host.K) := by
  intro h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h2, hd, hj⟩ : p ≠ 2 ∧ p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p = 1 := by
    obtain ⟨h1, -, h3, h4⟩ := (primeClass_eq_splitK_iff D.host.toHostRaw).1 hcl
    exact ⟨UpperTheory.Small.ne_two D.host h1, h3, h4⟩
  obtain ⟨s, hs⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨s, rfl⟩ := ZMod.intCast_surjective s
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ s * s + D.host.d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hs ⊢
    rw [← hs]; ring
  have hsq := D.host.sqrtMinusD_sq
  have hint : IsIntegral ℤ D.host.sqrtMinusD := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hsq]
    have := (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (D.host.d : ℤ))).neg
    simpa using this
  let b : 𝓞 D.host.K := ⟨⟨D.host.sqrtMinusD, IntermediateField.mem_adjoin_simple_self ℚ _⟩,
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.K D.host.E) Subtype.val_injective).1 hint⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) b := ⟨_, rfl⟩
  have hβ1 : (β : D.host.E) = D.host.sqrtMinusD := by rw [hβ]; rfl
  have hβ2 : β * β = -(D.host.d : 𝓞 D.host.E) := RingOfIntegers.ext (by simpa [hβ1, sq] using hsq)
  have hβ3 : cO D.host.E β = -β := RingOfIntegers.ext (by
    show star (β : D.host.E) = ((-β : 𝓞 D.host.E) : D.host.E)
    rw [bridge_star_holds D.R D.host, hβ1, D.host.conj_sqrtMinusD, ← hβ1]
    simp)
  have key : ∀ t : ℤ, (t : 𝓞 D.host.E) + β ∈ P.asIdeal ↔ (t : 𝓞 D.host.E) - β ∈ P.asIdeal := by
    intro t
    have h1 : (t : 𝓞 D.host.K) + b ∈ ((conjPrime₂ P).under (𝓞 D.host.K)).asIdeal ↔
        (t : 𝓞 D.host.K) + b ∈ (P.under (𝓞 D.host.K)).asIdeal := by rw [h]
    have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) = t + β := by
      rw [map_add, map_intCast, hβ]
    have h4 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) ∈ (conjPrime₂ P).asIdeal ↔
      algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) ∈ P.asIdeal := h1
    rw [h3, mem_conjP, map_add, map_intCast, hβ3, ← sub_eq_add_neg] at h4
    exact h4.symm
  have hprod : ((s : 𝓞 D.host.E) + β) * (s - β) ∈ P.asIdeal := by
    have e : ((s : 𝓞 D.host.E) + β) * (s - β) = (p : 𝓞 D.host.E) * m := by
      have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hm
      push_cast at this
      linear_combination this - hβ2
    rw [e]
    exact Ideal.mul_mem_right _ _ hP
  have ha : (s : 𝓞 D.host.E) + β ∈ P.asIdeal := (P.isPrime.mem_or_mem hprod).elim id (key s).2
  have hb := (key s).1 ha
  have h5 : (2 : 𝓞 D.host.E) * β ∈ P.asIdeal := by
    have := sub_mem ha hb
    rwa [show (s : 𝓞 D.host.E) + β - (s - β) = 2 * β by ring] at this
  rcases P.isPrime.mem_or_mem h5 with h6 | h6
  · exact h2 (prime_eq_of_mem P hp Nat.prime_two hP (by exact_mod_cast h6))
  · have h7 := neg_mem (Ideal.mul_mem_left _ β h6)
    rw [hβ2, neg_neg] at h7
    exact hd (prime_eq_of_mem P hp D.host.hyp.2.1 hP h7)

theorem exists_places_of_cls (T : Type) (L : LevCh D T) (μ0 : T) (hL : L.Is μ0)
    (hg : ∀ k, D.host.cls (D.host.g k) = .splitK) (hde : D.host.cls D.host.pde = .splitK)
    (hde' : D.host.cls D.host.pde' = .splitK) (hq : ∀ k, q0 D ≠ D.host.g k)
    (hQ : ∀ t, ∀ PP ∈ L.Q t, ((q0 D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) : ∃ P : Places L, P.v0 ∉ S1 D := by
  classical
  choose 𝔭 h𝔭 using exists_primes L hL
  obtain ⟨hq0, hq1, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  have hq2 : q0 D % LevelStarExponents.condE D = 1 := by
    have h1 : 1 < LevelStarExponents.condE D := by
      have := D.host.qd_big
      have hA : 0 < D.host.QS := D.host.QS_pos
      have hq' : 2 ≤ D.host.q := by omega
      have hd' : 1 ≤ D.host.d := by omega
      show 1 < D.host.QS * D.host.q * D.host.d
      calc 1 < 1 * 2 * 1 := by norm_num
        _ ≤ D.host.QS * D.host.q * D.host.d := Nat.mul_le_mul (Nat.mul_le_mul hA hq') hd'
    rw [← Nat.mod_mod_of_dvd _ (dvd_mul_left _ (Formalism.MainNotions.rPrAv D)), hq1, Nat.mod_eq_of_lt h1]
  have hq3 : D.host.cls (q0 D) = .splitK := GlobalTheory.Mem.cls_eq_splitK_of_cond D.host hq2
  obtain ⟨v0, hv0⟩ := exists_place D.host.F hq0
  have hw : ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ w : HeightOneSpectrum (𝓞 D.host.E), ∀ p : ℕ, p.Prime →
      (p : 𝓞 D.host.F) ∈ v.asIdeal → w.under (𝓞 D.host.F) = v ∧ w.under (𝓞 D.host.K) = 𝔭 p := by
    intro v
    by_cases h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal
    · obtain ⟨p, hp, hv⟩ := h
      obtain ⟨w, hw⟩ := exists_over_both hp v hv (𝔭 p) (h𝔭 p hp).1
      exact ⟨w, fun p' hp' hv' => prime_eq_of_mem v hp hp' hv hv' ▸ hw⟩
    · obtain ⟨w, -⟩ := exists_place D.host.E hq0
      exact ⟨w, fun p hp hv => absurd ⟨p, hp, hv⟩ h⟩
  choose w hw using hw
  have hS : ∀ v ∈ insert v0 (S1 D), ∃ p : ℕ, p.Prime ∧ D.host.cls p = .splitK ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal := by
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact ⟨_, hq0, hq3, hv0⟩
    · rcases (S1_mem_OmF D).1 hv with h | h | h | h
      · exact ⟨_, D.host.g_prime 0, hg 0, h⟩
      · exact ⟨_, D.host.g_prime 1, hg 1, h⟩
      · exact ⟨_, D.host.pde_prime, hde, h⟩
      · exact ⟨_, D.host.pde'_prime, hde', h⟩
  have hde2 : ∀ p : ℕ, p = D.host.pde ∨ p = D.host.pde' → p.Prime ∧ D.host.cls p = .splitK := by
    rintro p (rfl | rfl)
    · exact ⟨D.host.pde_prime, hde⟩
    · exact ⟨D.host.pde'_prime, hde'⟩
  refine ⟨⟨v0, hv0, w, fun v hv => ?_, fun v hv => ?_, fun v k hv => ?_, fun p hp => ⟨𝔭 p, fun v hv => ?_⟩,
    fun t P hP hS1 => ?_, fun t P hP h => ?_⟩, fun h => ?_⟩
  · obtain ⟨p, hp, -, h⟩ := hS v (by convert hv)
    exact (hw v p hp h).1
  · obtain ⟨p, hp, hc, h⟩ := hS v (by convert hv)
    refine GlobalTheory.MovedIdem.exists_isIdemAt (w v) fun e => under_conjugatePrime_ne_of_class hp hc (w v)
      ((natCast_mem_under (M := D.host.F) (w v) p).1 (by rw [(hw v p hp h).1]; exact h)) ?_
    rw [show conjPrime₂ (w v) = w v from HeightOneSpectrum.ext ((conjIdeal_asIdeal (w v)).symm.trans e)]
  · exact (hL.Pg _).2 ⟨k, (hw v _ (D.host.g_prime k) hv).2.trans ((h𝔭 _ (D.host.g_prime k)).2.1 k rfl)⟩
  · exact (hw v p (hde2 p hp).1 hv).2
  · obtain ⟨q, hq', hqP, hne⟩ := exists_prime_mem (hL.Q_pl t) hP
    have hqv := (natCast_mem_under (M := D.host.F) P q).2 hqP
    have h1 : q = D.host.pde ∨ q = D.host.pde' := by
      rcases (S1_mem_OmF D).1 hS1 with h | h | h | h
      · exact absurd (prime_eq_of_mem _ hq' (D.host.g_prime 0) hqv h) (hne 0)
      · exact absurd (prime_eq_of_mem _ hq' (D.host.g_prime 1) hqv h) (hne 1)
      · exact Or.inl (prime_eq_of_mem _ hq' D.host.pde_prime hqv h)
      · exact Or.inr (prime_eq_of_mem _ hq' D.host.pde'_prime hqv h)
    obtain ⟨h2, h3⟩ := hw _ q hq' hqv
    rcases eq_or_eq_conjP h2 with h | h
    · exact h.symm
    · exfalso
      apply under_conjugatePrime_ne_of_class hq' (hde2 q h1).2 P hqP
      rw [← h, h3, (h𝔭 q hq').2.2 h1 t P hP hqP]
  · exact hQ t P hP ((natCast_mem_under (M := D.host.F) P _).1 (h ▸ hv0))
  · rcases (S1_mem_OmF D).1 h with h | h | h | h
    · exact hq 0 (prime_eq_of_mem _ hq0 (D.host.g_prime 0) hv0 h)
    · exact hq 1 (prime_eq_of_mem _ hq0 (D.host.g_prime 1) hv0 h)
    · exact (leastSplitAuxiliaryPrime_ne_typePrimes D).1 (prime_eq_of_mem _ hq0 D.host.pde_prime hv0 h)
    · exact (leastSplitAuxiliaryPrime_ne_typePrimes D).2 (prime_eq_of_mem _ hq0 D.host.pde'_prime hv0 h)

theorem leastSplitAuxiliaryPrime_ne_typePrime_of_sizes {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (k : Fin 2) : q0 D ≠ D.host.g k := by
  intro e
  have h1 : Real.log (q0 D) ≤ large₂.sc.L := hs.2.2.2.2.2.2.2.2.1
  have h2 := (hs.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k k).1
  have hq : (0 : ℝ) < q0 D := by exact_mod_cast (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
  have h3 : (q0 D : ℝ) ≤ large₂.sc.b := (Real.log_le_iff_le_exp hq).1 h1
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hk : (2 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 2 ≤ D.R.k)
  have h4 : (D.R.k : ℝ) * large₂.sc.b ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := le_self_pow₀ (by nlinarith) (by norm_num)
  rw [← e] at h2
  nlinarith

end GlobalTheory.RowEx.GridExPf

namespace GlobalTheory.RowEx

open GlobalTheory.RowEx.GridExPf

theorem gridEx_of_hypotheses (hP : GlobalTheory.FunPr.Hypotheses₂) : GridEx := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS hQ => ?_⟩⟩
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hS.size
  have hcls : ∀ p ∈ D.host.levelPrimes, D.host.cls p = .splitK := Pm.level_split
  have hPl := exists_places_of_cls T R.toLevCh A.μ0 hS.core.lev (fun k => hcls _ (D.host.g_level k))
    (hcls _ D.host.pde_level.1) (hcls _ D.host.pde_level.2) (leastSplitAuxiliaryPrime_ne_typePrime_of_sizes hS.size) hQ
  obtain ⟨G⟩ := (GlobalTheory.ChiGridModel.nonempty_gridData_iff R.toLevCh A.μ0 hS.core.lev ⟨1, CF, large₂.sc.b⟩).2 hPl
  obtain ⟨W, hW⟩ := GlobalTheory.ChiGrid.WeilOver.exists_weil_over_of_clauses hP.weilRepresentationUnitaryPair R hS.core.lev
    hS.core.chain hS.core.models _ G
  haveI := hS.fin
  exact ⟨G, W, hW, GlobalTheory.FunObj.gridChoice_nonempty_of W hS.core.lev Set.finite_univ (GlobalTheory.RowClaim.Test.pde_ne_q hS)
    fun t _ P hP => GlobalTheory.RowClaim.Test.guard hS t P hP⟩

end GlobalTheory.RowEx

end
