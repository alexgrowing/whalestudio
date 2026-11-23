import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormCong

private theorem prime_dvd_int_of_cast_eq_mul {O : Type} [CommRing O] [IsDomain O] {ℓ : ℕ} (hℓ : ℓ.Prime) {q : O}
    (hq : Irreducible q) (hqℓ : q = (ℓ : O)) {m : ℤ} {c : O} (h : (m : O) = q * c) : (ℓ : ℤ) ∣ m := by
  by_contra hnd
  obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).2 hnd
  apply hq.not_isUnit
  have h1 : ((a * ℓ + b * m : ℤ) : O) = 1 := by rw [hab]; simp
  push_cast at h1
  rw [h, ← hqℓ] at h1
  exact isUnit_iff_exists_inv.2 ⟨a + b * c, by linear_combination h1⟩

theorem int_sq_dvd_of_eq {O : Type} [CommRing O] [IsDomain O] {ℓ : ℕ} (hℓ : ℓ.Prime) {q : O} (hq : Irreducible q)
    (hqℓ : q = (ℓ : O)) {n : ℤ} {c : O} (h : (n : O) = q ^ 2 * c) : (ℓ : ℤ) ^ 2 ∣ n := by
  obtain ⟨m, rfl⟩ := prime_dvd_int_of_cast_eq_mul hℓ hq hqℓ (c := q * c) (by rw [h]; ring)
  push_cast at h
  rw [← hqℓ] at h
  have h2 : ((m : ℤ) : O) = q * c := by
    apply mul_left_cancel₀ hq.ne_zero
    rw [h]; ring
  obtain ⟨k, rfl⟩ := prime_dvd_int_of_cast_eq_mul hℓ hq hqℓ h2
  exact ⟨k, by ring⟩

theorem exists_place_resChar (K : Type) [Field K] [NumberField K] {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Formalism.MainNotions.S.Loc.resChar p = ℓ := by
  haveI hmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hℓ).irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(ℓ : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 K)).injective_int]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) _ hker
  have hmem : ((ℓ : ℤ) : 𝓞 K) ∈ Q := by
    have h1 : (ℓ : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQc ▸ Ideal.mem_span_singleton_self _
    simpa using h1
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : ((ℓ : ℕ) : 𝓞 K) = 0 := by simpa using hmem
    exact hℓ.ne_zero (Nat.cast_eq_zero.mp h0)
  refine ⟨⟨Q, hQ.isPrime, hne⟩, ?_⟩
  haveI := hQ
  show ringChar (𝓞 K ⧸ Q) = ℓ
  have hz : ((ℓ : ℕ) : 𝓞 K ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
    simpa using hmem
  rcases (Nat.dvd_prime hℓ).1 ((ringChar.spec _ ℓ).1 hz) with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

theorem sq_dvd_at (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hN : ∀ p, (FP p).NormsOK) (i : Fin 2) :
    ((D.host.g i : ℕ) : ℤ) ^ 2 ∣ (Tn : ℤ) - T'n := by
  obtain ⟨p, hp⟩ := exists_place_resChar D.host.F (D.host.g_prime i)
  have hsome : ((D.s.atP p).split).isSome := by
    rw [D.s_split p, hp]
    fin_cases i <;> simp
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨-, -, -, -, -, hm⟩ := Z.agree p
  rcases hg : (Z.M p).split with _ | g
  · rw [hg, hsg] at hm
    exact (hm : False).elim
  rw [hg, hsg] at hm
  obtain ⟨-, hq⟩ := hm
  obtain ⟨-, -, -, -, hG⟩ := hN p
  obtain ⟨-, c, hc⟩ := hG g hg
  obtain ⟨-, -, hA, hB'⟩ := hB p
  refine int_sq_dvd_of_eq (D.host.g_prime i) g.q_irr ?_ (c := c) ?_
  · apply Subtype.ext
    rw [hq, sg.q_eq, hp]
    simp
  · apply Subtype.ext
    push_cast
    rw [← hA, ← hB']
    exact hc

end GlobalTheory.NormCong

open GlobalTheory.NormCong in
theorem GlobalTheory.NormCong.norms_congr : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).NormsOK) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] := by
  intro D Z FP u u' F F' hB hN
  have h0 := sq_dvd_at D Z FP (Tu D u) (Tu D u') F F' hB hN 0
  have h1 := sq_dvd_at D Z FP (Tu D u) (Tu D u') F F' hB hN 1
  have hcop : IsCoprime (((D.host.g 0 : ℕ) : ℤ) ^ 2) (((D.host.g 1 : ℕ) : ℤ) ^ 2) := by
    apply IsCoprime.pow
    exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  have h := dvd_sub_comm.1 (hcop.mul_dvd h0 h1)
  rw [Nat.modEq_iff_dvd, show gS D = D.host.g 0 * D.host.g 1 from rfl]
  push_cast
  rw [mul_pow]
  exact h
