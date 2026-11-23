import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical

noncomputable section

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped TensorProduct

namespace GlobalTheory.NormSum.IntOver

section Ad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem eps_mul_mem (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) (hm : (m : 𝓞 F) ∉ v.asIdeal) (x : 𝒜)
    (hx : (m : 𝒜) * x ∈ 𝒮) : afsplitEps E v * x ∈ 𝒮 := by
  have hval : Valued.v (m : v.adicCompletion F) = 1 := by
    rw [RepAt.val_nat]
    exact le_antisymm (v.valuation_le_one _) (not_lt.1 fun h' => hm ((v.valuation_lt_one_iff_mem _).1 h'))
  have hm0 : (m : v.adicCompletion F) ≠ 0 := fun h => by rw [h, map_zero] at hval; exact zero_ne_one hval
  have ha : (m : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  set u : 𝒮 := RepAt.incInt ⟨afsplitI v (m : v.adicCompletion F)⁻¹, afsplitI_mem_intAd v _ ha⟩ with hu
  have e1 : afsplitI v (m : v.adicCompletion F)⁻¹ * (m : 𝔸) = afsplitI v 1 := by
    rw [← map_natCast (algebraMap F 𝔸) m]
    ext w
    rw [afsplit_mul_apply]
    congr 1
    change afsplitI v (m : v.adicCompletion F)⁻¹ w * algebraMap F (w.adicCompletion F) (m : F) = afsplitI v 1 w
    by_cases h : w = v
    · subst h
      rw [afsplitI_self, afsplitI_self, map_natCast]
      exact inv_mul_cancel₀ hm0
    · rw [afsplitI_ne v w h, afsplitI_ne v w h, zero_mul]
  have e2 : (u : 𝒜) * (m : 𝒜) = afsplitEps E v := by
    rw [hu]
    change (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜) (afsplitI v (m : v.adicCompletion F)⁻¹) * (m : 𝒜) = _
    rw [← map_natCast (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜) m, ← map_mul, e1, afsplitEps,
      Algebra.TensorProduct.one_def, afsplitIE_tmul]
    rfl
  rw [← e2, mul_assoc]
  exact mul_mem u.2 hx

end Ad

end GlobalTheory.NormSum.IntOver

open GlobalTheory.NormSum.IntOver GlobalTheory.NormSum.RepAt GlobalTheory.NormSum.PtsMem in

theorem GlobalTheory.NormSum.exists_prime_integralOver :
    ∀ (D : Formalism.BasicNotions.D7) (N : ℕ) (h : ↥(Formalism.MainNotions.StandardLatticesGL3.GA D N)), ∃ p : ℕ, p.Prime ∧ GlobalTheory.NormSum.IntegralOver D p h := by
  intro D N h
  set g : Matrix (Fin N) (Fin N) (AE D) := ((h : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) with hg
  choose m hm0 hm using fun ij : Fin N × Fin N => denom (F := ℚ) (E := D.host.E) (g ij.1 ij.2)
  set M := ∏ ij, m ij with hMdef
  have hM0 : 0 < M := Finset.prod_pos fun ij _ => hm0 ij
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 1)
  have hpM' : ¬ p ∣ M := fun hd => by have := Nat.le_of_dvd hM0 hd; omega
  obtain ⟨v, hv, hw⟩ := exists_place p hp
  have hMv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro hm'
    obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM'))).map
      (Int.castRingHom (𝓞 ℚ))
    refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e]
    exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hm')) (Ideal.mul_mem_left _ _ (by simpa using hv))
  have hi : ∀ i j, afsplitEps D.host.E v * g i j ∈ OhE D := fun i j => eps_mul_mem v M hMv _ (by
    rw [hMdef, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_assoc]
    exact mul_mem (natCast_mem _ _) (hm (i, j)))
  obtain ⟨k, hk, hint, htriv⟩ := exists_int (F := ℚ) (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) v
    (h : GL (Fin N) (AE D)) h.2 (Units.inv_eq_of_mul_eq_one_left ((mem_GA D _).1 h.2)) hi
  refine ⟨p, hp, ⟨k, hk⟩, (mem_intG _).2 hint, fun i j l => ?_⟩
  have := zero_at (F := ℚ) (E := D.host.E) v p hp hw (g i j - (1 : Matrix (Fin N) (Fin N) (AE D)) i j) l
  rw [← htriv i j] at this
  exact this
