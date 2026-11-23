import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RFSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatSt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatChi
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.OBLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.ComplOddPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrI
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.UrepOf

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

theorem s6 : S6 := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ rF hl hc hr hk
  letI : Algebra Bh (FractionRing x.A) := rF.toAlgebra
  have hk' : RingHom.ker (algebraMap Bh (FractionRing x.A)) = maximalIdeal Bh := hk
  obtain ⟨H⟩ := hat_ex P (Bh := Bh) hr
  have hs := rF_surj P (Bh := Bh) hr hk'
  haveI := hc.noeth
  haveI := hc.complete
  haveI := H.fin
  have h2 : IsUnit (2 : Bh) := by
    by_contra hn
    have h3 : (2 : Bh) ∈ RingHom.ker (algebraMap Bh (FractionRing x.A)) := by rw [hk']; exact hn
    rw [RingHom.mem_ker, map_ofNat] at h3
    have h4 : (2 : x.K) = 0 := by
      have h5 : (algebraMap x.A (FractionRing x.A)).comp (PowerSeries.C (R := x.K)) 2 = 0 := by rw [map_ofNat]; exact h3
      exact (map_eq_zero _).1 h5
    have h6 : IsUnit (2 : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => hl ?_)
      have h7 : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by simpa using hlt
      rw [PadicInt.norm_int_lt_one_iff_dvd] at h7
      exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 (by exact_mod_cast h7)
    have h8 := h6.map (algebraMap ℤ_[l] x.K)
    rw [map_ofNat, h4] at h8
    exact not_isUnit_zero h8
  have hst := hat_st P hr H
  have hrg := hat_range P hs H
  obtain ⟨U, hx, hrk⟩ := idem x.a H.DE H.T H.r x.a_pos x.a_le h2 H.ch H.tr hk' (hat_chi P hr H) hst
    fun Z hZ => (hrg Z).1 hZ
  have hg : Nonempty (GrAlg H.T n x.a H.r U.ep) := by
    rcases x.a_le.lt_or_eq with ha | ha
    · exact gr_E x.a H.T H.r U x.a_pos ha hk' hst hx fun y => (hrg _).2 ⟨y, rfl⟩
    · have hn : 1 ≤ n := ha ▸ x.a_pos
      revert U
      rw [ha]
      intro U hx _
      exact gr_I H.T H.r U hn hst hx
  obtain ⟨g⟩ := hg
  exact urep_of H g U.coi hrk

end UpperTheory.V.Pa
