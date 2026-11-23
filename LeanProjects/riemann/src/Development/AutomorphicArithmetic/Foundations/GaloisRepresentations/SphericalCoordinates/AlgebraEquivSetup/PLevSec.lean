import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pLevSec :
    UpperTheory.Gal.W2.Seed.IntConj → LevSec := by
  intro hIC E _ _ _ A n p _ S T S₀ Kw hS
  have hn : 0 < n := S.facts.pos
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 E)
  let w₀ : Plc E := ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
  have hsim : ∀ g : GUf E n, (∀ u, comp u g ∈ GlobalTheory.LFun.KGL u n) → sim g ∈ UpperTheory.Gal.CertificateRingHomMap.ZU :=
    fun g h => (hIC E n g w₀ hn).2.1 h
  have hcj : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → (p : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj w).asIdeal := by
    intro w hw
    have h1 : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
      simpa using hw
    rw [← GlobalTheory.LocInj.under_conjSrc w] at h1
    have h2 : algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj w).asIdeal := h1
    simpa using h2
  refine ⟨fun k hk => ?_, fun k h1 h2 _ => ?_⟩
  · obtain ⟨hs, hK, hR⟩ := UpperTheory.Gal.CertificateRingHomMap.mem_lev.1 hk
    have hoff : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w (T.sec (T.j k)) = comp w k :=
      (T.j_eq _ _).1 (T.j_sec _)
    have hover : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ GlobalTheory.LFun.KGL w n := fun w hw =>
      hR w (fun h => hS w h hw) (fun h => hS _ h (hcj w hw))
    have hq : sim ((T.sec (T.j k))⁻¹ * k) ∈ UpperTheory.Gal.CertificateRingHomMap.ZU := by
      refine hsim _ fun u => ?_
      rw [map_mul, map_inv]
      by_cases hu : (p : 𝓞 E) ∈ u.asIdeal
      · rw [T.sec_p _ u hu, inv_one, one_mul]
        exact hover u hu
      · rw [hoff u hu, inv_mul_cancel]
        exact one_mem _
    refine UpperTheory.Gal.CertificateRingHomMap.mem_lev.2 ⟨?_, fun w hw => ?_, fun w hw hcw => ?_⟩
    · have e : sim (T.sec (T.j k)) = sim k * (sim ((T.sec (T.j k))⁻¹ * k))⁻¹ := by
        rw [map_mul, map_inv]; simp
      rw [e]
      exact mul_mem hs (inv_mem hq)
    · rw [hoff w (hS w hw)]
      exact hK w hw
    · by_cases hu : (p : 𝓞 E) ∈ w.asIdeal
      · rw [T.sec_p _ w hu]
        exact one_mem _
      · rw [hoff w hu]
        exact hR w hw hcw
  · have hall : ∀ u, comp u k ∈ GlobalTheory.LFun.KGL u n := fun u => by
      by_cases hu : (p : 𝓞 E) ∈ u.asIdeal
      · exact h2 u hu
      · rw [h1 u hu]; exact one_mem _
    refine UpperTheory.Gal.CertificateRingHomMap.mem_lev.2 ⟨hsim k hall, fun w hw => ?_, fun w _ _ => hall w⟩
    rw [h1 w (hS w hw)]
    exact one_mem _
