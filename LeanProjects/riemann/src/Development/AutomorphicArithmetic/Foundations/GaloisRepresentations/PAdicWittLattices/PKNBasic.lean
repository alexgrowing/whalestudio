import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletioStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp

open UpperTheory.Gal.G3

private theorem congOne_conj {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {G : GlobalTheory.LKTrip.HTGroup p}
    (L : GlobalTheory.LKGeo.Link D G) (N : ℕ) (g : G.GAf) (j j' : ℕ) (hj' : 0 < j')
    (hj : ∀ v ∈ GlobalTheory.LKGeo.LaHat D, j • L.actG g v ∈ GlobalTheory.LKGeo.LaHat D)
    (hi : ∀ v ∈ GlobalTheory.LKGeo.LaHat D, j' • L.actG g⁻¹ v ∈ GlobalTheory.LKGeo.LaHat D)
    (u : G.GAf) (hu : L.CongOne (N * (j * j')) u) : L.CongOne N (g * u * g⁻¹) := by
  intro v hv
  obtain ⟨w, hw, e⟩ := hu _ (hi v hv)
  refine ⟨j • L.actG g w, hj w hw, ?_⟩
  have h1 : L.actG g (L.actG g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have key : j' • L.actG (g * u * g⁻¹) v = j' • (v + N • j • L.actG g w) := by
    have e2 := congrArg (L.actG g) e
    simp only [map_add, map_nsmul, h1] at e2
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e2, smul_add, smul_smul, smul_smul]
    congr 2
    ring
  have hj0 : (j' : ℚ) ≠ 0 := by exact_mod_cast hj'.ne'
  rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ] at key
  exact smul_right_injective _ hj0 key

theorem UpperTheory.Gal.G3.pKNBasic :
    KNBasic := by
  intro p _ D G L N
  refine ⟨fun k hk u hu => ?_, fun g => ?_, fun M hN hM => GlobalTheory.W2.relIndex_KN_ne_zero L hN hM⟩
  · have key : ∀ u, L.CongOne N u → L.CongOne N (k * u * k⁻¹) := by
      intro u hu v hv
      obtain ⟨w, hw, e⟩ := hu _ (UpperTheory.Gal.Int.Geo.integ_of_mem (inv_mem hk) v hv)
      refine ⟨L.actG k w, UpperTheory.Gal.Int.Geo.integ_of_mem hk w hw, ?_⟩
      have h1 : L.actG k (L.actG k⁻¹ v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, map_add, map_nsmul, h1]
    refine ⟨key u hu.1, ?_⟩
    have e : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹ := by group
    rw [e]
    exact key _ hu.2
  · obtain ⟨j, hj0, hjp, hj⟩ := GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion p D (L.actG g)
    obtain ⟨j', hj0', hjp', hj'⟩ := GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion p D (L.actG g⁻¹)
    refine ⟨j * j', ?_, fun u hu => ⟨?_, ?_⟩⟩
    · exact Nat.Coprime.mul_left hjp hjp'
    · exact congOne_conj L N g j j' hj0' hj hj' u hu.1
    · have e : (g * u * g⁻¹)⁻¹ = g * u⁻¹ * g⁻¹ := by group
      rw [e]
      exact congOne_conj L N g j j' hj0' hj hj' _ hu.2
