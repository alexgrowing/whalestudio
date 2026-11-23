import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.DifferentLatIndex
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PTorusIndex
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.DiffLatStep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

theorem genIndex_eq_of_le {G : Type*} [AddCommGroup G] {W P Q : AddSubgroup G} (hWP : W ≤ P) (hWQ : W ≤ Q)
    (hQ : W.relIndex Q ≠ 0) : genIndex P Q = (W.relIndex P : ℝ) / (W.relIndex Q) := by
  have h1 := AddSubgroup.relIndex_mul_relIndex W (P ⊓ Q) P (le_inf hWP hWQ) inf_le_left
  have h2 := AddSubgroup.relIndex_mul_relIndex W (P ⊓ Q) Q (le_inf hWP hWQ) inf_le_right
  rw [AddSubgroup.inf_relIndex_left] at h1
  rw [AddSubgroup.inf_relIndex_right] at h2
  have ht : W.relIndex (P ⊓ Q) ≠ 0 := fun h => hQ (by rw [← h2, h, zero_mul])
  rw [genIndex, ← h1, ← h2, Nat.cast_mul, Nat.cast_mul, mul_div_mul_left]
  exact_mod_cast ht

theorem DifferentLatIndex.proof : DifferentLatIndex.Statement := by
  intro Em _ _ K _ _ N I ρ v hv s
  let _ : Algebra Em K := s.toAlgebra
  have hIfg : I.FG := fg_of_isNzFamily hv
  obtain ⟨_, hvI, hli, hm⟩ := hv
  set J0 := Submodule.span (𝓞 Em) (Set.range v) with hJ0
  set m := familyIndex I v with hmdef
  have hm' : J0.toAddSubgroup.relIndex I.toAddSubgroup = m := rfl
  rw [hm'] at hm
  set e := Module.finrank Em K with he
  have hdeg : Module.finrank ℚ K = Module.finrank ℚ Em * e := (Module.finrank_mul_finrank ℚ Em K).symm
  have hnE : Module.finrank ℚ Em ≠ 0 := Module.finrank_pos.ne'

  have hE : LinearIndependent Em v := (LinearIndependent.iff_fractionRing (𝓞 Em) Em).1 hli
  have hmE : (m : Em) ≠ 0 := by exact_mod_cast hm
  let w : Fin ρ → Fin N → Em := fun a => (m : Em)⁻¹ • v a
  have hw : LinearIndependent Em w :=
    hE.units_smul (fun _ => Units.mk0 ((m : Em)⁻¹) (inv_ne_zero hmE))
  have hvK : LinearIndependent K (fun a i => s (v a i)) :=
    (linearIndependent_algebraMap_comp_iff (R := Em) (S := K)).2 hE
  have hwK : LinearIndependent K (fun a i => s (w a i)) :=
    (linearIndependent_algebraMap_comp_iff (R := Em) (S := K)).2 hw

  have hvw : v = fun a => (m : 𝓞 Em) • w a := by
    funext a i
    simp [w, Algebra.smul_def, hmE]
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm
  have hsvw : (fun a i => s (v a i)) = fun a => (m : 𝓞 K) • fun i => s (w a i) := by
    funext a i
    simp [w, Algebra.smul_def, hmK]
  set B := Submodule.span (𝓞 Em) (Set.range w) with hB
  have hJ0_eq : J0 = idealLat w (Ideal.span {(m : 𝓞 Em)}) := by
    rw [hJ0, ← idealLat_top, hvw, idealLat_smul, Ideal.mul_top]
  have hB_eq : B = idealLat w ⊤ := (idealLat_top w).symm
  have hXJ0 : diffLat s J0 = idealLat (fun a i => s (v a i)) (extDifferent s) := diffLat_span s v
  have hXJ0' : diffLat s J0 = idealLat (fun a i => s (w a i)) (Ideal.span {(m : 𝓞 K)} * extDifferent s) := by
    rw [hXJ0, hsvw, idealLat_smul]
  have hXB : diffLat s B = idealLat (fun a i => s (w a i)) (extDifferent s) := diffLat_span s w
  have hF : familyLat s v = idealLat (fun a i => s (v a i)) ⊤ := (idealLat_top _).symm

  have hD : Ideal.absNorm (extDifferent s) = (discr Em).natAbs ^ e := absNorm_extDifferent s
  have hDne : Ideal.absNorm (extDifferent s) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact extDifferent_ne_bot s
  have iF : (diffLat s J0).toAddSubgroup.relIndex (familyLat s v).toAddSubgroup =
      Ideal.absNorm (extDifferent s) ^ ρ := by
    have h := idealLat_relIndex hvK (le_top : extDifferent s ≤ ⊤)
    rw [Ideal.absNorm_top, one_pow, mul_one] at h
    rw [hXJ0, hF, h]
  have iB : J0.toAddSubgroup.relIndex B.toAddSubgroup = (m ^ Module.finrank ℚ Em) ^ ρ := by
    have h := idealLat_relIndex hw (le_top : Ideal.span {(m : 𝓞 Em)} ≤ ⊤)
    rw [Ideal.absNorm_top, one_pow, mul_one, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h
    rw [hJ0_eq, hB_eq, h]
  have iXB : (diffLat s J0).toAddSubgroup.relIndex (diffLat s B).toAddSubgroup =
      (m ^ Module.finrank ℚ K) ^ ρ := by
    have h := idealLat_relIndex hwK (Ideal.mul_le_right : Ideal.span {(m : 𝓞 K)} * extDifferent s ≤ extDifferent s)
    rw [map_mul, mul_pow, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h
    rw [hXJ0', hXB]
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_ne_zero hDne) ρ) h

  have hJ0I : J0 ≤ I := Submodule.span_le.2 (Set.range_subset_iff.2 hvI)
  have hIB : I ≤ B := by
    intro u hu
    have hmu : m • u ∈ J0 := by
      have h := AddSubgroup.nsmul_index_mem (J0.toAddSubgroup.addSubgroupOf I.toAddSubgroup) ⟨u, hu⟩
      rw [AddSubgroup.mem_addSubgroupOf] at h
      exact h
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 Em)).1 hmu
    refine (Submodule.mem_span_range_iff_exists_fun (𝓞 Em)).2 ⟨c, ?_⟩
    have : ∑ a, c a • w a = (m : Em)⁻¹ • ∑ a, c a • v a := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [w]
      rw [smul_comm]
    rw [this, hc, ← Nat.cast_smul_eq_nsmul Em, inv_smul_smul₀ hmE]
  have hBfg : B.FG := Submodule.fg_span (Set.finite_range w)

  have hmulB := AddSubgroup.relIndex_mul_relIndex J0.toAddSubgroup I.toAddSubgroup B.toAddSubgroup hJ0I hIB
  have hmulX := AddSubgroup.relIndex_mul_relIndex (diffLat s J0).toAddSubgroup (diffLat s I).toAddSubgroup
    (diffLat s B).toAddSubgroup (diffLat_mono s hJ0I) (diffLat_mono s hIB)
  have hIBne : I.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
    intro h
    rw [h, mul_zero, iB] at hmulB
    exact pow_ne_zero _ (pow_ne_zero _ hm) hmulB.symm
  have hX1 := diffLat_relIndex_le s hJ0I hIfg (by rw [hm']; exact hm)
  have hX2 := diffLat_relIndex_le s hIB hBfg hIBne
  change _ ≤ _ ^ e at hX1 hX2
  have hprod : (diffLat s J0).toAddSubgroup.relIndex (diffLat s I).toAddSubgroup *
      (diffLat s I).toAddSubgroup.relIndex (diffLat s B).toAddSubgroup =
      (J0.toAddSubgroup.relIndex I.toAddSubgroup) ^ e * (I.toAddSubgroup.relIndex B.toAddSubgroup) ^ e := by
    rw [hmulX, iXB, ← mul_pow, hmulB, iB, hdeg, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hBpos : 0 < (I.toAddSubgroup.relIndex B.toAddSubgroup) ^ e := pow_pos (Nat.pos_of_ne_zero hIBne) e
  have iXI : (diffLat s J0).toAddSubgroup.relIndex (diffLat s I).toAddSubgroup = m ^ e := by
    rw [← hm']
    rcases lt_or_eq_of_le hX1 with hlt | heq
    · exact absurd hprod (ne_of_lt (Nat.mul_lt_mul_of_lt_of_le hlt hX2 hBpos))
    · exact heq

  have hWQ : diffLat s J0 ≤ familyLat s v := by
    rw [hXJ0, hF]
    exact Submodule.map_mono (fun c _ => Submodule.mem_pi.2 fun i _ => Submodule.mem_top)
  rw [genIndex_eq_of_le (diffLat_mono s hJ0I) hWQ (by rw [iF]; exact pow_ne_zero _ hDne), iXI, iF, hD]
  have hexp : (Module.finrank ℚ K : ℝ) / Module.finrank ℚ Em = (e : ℝ) := by
    rw [hdeg, Nat.cast_mul]
    field_simp
  rw [hexp, Real.rpow_natCast, div_pow]
  have habs : ((discr Em).natAbs : ℝ) = |(discr Em : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  push_cast
  rw [habs]
  ring

end GroundTheory.Heights₂.Heights.NineStatements
