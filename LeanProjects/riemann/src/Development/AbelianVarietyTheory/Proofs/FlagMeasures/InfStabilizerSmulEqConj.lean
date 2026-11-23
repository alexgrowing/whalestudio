import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerCommensurableInvVolumeSmulComplementStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem inf_stabilizer_smul_eq_conj {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G)
    {h : G} (hh : h ∈ H) (x : X) :
    H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) h1) hh, ?_⟩
    rw [mul_smul, mul_smul, h2, inv_smul_smul]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := H.mul_mem (H.mul_mem hh h1) (H.inv_mem hh)
      simpa [mul_assoc] using this
    · rw [mul_smul, mul_smul, inv_smul_eq_iff] at h2
      exact h2

theorem invVol_conj_of_invVol_conj {G : Type} [Group G] (K A B : Subgroup G) (g : G)
    (hA : K.relIndex A ≠ 0) (hA' : A.relIndex K ≠ 0) (hB : K.relIndex B ≠ 0) (hB' : B.relIndex K ≠ 0)
    (h : invVol K (MulAut.conj g • A) = invVol K A) :
    invVol K (MulAut.conj g • B) = invVol K B := by
  have e : ∀ A B : Subgroup G,
      (MulAut.conj g • A).relIndex (MulAut.conj g • B) = A.relIndex B := fun A B =>
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A B
      (MulAut.conj g).injective
  have hpos : 0 < invVol K (MulAut.conj g • A) := by
    rw [h]; exact (invVol_mul_pos_le_conj K A A hA hA' hA hA').2.1
  have hAB : A.relIndex B ≠ 0 := Subgroup.relIndex_ne_zero_trans hA' hB
  have hBA : B.relIndex A ≠ 0 := Subgroup.relIndex_ne_zero_trans hB' hA
  have c1 : K.relIndex (MulAut.conj g • A) ≠ 0 := by
    intro h0
    simp [invVol, h0] at hpos
  have c2 : (MulAut.conj g • A).relIndex K ≠ 0 := by
    intro h0
    simp [invVol, h0] at hpos
  have c3 : K.relIndex (MulAut.conj g • B) ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans c1 (by rw [e]; exact hAB)
  have c4 : (MulAut.conj g • B).relIndex K ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans (by rw [e]; exact hBA) c2
  rw [(invVol_mul_pos_le_conj K _ _ c1 c2 c3 c4).1, (invVol_mul_pos_le_conj K A B hA hA' hB hB').1, h]
  congr 1
  rw [invVol, invVol, e, e]

theorem Frames.nu_pos_and_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → 0 < S.nu d ∧ ∀ h ∈ S.H0, S.nu (h • d) = S.nu d := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  obtain ⟨hv, hd⟩ := GlobalTheory.T.stabilizer_commensurable_invVolume_smul_complement L r k S
  obtain ⟨d1, d2⟩ := hd d Λ hT
  have hSD := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).1
  obtain ⟨l1, l2, l3⟩ := hv Λ hSD.1
  refine ⟨(invVol_mul_pos_le_conj _ _ _ d1 d2 d1 d2).2.1, fun h hh => ?_⟩
  have := l3 h hh
  rw [inf_stabilizer_smul_eq_conj _ hh] at this
  unfold Frames.nu
  rw [inf_stabilizer_smul_eq_conj _ hh]
  exact invVol_conj_of_invVol_conj _ _ _ h l1 l2 d1 d2 this

end GlobalTheory.HL
