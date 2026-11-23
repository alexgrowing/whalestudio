import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerCommensurableUnramifiedHermitiaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometriesFixingSubspaceLeQuasiReflectionClosureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeConjModularCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuasiReflectionStabilizesLatticeStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Unimod

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_swap (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHerm L Hm)
    (x y : Fin n → E) : hf L Hm x y = L.cj (hf L Hm y x) := by
  have h : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun hH i) j
  simp only [hf, map_sum, map_mul, L.cj_cj, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem qrefl_mem (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHerm L Hm)
    (Y : Submodule E (Fin n → E)) {a : Fin n → E} (ha : a ∈ perp L Hm Y)
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : IsQRefl L Hm a g) : g ∈ fixG L Hm Y := by
  obtain ⟨_, hi, c, hc⟩ := hg
  have hfix : ∀ v ∈ Y, g v = v := fun v hv => by
    have h0 : hf L Hm a v = 0 := ha v hv
    rw [hc, hf_swap L hH v a, h0]; simp
  refine ⟨hi, fun v => ⟨fun hv => ?_, fun hv => by rw [hfix v hv]; exact hv⟩, fun v hv => ?_⟩
  · have : g v = v := g.injective (hfix _ hv)
    rwa [this] at hv
  · rw [hfix v hv]; simp

theorem conj_self {G : Type} [Group G] {H : Subgroup G} {h : G} (hh : h ∈ H) :
    MulAut.conj h • H = H := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply]
  constructor
  · intro hy
    have := H.mul_mem (H.mul_mem hh hy) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hy
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hy) hh

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem inf_stab_smul (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) {h} (hh : h ∈ H) :
    H ⊓ stabL L (h • Λ) = MulAut.conj h • (H ⊓ stabL L Λ) := by
  rw [((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ hΛ hΛ H).2 h).2, Subgroup.smul_inf, conj_self hh]

theorem comm_conj (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) : ∀ h ∈ H,
    (H ⊓ stabL L Λ).relIndex (MulAut.conj h • (H ⊓ stabL L Λ)) ≠ 0 ∧
      (MulAut.conj h • (H ⊓ stabL L Λ)).relIndex (H ⊓ stabL L Λ) ≠ 0 := by
  intro h hh
  have hl := ((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ hΛ hΛ H).2 h).1
  rw [← inf_stab_smul L H hΛ hh]
  exact ⟨(GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hl hΛ H).1, (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hΛ hl H).1⟩

theorem invVol_self {G : Type} [Group G] (K : Subgroup G) : invVol K K = 1 := by
  simp [invVol]

theorem delta_inv (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) {g} (hg : g ∈ H) :
    invVol (H ⊓ stabL L Λ) (MulAut.conj g • (H ⊓ stabL L Λ)) *
      invVol (H ⊓ stabL L Λ) (MulAut.conj g⁻¹ • (H ⊓ stabL L Λ)) = 1 := by
  rw [← (GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H hΛ)).1 g hg g⁻¹ (H.inv_mem hg)]
  simp [invVol_self]

theorem delta_indep (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ0 Λ : Submodule L.O (Fin n → E)} (h0 : IsLat L Λ0) (hΛ : IsLat L Λ) {g} (hg : g ∈ H)
    (h1 : invVol (H ⊓ stabL L Λ) (MulAut.conj g • (H ⊓ stabL L Λ)) = 1) :
    invVol (H ⊓ stabL L Λ0) (MulAut.conj g • (H ⊓ stabL L Λ0)) = 1 := by
  have a := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hΛ h0 H).1
  have b := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ h0 hΛ H).1
  have hl := ((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ hΛ hΛ H).2 g).1
  have c := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hl h0 H).1
  have d := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ h0 hl H).1
  rw [inf_stab_smul L H hΛ hg] at c d
  have e1 := ((GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H h0)).2.2.2 _ a b g hg).1
  have e2 := (GlobalTheory.HL.invVol_mul_pos_le_conj _ _ _ a b c d).1
  have e3 := (GlobalTheory.HL.invVol_mul_pos_le_conj _ _ _ a b a b).2.1
  rw [e1, h1, mul_one] at e2
  exact mul_right_cancel₀ e3.ne' (by rw [e2, one_mul])

theorem unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ Λ0 Λ : Submodule L.O (Fin n → E), IsLat L Λ0 → IsLat L Λ → ∀ h ∈ fixG L Hm (Submodule.span E (Set.range x)), invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L (h • Λ)) = invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ) := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH m x hx Λ0 Λ h0 hΛ h hh
  have hgen := GlobalTheory.T.isometriesFixingSubspace_le_quasiReflection_closure L Hm hH m x hx
  have hq := GlobalTheory.T.exists_lattice_and_inverting_automorphism_of_quasi_reflection L Hm hH m x hx
  have hmem := fun a ha g hg => qrefl_mem L hH.1 (Submodule.span E (Set.range x)) (a := a) ha (g := g) hg
  set H := fixG L Hm (Submodule.span E (Set.range x)) with hHdef
  have key : ∀ g ∈ Subgroup.closure
      {g | ∃ a ∈ perp L Hm (Submodule.span E (Set.range x)), IsQRefl L Hm a g},
      g ∈ H ∧ invVol (H ⊓ stabL L Λ0) (MulAut.conj g • (H ⊓ stabL L Λ0)) = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, hg⟩ := hg
      have hgH := hmem a ha g hg
      refine ⟨hgH, ?_⟩
      obtain ⟨Λ1, h1, α, hα, hαg⟩ := hq a ha g hg
      refine delta_indep L H h0 h1 hgH ?_
      have M := GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H h1)
      have e1 := M.2.2.1 α hα g hgH
      have e2 := M.2.1 g hgH
      have e3 := delta_inv L H h1 hgH
      rw [hαg] at e1
      rw [e1] at e3
      nlinarith
    | one => exact ⟨H.one_mem, by simp [invVol_self]⟩
    | mul a b _ _ ha hb =>
      refine ⟨H.mul_mem ha.1 hb.1, ?_⟩
      rw [(GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H h0)).1 a ha.1 b hb.1, ha.2, hb.2, one_mul]
    | inv a _ ha =>
      refine ⟨H.inv_mem ha.1, ?_⟩
      have := delta_inv L H h0 ha.1
      rwa [ha.2, one_mul] at this
  have a := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hΛ h0 H).1
  have b := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ h0 hΛ H).1
  rw [inf_stab_smul L H hΛ hh,
    ((GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H h0)).2.2.2 _ a b h hh).1, (key h (hgen hh)).2, one_mul]

end GlobalTheory.HL.Unimod
