import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvSepW

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ}
  {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ}

def whittakerPairingValue (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (W : GL (Fin m) k → ℂ) (x : WT (m := m) ψ) : ℂ :=
  I fun g => (x : GL (Fin m) k → ℂ) g * W g

def pairW (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (W : GL (Fin m) k → ℂ) : WT (m := m) ψ →ₗ[ℂ] ℂ where
  toFun := whittakerPairingValue I W
  map_add' a b := by
    simp only [whittakerPairingValue]
    rw [← map_add]; congr 1; funext g
    simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' c a := by
    simp only [whittakerPairingValue, RingHom.id_apply]
    rw [← map_smul]; congr 1; funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring

include hψ in
theorem repr_delta (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K)
    {y : WT (m := m) ψ} (hy : ∀ κ ∈ K, rhoW ψ κ y = y) :
    I (fun g => (delta ψ K : GL (Fin m) k → ℂ) g * Wf ψ hψ I B y g) = B y (delta ψ K) := by
  have e : (fun g => (delta ψ K : GL (Fin m) k → ℂ) g * Wf ψ hψ I B y g) = lam ψ hψ I B y •
      fun g => (starRingEnd ℂ) ((delta ψ K : GL (Fin m) k → ℂ) g) * (delta ψ K : GL (Fin m) k → ℂ) g := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ
    · obtain ⟨u, hu, κ, hκ, rfl⟩ := h
      rw [delta_mul hK hu hκ, Wf_left hψ hI hB y hu, Wf_apply, hy κ hκ, conj_psi]
      ring
    · rw [delta_eq_zero h]
      ring
  rw [e, map_smul, smul_eq_mul, ← formI_apply, lam_eq hψ hI hB hK hy, lamK]
  exact div_mul_cancel₀ _ (cK_ne_zero hI hK)

include hψ in

theorem repr (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (y x : WT (m := m) ψ) :
    I (fun g => (x : GL (Fin m) k → ℂ) g * Wf ψ hψ I B y g) = B y x := by
  obtain ⟨K, hK, hKf⟩ := exists_good_fix hψ x y
  have hspan := mem_span_delta hK.1 hK.2.1 x (fun κ hκ => (hKf κ hκ).1)
  refine LinearMap.eqOn_span' (f := pairW I (Wf ψ hψ I B y)) (g := B y) ?_ hspan
  rintro _ ⟨g, hg, rfl⟩
  have hfix : ∀ κ ∈ K.map (MulAut.conj g).toMonoidHom, rhoW ψ κ (rhoW ψ g y) = rhoW ψ g y := by
    intro κ hκ
    have e : κ * g = g * (g⁻¹ * κ * g) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (hKf _ (mem_conj.1 hκ)).2]
  have hF := isTestFun_mul (delta ψ (K.map (MulAut.conj g).toMonoidHom)) (Wf ψ hψ I B (rhoW ψ g y))
    (fun u hu h => Wf_left hψ hI hB _ hu h) (isLocallyConstant_Wf hψ _)
  have h1 := hI.1 _ hF g⁻¹
  have h2 := repr_delta hψ hI hB hg hfix
  show whittakerPairingValue I (Wf ψ hψ I B y) _ = _
  simp only [whittakerPairingValue, rhoW_apply]
  rw [← hB.2.2 g y, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, ← h2,
    ← h1]
  congr 1
  funext h
  rw [Wf_right, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end DiscreteGroups.sglob.LConv

end
