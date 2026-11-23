import Formalism.CoboundaryTransfers.GammaStableTransfers.MemCoboundariesOfIsOneCoboundary
import Formalism.CoboundaryTransfers.GammaStableTransfers.GammaStableOfGammaQUnitHolds

noncomputable section

namespace Formalism.CoboundaryTransfers

theorem liftsAt_mono : Mono := by
  intro O A _ _ _ B M M' D _ _ _ _ W hMM' hGQ
  refine ⟨{
    N := W.N
    φ := W.φ
    γ := W.γ
    φ_smul := W.φ_smul
    γ_smul := W.γ_smul
    comm := W.comm
    X_inj := W.X_inj
    Q_bij := W.Q_bij
    φ_N := fun x hx => by
      have h : B.Q ^ M' = B.Q ^ (M' - M) * B.Q ^ M := by
        rw [← pow_add, Nat.sub_add_cancel hMM']
      rw [h, mul_smul]
      exact W.N.smul_mem _ (W.φ_N x hx)
    γ_N := W.γ_N
    γ_QN := gammaStableOfGammaQUnit_holds O A B M' D W.N W.γ hGQ W.Q_bij W.γ_smul W.γ_N }, rfl, rfl, rfl⟩

theorem integral_wach_definitions : IntDefs := by
  intro O A _ _ _ B M D _ _ _ _ W
  have h1 : ∀ y, y ∈ W.QInvSub ↔ W.QInv y := by
    intro y
    simp only [WachMod.QInvSub, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply,
      WachMod.QInv]
  have h2 : ∀ z, z ∈ W.XNSub ↔ W.XN z := by
    intro z
    simp only [WachMod.XNSub, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply,
      WachMod.XN]
    constructor
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
  have h3 : ∀ y z, (y, z) ∈ W.ZInt ↔ W.Cocycle y z := by
    intro y z
    rw [WachMod.ZInt, Submodule.mem_inf, Submodule.mem_prod, Submodule.restrictScalars_mem,
      Submodule.restrictScalars_mem, h1, h2, W.mem_Z1_iff_cocycle]
    rfl
  have h4 : ∀ y z, (y, z) ∈ W.BInt ↔ W.IsCob1 y z := by
    intro y z
    have hf : ∀ x, ((W.φ - LinearMap.id).prod (W.γ - LinearMap.id)) x =
        (W.φ x - x, W.γ x - x) := fun _ => rfl
    rw [WachMod.BInt, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, hxe⟩
      rw [hf] at hxe
      obtain ⟨e1, e2⟩ := Prod.mk.inj hxe
      exact ⟨x, hx, e1.symm, e2.symm⟩
    · rintro ⟨x, hx, rfl, rfl⟩
      exact ⟨x, hx, hf x⟩
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_⟩
  · rintro ⟨y, z⟩ h
    exact (h3 y z).2 (W.cocycle_of_isCob1 ((h4 y z).1 h))
  · rintro ⟨y, z⟩ h
    exact W.mem_coboundaries_of_isOneCoboundary ((h4 y z).1 h)
  · rintro ⟨y, z⟩ h
    exact W.cocycle_mem_Zf ((h3 y z).1 h)

end Formalism.CoboundaryTransfers
