import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IotaEx

namespace UpperTheory.V.Z.Sym.Glob

open Matrix Loc

private theorem base_bot {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (ι : Γ →* G) (U : Subgroup G)
    (W : Representation ℂ Γ V) : ∃ B : Base Γ G V, B.ι = ι ∧ B.U = U ∧ B.ω = 1 ∧ B.Γ₀ = ⊥ ∧ B.W = W := by
  refine ⟨⟨ι, U, 1, W, ⊥, bot_le, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl⟩
  · intro z hz
    rw [Subgroup.mem_bot.1 hz, map_one]
    exact one_mem _
  · intro z hz
    rw [Subgroup.mem_bot.1 hz, map_one]
    exact one_mem _
  · intro z hz v
    obtain rfl := Subgroup.mem_bot.1 hz
    simp

private theorem base_sub {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (ι : Γ →* G) (S : Subgroup Γ)
    (T U : Subgroup G) (h : ∀ γ ∈ S, ι γ ∈ T) (x : G) (W : Representation ℂ S V) :
    ∃ B : Base S T V, (∀ γ : S, (B.ι γ : G) = ι γ) ∧ (∀ g : T, g ∈ B.U ↔ x⁻¹ * g * x ∈ U) ∧ B.ω = 1 ∧ B.Γ₀ = ⊥ ∧ B.W = W := by
  obtain ⟨B, h1, h2, h3⟩ := base_bot ((ι.comp S.subtype).codRestrict T fun γ => h γ γ.2)
    ((U.comap (MulAut.conj x⁻¹).toMonoidHom).subgroupOf T) W
  refine ⟨B, fun γ => by rw [h1]; rfl, fun g => ?_, h3⟩
  rw [h2, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  simp

private theorem mem_SU {K : Type} [Field K] {Δ : K} (g : DX Δ) : g ∈ SU Δ ↔ (mt g).det = 1 := by
  rw [SU, MonoidHom.mem_ker, ← Units.val_eq_one]
  rfl

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.baseS :
    UpperTheory.V.Z.Sym.Glob.BaseS := by
  intro F _ _ Δ D _ V _ _ W ch htr x
  obtain ⟨-, ⟨ι, hι⟩, -⟩ := iotaEx F Δ
  have hmem : ∀ γ ∈ SU Δ, ι γ ∈ SA Δ := by
    intro γ hγ
    refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 ((mem_SU _).2 ?_)
    have h1 : (mt ((ι γ).1 v)).det = 1 := by
      rw [hι γ v, ← RingHom.mapMatrix_apply, ← RingHom.map_det, (mem_SU γ).1 hγ, map_one]
    exact h1
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := base_sub ι (SU Δ) (SA Δ) D.U2 hmem x W
  refine ⟨B, ⟨fun γ v => ?_, h2, h3, h4, fun γ τ h => ?_⟩, h5⟩
  · rw [h1]
    exact hι _ v
  · rw [h5]
    exact htr γ τ h
