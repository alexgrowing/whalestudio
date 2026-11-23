import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselWittDecomposition

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys ValuativeRel Filter Topology

namespace GlobalTheory.TameRead

theorem toZMod_surj (g : ℕ) [Fact g.Prime] : Function.Surjective (PadicInt.toZMod (p := g)) := by
  intro a
  refine ⟨(a.val : ℤ_[g]), ?_⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem units_toZMod_surj (g : ℕ) [Fact g.Prime] :
    Function.Surjective (Units.map (PadicInt.toZMod (p := g)).toMonoidHom) := by
  have : IsLocalHom (PadicInt.toZMod (p := g)) := IsLocalHom.of_surjective _ (toZMod_surj g)
  exact IsLocalRing.surjective_units_map_of_local_ringHom _ (toZMod_surj g) this

theorem val_sub_one_lt (g : ℕ) [Fact g.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (u : ℤ_[g])
    (hu : PadicInt.toZMod u = 1) : valuation F (e (u : ℚ_[g]) - 1) < 1 := by
  have hm : u - 1 ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, hu, map_one, sub_self]
  have hn : ‖u - 1‖ < 1 := PadicInt.mem_nonunits.1 hm
  have hn' : ‖((u : ℚ_[g]) - 1)‖ < 1 := by
    have : ((u - 1 : ℤ_[g]) : ℚ_[g]) = (u : ℚ_[g]) - 1 := by push_cast; rfl
    rw [← this]; exact hn
  have ht : Tendsto (fun n : ℕ => ((u : ℚ_[g]) - 1) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn'
  have ht' : Tendsto (fun n : ℕ => (e ((u : ℚ_[g]) - 1)) ^ n) atTop (𝓝 0) := by
    have := (he.tendsto 0).comp ht
    simpa [Function.comp_def, map_pow] using this
  have h1 : e ((u : ℚ_[g]) - 1) = e (u : ℚ_[g]) - 1 := by rw [map_sub, map_one]
  rw [← h1]
  exact (GlobalTheory.FlatFBCompare.val_lt_one_iff _).2 ht'

theorem exists_tamePart : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ ξ : Fˣ →* ℂˣ, GlobalTheory.SplitWeil.IsTame ξ →
    ∃ χ : (ZMod g)ˣ →* ℂˣ, TamePart (ξ.comp (Units.map e.toMonoidHom)) χ := by
  intro g _ F _ _ _ _ e he ξ hξ
  let μ : ℤ_[g]ˣ →* ℂˣ := (ξ.comp (Units.map e.toMonoidHom)).comp (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom)
  have hker : (Units.map (PadicInt.toZMod (p := g)).toMonoidHom).ker ≤ μ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have hu' : PadicInt.toZMod (u : ℤ_[g]) = 1 := by
      have := congrArg (fun x : (ZMod g)ˣ => (x : ZMod g)) hu
      simpa using this
    apply hξ
    have := val_sub_one_lt g e he (u : ℤ_[g]) hu'
    simpa [μ] using this
  refine ⟨(Units.map (PadicInt.toZMod (p := g)).toMonoidHom).liftOfSurjective (units_toZMod_surj g) ⟨μ, hker⟩, ?_⟩
  intro u
  exact ((Units.map (PadicInt.toZMod (p := g)).toMonoidHom).liftOfRightInverse_comp_apply _
    (Function.rightInverse_surjInv (units_toZMod_surj g)) ⟨μ, hker⟩ u).symm

end GlobalTheory.TameRead
