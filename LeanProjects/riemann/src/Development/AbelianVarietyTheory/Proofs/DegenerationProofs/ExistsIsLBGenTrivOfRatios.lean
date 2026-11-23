import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem eq_of_res_eq_of_nonempty {U : M.Z.Opens} {f g : Γ(M.Z, U)}
    (h : ∀ hU : (U : Set M.Z).Nonempty, M.res U hU f = M.res U hU g) : f = g := by
  by_cases hU : (U : Set M.Z).Nonempty
  · exact M.res_injective U hU (h hU)
  · obtain rfl : U = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hU)
    exact Subsingleton.elim _ _

theorem exists_unit_res_eq {U : M.Z.Opens} {x : Ω} (hx : x ≠ 0) (h : ∀ z ∈ U, x ∈ M.O z)
    (h' : ∀ z ∈ U, x⁻¹ ∈ M.O z) :
    ∃ g : Γ(M.Z, U)ˣ, ∀ hU : (U : Set M.Z).Nonempty, M.res U hU (g : Γ(M.Z, U)) = x := by
  by_cases hU : (U : Set M.Z).Nonempty
  · obtain ⟨a, ha⟩ := (mem_ringOn_iff_exists hU).1 (mem_ringOn.2 h)
    obtain ⟨b, hb⟩ := (mem_ringOn_iff_exists hU).1 (mem_ringOn.2 h')
    have hab : a * b = 1 := M.res_injective U hU (by
      rw [map_mul, map_one, res_apply, res_apply, ha, hb, mul_inv_cancel₀ hx])
    exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, fun _ => (M.res_apply U hU a).trans ha⟩
  · exact ⟨1, fun h => (hU h).elim⟩

theorem exists_isLB_genTriv_of_ratios : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (ι : Type) (U : ι → M.Z.Opens) (d : ι → Ω), ⨆ k, U k = ⊤ → (∀ k, d k ≠ 0) → (∀ k k', ∀ z ∈ U k ⊓ U k', d k' / d k ∈ M.O z) → ∃ g : ∀ k k', Γ(M.Z, U k ⊓ U k')ˣ, (⟨ι, U, g⟩ : LB M.Z).IsLB ∧ M.GenTriv ⟨ι, U, g⟩ d := by
  intro o Ω _ _ _ M ι U d hU hd hr
  have key : ∀ k k', ∃ g : Γ(M.Z, U k ⊓ U k')ˣ, ∀ h : ((U k ⊓ U k' : M.Z.Opens) : Set M.Z).Nonempty,
      M.res _ h (g : Γ(M.Z, U k ⊓ U k')) = d k' / d k := fun k k' =>
    M.exists_unit_res_eq (div_ne_zero (hd k') (hd k)) (hr k k') fun z hz => by
      rw [inv_div]
      exact hr k' k z ⟨hz.2, hz.1⟩
  choose g hg using key
  have hres : ∀ k k' {V : M.Z.Opens} (h : V ≤ U k ⊓ U k') (hV : (V : Set M.Z).Nonempty),
      M.res V hV ((Semi.res h (g k k') : Γ(M.Z, V)ˣ) : Γ(M.Z, V)) = d k' / d k := fun k k' V h hV =>
    (M.res_resG h hV _).trans (hg k k' _)
  refine ⟨g, ⟨hU, fun i => Units.ext (M.eq_of_res_eq_of_nonempty fun hV => ?_),
    fun i j k => Units.ext (M.eq_of_res_eq_of_nonempty fun hV => ?_)⟩,
    ⟨hd, fun k k' h => (M.res_apply _ h _).symm.trans (hg k k' h)⟩⟩
  · refine (hres i i _ hV).trans ?_
    rw [div_self (hd i), Units.val_one, map_one]
  · rw [Units.val_mul, map_mul]
    refine (congrArg₂ (· * ·) (hres i j _ hV) (hres j k _ hV)).trans (Eq.trans ?_ (hres i k _ hV).symm)
    have := hd i
    have := hd j
    field_simp

end GlobalTheory.ZH.RatModel
end
