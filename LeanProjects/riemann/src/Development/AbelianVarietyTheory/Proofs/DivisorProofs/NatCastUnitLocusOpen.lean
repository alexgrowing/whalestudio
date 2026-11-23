import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitLocus

theorem isUnit_of_basicOpen_eq_top' {Y : Scheme.{0}} (s : Γ(Y, ⊤)) (h : Y.basicOpen s = ⊤) : IsUnit s :=
  Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Y.mem_basicOpen _ x hx).1 (h.ge hx)

theorem natCast_unit_locus (S' : Scheme.{0}) (d : ℕ) : ∃ U : S'.Opens,
    (∀ V : S'.Opens, V ≤ U → IsUnit ((d : ℕ) : Γ(V.toScheme, ⊤))) ∧
    ∀ (T : Scheme.{0}) (g : T ⟶ S'), IsUnit ((d : ℕ) : Γ(T, ⊤)) → Set.range g.base ⊆ (U : Set S') := by
  refine ⟨S'.basicOpen ((d : ℕ) : Γ(S', ⊤)), ?_, ?_⟩
  · intro V hV
    apply isUnit_of_basicOpen_eq_top'
    have e := Scheme.preimage_basicOpen_top V.ι ((d : ℕ) : Γ(S', ⊤))
    rw [map_natCast] at e
    rw [← e, eq_top_iff]
    intro x _
    show V.ι.base x ∈ S'.basicOpen _
    exact hV (show V.ι x ∈ (V : Set S') by rw [← Scheme.Opens.range_ι V]; exact ⟨x, rfl⟩)
  · intro T g hd
    rintro _ ⟨x, rfl⟩
    have e := Scheme.preimage_basicOpen_top g ((d : ℕ) : Γ(S', ⊤))
    rw [map_natCast, T.basicOpen_of_isUnit hd] at e
    have hx : x ∈ g ⁻¹ᵁ S'.basicOpen ((d : ℕ) : Γ(S', ⊤)) := by rw [e]; trivial
    exact hx

end GlobalTheory.UnitLocus
