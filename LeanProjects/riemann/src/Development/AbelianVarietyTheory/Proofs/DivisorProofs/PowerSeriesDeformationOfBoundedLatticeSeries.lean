import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesReparamBoundedCoefficients
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem deform_of_lattice_series : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := by
  intro κ C _ _ _ _ e x g hg m ζ lev k X n π B a b hπ0 hπ1 hfin ha hb hJ hE
  have hA := fun i => lattice_series_regroup C X n π (a i) B hπ0 hπ1 hfin (ha i)
  have hB := fun i j => lattice_series_regroup C X n π (b i j) B hπ0 hπ1 hfin (hb i j)
  choose Θ hΘb hΘs hΘc using hA
  choose Γ hΓb hΓs hΓc using hB
  obtain ⟨ε, hε, hu⟩ := hE
  have heπ : e π ≠ 0 := (map_ne_zero e).2 hπ0
  have hnπ : 0 < ‖e π‖ := norm_pos_iff.2 heπ
  refine ⟨Θ, Γ, π, max B 0, hπ1, fun i l => ⟨hΘb i l, fun j => hΓb i j l⟩, ?_, ε * ‖e π‖, mul_pos hε hnπ, ?_⟩
  · have h1 : (fun i => ∑' l, PowerSeries.coeff l (Θ i) * π ^ l) = fun i => ∑' α, a i α := funext hΘs
    have h2 : (fun i j => ∑' l, PowerSeries.coeff l (Γ i j) * π ^ l) = fun i j => ∑' α, b i j α :=
      funext fun i => funext (hΓs i)
    rw [h1, h2]; exact hJ
  · intro u hu0 hul
    have hv0 : u / e π ≠ 0 := div_ne_zero hu0 heπ
    have hvl : ‖u / e π‖ < ε := by rw [norm_div, div_lt_iff₀ hnπ]; exact hul
    obtain ⟨⟨hsa, hsb⟩, x₀, hg₀, lev₀, hJ₀, hk⟩ := hu (u / e π) hv0 hvl
    refine ⟨fun i => ⟨(hΘc i e u (hsa i)).1, fun j => (hΓc i j e u (hsb i j)).1⟩, x₀, hg₀, lev₀, ?_, hk⟩
    have h1 : (fun i => ∑' l, e (PowerSeries.coeff l (Θ i)) * u ^ l) = fun i => ∑' α, e (a i α) * (u / e π) ^ n α :=
      funext fun i => (hΘc i e u (hsa i)).2
    have h2 : (fun i j => ∑' l, e (PowerSeries.coeff l (Γ i j)) * u ^ l) =
        fun i j => ∑' α, e (b i j α) * (u / e π) ^ n α :=
      funext fun i => funext fun j => (hΓc i j e u (hsb i j)).2
    rw [h1, h2]; exact hJ₀

end GlobalTheory.MBLow
