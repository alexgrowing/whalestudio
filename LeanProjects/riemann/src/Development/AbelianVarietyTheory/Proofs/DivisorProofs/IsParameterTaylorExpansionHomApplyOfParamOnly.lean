import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isTay_apply_of_fn_eq_param : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (f : (I → ℂ) → ℂ), (∀ p ∈ W, h.fn p = f p.1) → ρ h = GlobalTheory.PeriodFamily.taylor N t f ⊗ₜ[ℂ] 1 := by
  intro I _ _ g R _ _ N t W W₀ h0 ρ hρ h f hf
  apply GlobalTheory.tensor_hol_ext_of_values W₀ R
  intro p hp
  have e1 := hρ h p hp
  have e2 : (fun z : I → ℂ ↦ h.fn (z, p.2)) =ᶠ[𝓝 0] f := by
    have hc : Continuous (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) := continuous_id.prodMk continuous_const
    have hm : ∀ᶠ z in 𝓝 (0 : I → ℂ), ((z, p.2) : Tot I g) ∈ W :=
      hc.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds (h0 p hp))
    filter_upwards [hm] with z hz using hf _ hz
  have e3 := (GlobalTheory.PeriodFamily.taylor_formal_properties (D := R) N t).2.2.2.1 _ _ e2
  change evT R p hp (ρ h) = evT R p hp (GlobalTheory.PeriodFamily.taylor N t f ⊗ₜ[ℂ] (1 : Hol W₀))
  rw [e1, e3]
  simp [evT, Algebra.TensorProduct.lift_tmul]

end GlobalTheory.AnPer
