import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTrdegEqDimensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTrdegFormulaStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem flagged_model_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) [Nonempty K], Function.Injective β → Birational y ∧ IsArithVar (mCoordIdeal y) (Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) + 1) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl _ hβ
  obtain ⟨-, ⟨x, hx⟩, hchar, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y S Ω K J y 𝔐 hβ
  have hA := GlobalTheory.T.generic_trdeg_eq_dimension E H D l Xo c O β Y 𝔐.Ω₀ 𝔐.ξ₀ Ω x 𝔐.fn hβ 𝔐.gen₀ (hx ▸ 𝔐.fn_over)
  letI : Algebra 𝔐.Ω₀ Ω := 𝔐.fn.toAlgebra
  have hB := GlobalTheory.T.generic_flag_trdeg_formula 𝔐.Ω₀ Ω Fl.Li₀ 𝔐.Li Fl.j (CMType H ⊕ CMType H) (labelRk D) Fl.V₀ Fl.b Fl.deg Fl.generic
  haveI : CharZero 𝔐.Ω₀ := (RingHom.charZero_iff 𝔐.fn.injective).mpr hchar
  haveI : FaithfulSMul ℤ 𝔐.Ω₀ := (faithfulSMul_iff_algebraMap_injective ℤ 𝔐.Ω₀).mpr Int.cast_injective
  haveI : FaithfulSMul 𝔐.Ω₀ Ω := (faithfulSMul_iff_algebraMap_injective 𝔐.Ω₀ Ω).mpr 𝔐.fn.injective
  have htow := trdeg_add_eq ℤ 𝔐.Ω₀ (A := Ω)
  rw [hA, hB] at htow
  have hcard : Fintype.card (CMType H) = Module.finrank ℚ E / 2 := by
    rw [Fintype.card_eq_nat_card]; exact GlobalTheory.PeriodCoord.card_cmType H
  have harith : D.dim + ∑ σ : CMType H ⊕ CMType H, labelRk D σ * (labelRk D σ - 1) / 2 =
      Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) := by
    have h1 : (D.p + D.q) * (D.p + D.q - 1) / 2 = D.p * (D.p - 1) / 2 + D.q * (D.q - 1) / 2 + D.p * D.q := by
      rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right, Nat.add_choose_eq]
      simp [Finset.Nat.antidiagonal_succ, Finset.sum_range_succ]
      ring
    rw [Fintype.sum_sum_type, h1, Datum.dim, ← hcard]
    simp [Finset.sum_const, Finset.card_univ, labelRk]
    ring
  have htr : Algebra.trdeg ℤ Ω = ((Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) : ℕ) : Cardinal) := by
    rw [← htow, ← harith]; push_cast; rfl
  exact GlobalTheory.T.birational_of_transcendence_degree 𝔐.X Ω 𝔐.ξ K J y _ 𝔐.tie htr

end GlobalTheory.CompanionTheory.Ar
