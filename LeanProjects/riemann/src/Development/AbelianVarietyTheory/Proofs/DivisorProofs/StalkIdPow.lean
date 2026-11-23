import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheafA
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.Poinc

theorem stalkId_pow' {Y : Scheme.{0}} (I : Y.IdealSheafData) (a : ℕ) (y : Y) :
    ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (I ^ a) y = ReciprocityTheory.AnForm.R.FinalTheorems.stalkId I y ^ a := by
  obtain ⟨W, hW, h₁, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  rw [ds_stalkId_eq_map _ ⟨W, hW⟩ y h₁, ds_stalkId_eq_map _ ⟨W, hW⟩ y h₁, ← Ideal.map_pow]
  rfl

theorem valOn_pow : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S)
    (φ : InvFun ℤ) (J : S.IdealSheafData) (d k : ℕ), ValOn F j φ J d → ValOn F j φ (J ^ k) (k * d) := by
  intro o _ ζ g n F S j φ J d k h T ξ hξ
  obtain ⟨a, ha, hJ⟩ := h T ξ hξ
  refine ⟨k * a, ?_, ?_⟩
  · push_cast; rw [ha]; ring
  · rw [idlAlong, stalkId_pow', Ideal.map_pow, ← idlAlong, hJ, Ideal.span_singleton_pow, pow_mul']

end GlobalTheory.Poinc
