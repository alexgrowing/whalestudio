import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem datum_nsmul_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {k : ℕ} (hk : k ≠ 0) {x : D.La} (h : k • x = 0) : x = 0 := by
  apply D.unimod.1
  ext y
  have h1 : D.EF (k • x) y = 0 := by rw [h, map_zero]; rfl
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h1
  rw [map_zero, LinearMap.zero_apply]
  exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hk)

theorem marking_iso_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (i : Fin F.n), (∀ a, (∃ b, F.t i a = l.M • b) → ∃ b, a = l.M • b) ∧ ∀ b, ∃ a e, b = F.t i a + l.M • e := by
  intro E _ _ _ H Dw l Xo _ σ' g ty F i
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact Nat.lcm_ne_zero hM l.A_pos.ne' (by simpa [Geo.Tor.Level.M'] using hk)
  refine ⟨?_, ?_⟩
  · rintro a ⟨b, hb⟩
    obtain ⟨c, hc⟩ := (F.t_inj i (k • a)).1 ⟨b, by rw [map_nsmul, hb, hk, mul_comm, mul_smul]⟩
    refine ⟨c, sub_eq_zero.1 (datum_nsmul_eq_zero Dw hk0 ?_)⟩
    rw [smul_sub, hc, hk, mul_comm, mul_smul, sub_self]
  · intro b
    obtain ⟨a, e, h⟩ := F.t_surj i b
    exact ⟨a, k • e, by rw [h, hk, mul_smul]⟩

end GlobalTheory.AnVal
