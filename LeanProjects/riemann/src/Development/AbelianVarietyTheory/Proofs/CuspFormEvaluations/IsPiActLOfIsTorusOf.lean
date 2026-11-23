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

namespace GlobalTheory.AnVal.IsPiAct

theorem negOnePow_natCast_mul (M : ℕ) (k : ℤ) :
    Int.negOnePow ((M : ℤ) * k) = Int.negOnePow k ^ M := by
  induction M with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [add_mul, _root_.one_mul, Int.negOnePow_add, ih, pow_succ]

theorem isPi_actL_of_isTorusOf :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pm : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsPeriod D ty Pm → IsTorusOf D ty Pm Hm T ψ → ∀ (α : 𝓞 E) (M : ℕ), α * H.bar α = (M : 𝓞 E) → I2.IsPi T M (vspActL α) := by
  intro E _ _ _ H D g ty Pm Hm T ψ hP hT α M hM
  obtain ⟨-, -, -, hL, hact, heps⟩ := hT

  have hnorm : ∀ τ : E →+* ℂ, τ (α : E) * starRingEnd ℂ (τ (α : E)) = (M : ℂ) := by
    intro τ
    have h := congrArg (fun x : 𝓞 E => τ (x : E)) hM
    push_cast at h
    have hb := congrArg τ (H.bar_eq α)
    rw [IsCMField.complexEmbedding_complexConj] at hb
    rw [map_mul, map_natCast] at h
    rw [← hb]
    exact h
  have hcoord : ∀ (u : I2.Vsp T.dim) i, (I2.act α u) i = i.1 (α : E) * u i := fun _ _ => rfl

  have hlat : ∀ a, I2.act α (ψ (Pm a)) = ψ (Pm (α • a)) := by
    intro a
    rw [← hact]
    congr 1
    funext k
    exact (hP.1 α a k).symm
  unfold I2.IsPi
  refine ⟨fun β v => ?_, fun x hx => ?_, fun v w => ?_, fun x hx => ?_⟩ <;>
    simp only [vspActL, LinearMap.coe_mk, AddHom.coe_mk]
  · ext i
    change i.1 (α : E) * (i.1 (β : E) * v i) = i.1 (β : E) * (i.1 (α : E) * v i)
    ring
  · obtain ⟨a, rfl⟩ := (hL x).1 hx
    rw [hlat, hL]
    exact ⟨α • a, rfl⟩
  · unfold I2.Hf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoord, hcoord, map_mul]
    linear_combination (v i * starRingEnd ℂ (w i)) * hnorm i.1
  · obtain ⟨a, rfl⟩ := (hL x).1 hx
    have hEF : D.EF (α • a) (H.w0 • α • a) = (M : ℤ) * D.EF a (H.w0 • a) := by
      have hc : H.bar α * H.w0 * α = (M : 𝓞 E) * H.w0 := by rw [← hM]; ring
      rw [D.adj, smul_smul, smul_smul, hc, mul_smul, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
    rw [hlat, heps, heps, hEF, negOnePow_natCast_mul, Units.val_pow_eq_pow_val]

end GlobalTheory.AnVal.IsPiAct
