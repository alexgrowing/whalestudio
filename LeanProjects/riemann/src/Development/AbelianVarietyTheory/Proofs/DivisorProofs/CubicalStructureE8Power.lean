import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpLinComb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowE8

theorem exists_cp_e8LB : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀) (W : Matrix (Fin 8) (Fin 8) ℤ), ∃ Q : GlobalTheory.UU.CP (powObj G₀ 8), Q.L.L = GlobalTheory.PowE8.e8LB G₀ P.L.L W := by
  intro S G₀ _ _ P W
  haveI hm : ∀ k : (Fin 8 × Fin 8) × Fin 4,
      IsMonHom ((![powPr G₀ k.1.1 * powPr G₀ k.1.2, powPr G₀ k.1.1, powPr G₀ k.1.2, 1] :
        Fin 4 → (powObj G₀ 8 ⟶ G₀)) k.2) := by
    rintro ⟨⟨a, b⟩, i⟩
    fin_cases i <;> dsimp <;>
      first
        | infer_instance
        | exact (inferInstance : IsMonHom (lift (powPr G₀ a) (powPr G₀ b) ≫ μ))
        | exact (inferInstance : IsMonHom (toUnit (powObj G₀ 8) ≫ η[G₀]))
  obtain ⟨Q, hQ⟩ := GlobalTheory.LinCombCP.exists_cp_linComb P (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => (![powPr G₀ k.1.1 * powPr G₀ k.1.2, powPr G₀ k.1.1, powPr G₀ k.1.2, 1] :
      Fin 4 → (powObj G₀ 8 ⟶ G₀)) k.2)
    (fun k => -(W k.1.1 k.1.2 * negε k.2))
  refine ⟨Q, hQ.trans ?_⟩
  unfold GlobalTheory.PowE8.e8LB GlobalTheory.LinCombCP.cpLB
  congr 1
  funext k
  rcases k with ⟨⟨a, b⟩, i⟩
  fin_cases i <;> rfl

end GlobalTheory.PowE8
