import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculusStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActLevIffLevelActionOver
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.MoveOrder

theorem finite_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) («γ» : LevelAut Dw l) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), 1 ≤ Dw.p + Dw.q → l.A = 1 → IsIso ρ → IsLevMove ρ ν (liftLa «γ») LinearMap.id → ∃ n : ℕ, 0 < n ∧ (fun f : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left => f ≫ ν.φ)^[n] (𝟙 _) = 𝟙 _ := by
  intro E _ _ _ H Dw l Xo c γ ρ ν hpq hl hρ hm
  have hA : l.A.Coprime l.M := by rw [hl]; exact Nat.coprime_one_left _
  obtain ⟨⟨ι, hι, -⟩, hmul, -⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
  have h₀ : IsLevMove (𝟙 Xo.X) ι (liftLa (1 : LevelAut Dw l)) LinearMap.id := by
    refine ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  have key : ∀ k : ℕ, ∃ (ρk : Xo.X ⟶ Xo.X) (μ : SABMap Xo.univ.t Xo.univ.t ρk), IsIso ρk ∧
      IsLevMove ρk μ (liftLa («γ» ^ k)) LinearMap.id ∧
      μ.φ = (fun f : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left => f ≫ ν.φ)^[k] (𝟙 _) := by
    intro k
    induction k with
    | zero => exact ⟨𝟙 _, ι, inferInstance, by rw [pow_zero]; exact h₀, by rw [hι]; rfl⟩
    | succ k ih =>
      obtain ⟨ρk, μ, ik, hk, hφ⟩ := ih
      obtain ⟨κ, hκ, -⟩ := hmul ρk ρ μ ν
      refine ⟨ρk ≫ ρ, κ, inferInstance, ⟨?_, fun a => ?_, fun a => ?_⟩, ?_⟩
      · rw [Category.assoc, hm.1, hk.1]
      · rw [pow_succ, GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub («γ» ^ k) «γ» a), hκ,
          ← Category.assoc, hk.2.1, Category.assoc, hm.2.1, Category.assoc]
      · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a =
            (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
        rw [e, hκ, ← Category.assoc, hk.2.2, Category.assoc, hm.2.2, Category.assoc]
      · rw [hκ, hφ, Function.iterate_succ_apply']
  refine ⟨orderOf «γ», orderOf_pos «γ», ?_⟩
  obtain ⟨ρn, μ, i, h, hφ⟩ := key (orderOf «γ»)
  rw [pow_orderOf_eq_one] at h
  rw [← hφ, (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c 1 i inferInstance h h₀).2, hι]

end GlobalTheory.MoveOrder
