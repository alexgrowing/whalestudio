import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedBimultiplicativeGeneratorLambdaInvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTrivialisationOfBalancedBimultiplicativStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiGeneratorsDegenerationLawsSymmetricBalaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPreDataLawsOfGeneratorValuesStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UTau0

theorem exists_symmetric_balanced_generator_psi_zero_localRing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ : DegPre R) (O : Type) [CommRing O]
    [StarRing O] [Module O D₀.X] [Module.Projective O D₀.X] [Module.Finite O D₀.X] (onB : D₀.P.OAct O),
    (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) → ∀ w0 : O, w0 + star w0 = 1 →
    (∃ u : LB.Gen (LB.LinComb D₀.P.L (K := Fin 4) ![(padd D₀.P.A (𝟙 _) (onB.act w0)).left, 𝟙 D₀.P.A.left,
        (onB.act w0).left, (toUnit D₀.P.A ≫ η[D₀.P.A]).left] ![1, -2, -1, 2]),
      u.IsGen ∧ LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (eSec D₀.P.A)) (LB.oneGen D₀.P.L)) →
    ∃ (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => ptK (D₀.c y)) (fun _ => -1)))
      (h : ∀ y, (ψ y).IsGen),
      letI : Module O ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).X := ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).OAct O, oa.onB = onB ∧
        ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := ψ, psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := ψ, psi_gen := h } : DegPre R) y Set.univ := by
  intro R _ _ _ D₀ O _ _ _ _ _ onB hlin w0 hw ⟨uw, huw, huw0⟩
  have cadd : ∀ y y' : D₀.X, D₀.c (y + y') = D₀.c y * D₀.c y' := fun y y' => D₀.c_add y y'
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_balanced_bimultiplicative_generator_lambda_inv R D₀.P.A D₀.P.isAb ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub O onB.toRingAct
    onB.rosati D₀.X D₀.c cadd hlin
  obtain ⟨τ', hτ', hτs⟩ := GlobalTheory.T.symmetric_trivialisation_of_balanced_bimultiplicative R D₀.P.A D₀.P.isAb ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub O
    onB.toRingAct onB.rosati D₀.X D₀.c cadd hlin w0 hw τ hτ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_psi_generators_degenerationLaws_symmetricBalanced R D₀ O onB hlin w0 hw uw huw huw0 τ' hτ' hτs
  obtain ⟨h, rest⟩ := GlobalTheory.T.degenerationPreData_laws_of_generator_values R D₀ O onB hlin w0 uw huw huw0 ψ hψ
  exact ⟨_, h, rest⟩

end GlobalTheory.UTau0
