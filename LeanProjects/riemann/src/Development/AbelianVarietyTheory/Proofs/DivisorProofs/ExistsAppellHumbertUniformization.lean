import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianThetaFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitianStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem exists_isAH_diag : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → ∀ u : HolUnif X.A (X.diag c) (Module.finrank ℚ F),
    ∃ (u' : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (Hm : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ)
      (χ : u'.Λ → ℂ), u'.ex = u.ex ∧ u'.IsAH Hm χ := by
  intro F _ _ _ 𝔠 X c hc u
  obtain ⟨u', Hm, χ, hex, hH, hχ, hfr⟩ := GlobalTheory.T.exists_hermitian_theta_factor X.A X.ab (X.diag c) (pull_isLB (X.isLB c) _) _ u
  exact ⟨u', Hm, χ, hex, hH,
    GlobalTheory.T.appell_humbert_factor_of_hermitian X.A X.ab (X.diag c) (pull_isLB (X.isLB c) _) (X.pos c hc) _ u' Hm χ hH hχ hfr, hχ, hfr⟩

end GlobalTheory.RealMult.Obj
