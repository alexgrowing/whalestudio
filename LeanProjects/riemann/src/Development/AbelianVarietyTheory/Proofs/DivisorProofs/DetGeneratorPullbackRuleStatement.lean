import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGeneratorPullbackRule
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_generator_pullback_rule : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {N : ℕ} {M : Scheme.{0}} {s : M ⟶ Sp (Localization.Away (N : ℤ))} {U : Obj F 𝔠 M} {α : U.Level N} {V : M.Opens},
    IsDPModel N s U α V → ∀ {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k)
    {W : M.Opens} (hW : IsAffineOpen W) {Y : Obj F 𝔠 (Sp Γ(M, W))} {φY : Y.A.left ⟶ U.A.left}, Y.IsPullBy U hW.fromSpec φY →
    ∀ {δY : Y.DetGen} {h h' : R₀ ⊗[ℤ] Γ(M, W)}, IsChartFun r₀ Y δY h → IsChartFun r₀ Y δY h' → h = h' := by
  first | exact @GlobalTheory.RealMult.isChartFun_unique | exact GlobalTheory.RealMult.isChartFun_unique | (intros; apply GlobalTheory.RealMult.isChartFun_unique <;> assumption)
