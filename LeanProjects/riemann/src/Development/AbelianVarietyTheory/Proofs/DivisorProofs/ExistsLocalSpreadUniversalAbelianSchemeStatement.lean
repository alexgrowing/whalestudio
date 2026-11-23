import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpreadUniversalAbelianScheme
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_spread_universal_abelian_scheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (o₁ Ω : Type) [CommRing o₁] [Field Ω] [Algebra o₁ Ω] [ArithBase o₁ Ω] (M : RatModel o₁ Ω) (π : M.Z ⟶ C.Z) (uη : Sp Ω ⟶ Xo.XF c), GlobalTheory.IsNormalScheme M.Z → M.pt ≫ π = uη ≫ C.i → ∀ (A₁ : PolAV (Sp Ω)) (m : ℕ) (ze : o₁ˣ), IsUnit (m : o₁) → UOver Xo c A₁ (RingHom.id Ω) uη → Out.Level A₁ m (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze)) → ∀ (K : Type) [Field K] (yM : Sp K ⟶ M.Z) (y : Sp K ⟶ Xo.XF c), yM ≫ π = y ≫ C.i → ∃ (R : Subalgebra o₁ Ω) (P : PolAV (Sp R)) (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c) (𝔭 : Ideal R), R.FG ∧ (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ P.g = A₁.g ∧ HypS P.A P.L ∧ Nonempty (Out.Level P m (unitOn (Units.map (algebraMap o₁ R).toMonoidHom ze))) ∧ (∀ a, IsMonHom (act a)) ∧ GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u ∧ spMap (ratHull R).val.toRingHom ≫ u = uη ∧ 𝔭.IsPrime ∧ ∀ a b : R, b ∉ 𝔭 → (a : Ω) / (b : Ω) ∈ M.O (yM (closedPoint K)) := by
  first | exact @GlobalTheory.UCovSep.LocalSpread.exists_local_spread | exact GlobalTheory.UCovSep.LocalSpread.exists_local_spread | (intros; apply GlobalTheory.UCovSep.LocalSpread.exists_local_spread <;> assumption)
