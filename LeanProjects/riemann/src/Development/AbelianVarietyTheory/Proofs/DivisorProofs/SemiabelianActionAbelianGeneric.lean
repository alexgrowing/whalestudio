import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPullbackAbelianGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianGenericIsogenyExtensionStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DieuCover

theorem exists_cover_hasDieu_of_hypotheses : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
  (q : ℕ) [Fact q.Prime], q ≠ 2 → ¬ q ∣ (discr E).natAbs →
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C],
  IsSmoothProjCurve k C → ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct (𝓞 E) G), AbGen (H.bar : 𝓞 E →+* 𝓞 E) i →
  ∃ (C₁ : Scheme.{0}) (_ : Algebra k Γ(C₁, ⊤)) (_ : IsIntegral C₁) (π : C₁ ⟶ C), IsSmoothProjCurve k C₁ ∧ IsCover k π ∧
    ∃ (G₁ : Over C₁) (_ : GrpObj G₁) (_ : IsSemiAbelian G₁) (i₁ : OAct (𝓞 E) G₁) (φ : G₁.left ⟶ G.left), IsActPull i₁ i π φ ∧
      HasDieu q k (H.bar : 𝓞 E →+* 𝓞 E) i₁ :=
  fun hX hP hH => GlobalTheory.T.frobenius_pullback_abelian_generic (GlobalTheory.T.abelian_generic_isogeny_extension hX hX.btd hP) hX hP hH

end GlobalTheory.DieuCover
