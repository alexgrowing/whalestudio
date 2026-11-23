import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointNumberFieldModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalPointNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalPointClosedPointImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointOverNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisCardEqDimStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieRead

theorem fibAt_interior : Hypotheses2 → HypothesesH → OnObj fun D O _ _ H _ => ∀ y : Pt O.s, y ∈ H.int → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (F : SemiFib K) (ι : K →+* Qb), F.P₀.g = D.R.f * O.N ∧ FibTie O y F ι := by
  intro _ _ D O _ _ A T H h y hy
  have hb := (h.ht.int y).1 hy
  obtain ⟨K, _, _, ι, jF, yK, uK, h1, h2, h3, h4⟩ := GlobalTheory.T.flag_point_number_field_model O.s.T.Z y
  have hK : yK (IsLocalRing.closedPoint K) ∉ genBd O.s.T.Z := by
    intro hm
    apply hb
    have e : (spMap ι) (IsLocalRing.closedPoint Qb) = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    show y.y (IsLocalRing.closedPoint Qb) ∈ _
    rw [← h2]
    show yK ((spMap ι) (IsLocalRing.closedPoint Qb)) ∈ _
    rw [e]
    exact hm
  obtain ⟨yO, hO⟩ := GlobalTheory.T.toroidal_point_number_field O.s.T.Z K jF yK h3
  obtain ⟨P₀, θ, hθ, hL⟩ := GlobalTheory.T.toroidal_point_closed_point_image O.s.T.Z K yK hK
  obtain ⟨v₀, hv₀, -⟩ := GlobalTheory.T.flag_point_over_number_field O.s.T.Z y K ι jF yK uK h1 h2 h3 h4 P₀ θ hθ _ rfl
  have hg : P₀.g = (letters O.S.Dw).length := GlobalTheory.T.lie_basis_card_eq_dim K P₀ _ v₀ hv₀
  obtain ⟨v, hv, hvu⟩ := GlobalTheory.T.flag_point_over_number_field O.s.T.Z y K ι jF yK uK h1 h2 h3 h4 P₀ θ hθ P₀.g hg
  letI : GrpObj ((Over.pullback yO).obj O.s.T.Z.t.G) := Functor.grpObjObj
  have hψ := isGrpPullback_pullback O.s.T.Z.t.G yO
  have w : θ ≫ O.s.T.Z.t.G.hom = (P₀.A.hom ≫ spMap (algebraMap (𝓞 K) K)) ≫ yO := by
    rw [Category.assoc, hO]; exact hθ.1.w
  let φ : P₀.A.left ⟶ ((Over.pullback yO).obj O.s.T.Z.t.G).left := pullback.lift θ (P₀.A.hom ≫ spMap (algebraMap (𝓞 K) K)) w
  have hφψ : φ ≫ pullback.fst O.s.T.Z.t.G.hom yO = θ := pullback.lift_fst _ _ _
  have hfib : IsGrpPullback P₀.A ((Over.pullback yO).obj O.s.T.Z.t.G) (spMap (algebraMap (𝓞 K) K)) φ := by
    refine IsGrpPullback.cancel hψ ?_ (pullback.lift_snd _ _ _)
    rw [hφψ, hO]
    exact hθ
  refine ⟨K, inferInstance, inferInstance,
    ⟨P₀, (Over.pullback yO).obj O.s.T.Z.t.G, IsSemiAbelian.pullback yO O.s.T.Z.t.G O.s.T.Z.t.semi, φ, hfib, v, hv⟩,
    ι, ?_, ?_⟩
  · show P₀.g = _
    rw [hg]
    exact length_letters O.S
  · refine ⟨jF, yO, pullback.fst _ _, h1, ?_, hψ, ?_, hg, ?_⟩
    · rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      change spMap ι ≫ spMap (algebraMap (𝓞 K) K) ≫ yO = _
      rw [hO, ← Category.assoc, h2]
    · show LBIso (O.s.T.Z.t.PP.L.pull (φ ≫ _)) P₀.L
      rw [hφψ]
      exact hL
    · intro k x hx
      show _ = _ ≫ (v k).left ≫ φ ≫ _
      rw [hφψ, hvu k x hx, h4]

end GlobalTheory.LieRead

end
