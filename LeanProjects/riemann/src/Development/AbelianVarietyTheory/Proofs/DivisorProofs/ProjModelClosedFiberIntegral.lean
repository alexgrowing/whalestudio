import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefFibreOfNormsPowerStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

set_option autoImplicit false
noncomputable section
open GlobalTheory.ProjVar GlobalTheory.ArInt GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.AmpNefFib

theorem ab_nefFib {D : D7} {O : Setup D} (hO : O.Core) (c : O.s.Comp) : (O.met.ab c).NefFib := by
  obtain ⟨_, P, h⟩ := hO
  rw [h.ab_eq]
  exact P.nefFib_ab c

theorem main : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H),
  ∀ (P : Finset ℕ) (c : O.s.Comp) (X' : Scheme.{0}) (p' : X' ⟶ Sp (𝓞 D.what₂.LL)), IsProjOver p' →
  ∀ (ρ : X' ⟶ (h.mdl P c).V.X) (hρ : ρ ≫ (h.mdl P c).V.p = p') (r : ℕ) [Fact r.Prime]
    (Z : Scheme.{0}) (i : Z ⟶ X') [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod r) Γ(Z, ⊤)],
    topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod r) (((h.mdl P c).amp.pull ρ hρ).B.pull i) 1 := by
  intro hP _ D O hO A T H h P c X' p' hp' ρ hρ r _ Z i _ _ _ hd
  have hV : ArInt.NefFib (h.mdl P c).amp :=
    GlobalTheory.T.nef_fibre_of_norms_power hP _ _ _ (ab_nefFib hO c) _ _ _ (h.mdl P c).k_pos (norms_of_induces (h.mdl P c).amp_spec)
  have hX := ArInt.nefFib_pull _ _ _ _ _ (h.mdl P c).V.ar.isProjOver hp' ρ hρ _ hV
  exact hX Z i (ZMod r) hd

end GlobalTheory.AmpNefFib
