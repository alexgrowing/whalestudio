import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrD
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRawChartFramesBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.FrameBCGen

theorem cφG_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {T T' : Over X0} (ρ : T' ⟶ T) (a b : T ⟶ t.G) :
    cφG t ![ρ ≫ a, ρ ≫ b] = fun I => ρ.left ≫ cφG t ![a, b] I := by
  funext I
  refine Eq.symm (congrArg (fun q => q.left) ((psum_hom (preHom ρ) ![a, b] I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => ?_))))
  fin_cases i <;> rfl

theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t x1 d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 h01 d x x' hx e he
  subst h01
  let ρ : ∀ m, jOG (spMap ψ ≫ x0) d m 2 ⟶ jOG x0 d m 2 := fun m =>
    Over.homMk (spMap (jetCoef ψ (Fin 2 × Fin d) m)) (by
      show spMap (jetCoef ψ (Fin 2 × Fin d) m) ≫ spMap (algebraMap S (Jet S (Fin 2 × Fin d) m)) ≫ x0 =
        spMap (algebraMap S' (Jet S' (Fin 2 × Fin d) m)) ≫ spMap ψ ≫ x0
      rw [← Category.assoc, ← Category.assoc, RawFrameBC.spMap_comp_eq, RawFrameBC.spMap_comp_eq, JetTr.jetCoef_alg])
  have hp : ∀ m (i : Fin 2), jptG t (spMap ψ ≫ x0) d x' m i = ρ m ≫ jptG t x0 d x m i := by
    intro m i
    apply Over.OverMorphism.ext
    show spMap (jetCopy (S := S') d m i).toRingHom ≫ (x' m).left =
      spMap (jetCoef ψ (Fin 2 × Fin d) m) ≫ spMap (jetCopy (S := S) d m i).toRingHom ≫ (x m).left
    rw [hx, ← Category.assoc, ← Category.assoc, RawFrameBC.spMap_comp_eq, RawFrameBC.spMap_comp_eq]
    exact congrArg (fun f => spMap f ≫ (x m).left) (JetTr.jetCoef_copy ψ d m 2 i).symm
  have key := fun m => RawFrameBC.exists_reindexed_pull t.PP.isLB
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) (he m) (ρ m).left
    (cφG t ![jptG t (spMap ψ ≫ x0) d x' m (0 : Fin 2), jptG t (spMap ψ ≫ x0) d x' m (1 : Fin 2)])
    (by rw [hp, hp, cφG_comp])
  choose e' h₁ h₂ _ using key
  exact ⟨e', h₁, h₂⟩

end GlobalTheory.FrameBCGen
