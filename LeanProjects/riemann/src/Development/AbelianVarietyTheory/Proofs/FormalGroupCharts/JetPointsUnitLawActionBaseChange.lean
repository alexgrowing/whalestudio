import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrD

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.JetPointBC

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

section Maps

variable {X0 : Scheme.{0}} {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0)

def baseMap : overAt (spMap ψ ≫ x0) S' ⟶ overAt x0 S :=
  Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap (algebraMap S S) ≫ x0 = spMap (algebraMap S' S') ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap]
    first | done | rfl)

def jetPtMap (d m n : ℕ) : jOG (spMap ψ ≫ x0) d m n ⟶ jOG x0 d m n :=
  Over.homMk (spMap (jetCoef ψ (Fin n × Fin d) m)) (by
    show spMap (jetCoef ψ (Fin n × Fin d) m) ≫ spMap (algebraMap S _) ≫ x0 =
      spMap (algebraMap S' _) ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap, JetTr.jetCoef_alg])

theorem sq_aug (d m : ℕ) :
    homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin 1 × Fin d) m →ₐ[S'] S') ≫ jetPtMap ψ x0 d m 1 =
      baseMap ψ x0 ≫ homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetCoef ψ _ m) = spMap ψ ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (JetTr.jetCoef_aug ψ _ m)

theorem sq_subst {n n' d : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) :
        Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m) ≫ jetPtMap ψ x0 d m n =
      jetPtMap ψ x0 d m n' ≫
        homAt x0 (jetSubstP m φ : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetCoef ψ _ m) = spMap (jetCoef ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (JetTr.jetCoef_substP ψ m φ).symm

theorem sq_copy (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        jetPtMap ψ x0 d m 1 =
      jetPtMap ψ x0 d m n ≫
        homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetCoef ψ _ m) = spMap (jetCoef ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (JetTr.jetCoef_copy ψ d m n i).symm

end Maps

theorem unit_law_act_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ((∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) → (∀ m, homAt x1 (jetAug : Jet S' (Fin 1 × Fin d) m →ₐ[S'] S') ≫ x' m = 1)) ∧ (∀ F : Fin d → PS S 2 d, (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m = jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) → (∀ m, homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (MvPowerSeries.map ψ (F p.2))) ≫ x' m = jptG t x1 d x' m (0 : Fin 2) * jptG t x1 d x' m (1 : Fin 2))) ∧ ∀ act : 𝓞 E → Fin d → PS S 1 d, (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (∀ m (b : 𝓞 E), x m ≫ t.act.act b = homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m) → (∀ m (b : 𝓞 E), x' m ≫ t.act.act b = homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (MvPowerSeries.map ψ (act b p.2))) ≫ x' m) := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 hx1 d x x' hx'
  subst hx1
  obtain rfl : x' = fun m => jetPtMap ψ x0 d m 1 ≫ x m :=
    funext fun m => Over.OverMorphism.ext (hx' m)
  refine ⟨fun h m => ?_, fun F _ h m => ?_, fun act _ h m b => ?_⟩
  · rw [← Category.assoc, sq_aug, Category.assoc, h m]
    simp [Hom.one_def]
  · simp only [JetTr.psTrunc_map]
    rw [← Category.assoc, sq_subst, Category.assoc, h m]
    simp only [jptG, Hom.mul_def, comp_lift_assoc]
    rw [← Category.assoc (homAt _ _) (jetPtMap _ _ _ _ _), ← Category.assoc (homAt _ _) (jetPtMap _ _ _ _ _),
      sq_copy, sq_copy, Category.assoc, Category.assoc]
  · simp only [JetTr.psTrunc_map]
    rw [← Category.assoc (homAt _ _), sq_subst, Category.assoc, Category.assoc, h m b]

end GlobalTheory.JetPointBC
