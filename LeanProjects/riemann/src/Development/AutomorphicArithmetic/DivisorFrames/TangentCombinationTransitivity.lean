import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

theorem UpperTheory.tangent_combination_transitivity :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (K : Type) [Field K] (x : Sp K ⟶ X) (g r : ℕ) (e : Fin g → (Sp (DualNumber K) ⟶ t.G.left)) (u : Fin r → (Sp (DualNumber K) ⟶ t.G.left)) (A : Fin r → Fin g → K), (∀ i, IsTanAtG t x (e i)) → (∀ i, IsCombAtG t x e (A i) (u i)) → (∀ (cf : Fin r → K) w, IsCombAtG t x u cf w ↔ IsCombAtG t x e (∑ i, cf i • A i) w) ∧ (IsIndep t x u → LinearIndependent K A) := by
  intro E _ _ _ H X t K _ x g r e u A he hA
  have hu : ∀ i, IsTanAtG t x (u i) := fun i => GlobalTheory.ShFam.Pad.Guard.comb_tan he (hA i)
  have hm : ∀ cf : Fin r → K, Matrix.mulVec (Matrix.of fun j i => A i j) cf = ∑ i, cf i • A i := by
    intro cf
    funext j
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have fwd : ∀ (cf : Fin r → K) w, IsCombAtG t x u cf w → IsCombAtG t x e (∑ i, cf i • A i) w := by
    intro cf w h
    rw [← hm]
    exact tanLinG e he u (Matrix.of fun j i => A i j) cf w hA h
  have key : ∀ (cf : Fin r → K) w, IsCombAtG t x u cf w ↔ IsCombAtG t x e (∑ i, cf i • A i) w := by
    intro cf w
    refine ⟨fwd cf w, fun h => ?_⟩
    obtain ⟨w', -, h'⟩ := GlobalTheory.ShFam.Pad.Guard.exists_comb hu cf
    exact GlobalTheory.ShFam.Pad.Guard.comb_unique he (fwd cf w' h') h ▸ h'
  refine ⟨key, fun hi => ?_⟩
  rw [Fintype.linearIndependent_iffₛ]
  intro cf cf' hc
  obtain ⟨w, -, h⟩ := GlobalTheory.ShFam.Pad.Guard.exists_comb hu cf
  have h' : IsCombAtG t x u cf' w := (key cf' w).2 (hc ▸ (key cf w).1 h)
  exact congrFun (hi _ _ w h h')
