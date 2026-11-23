import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra

noncomputable section

namespace GlobalTheory.TangentLinear

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameTangent

attribute [local instance] Over.cartesianMonoidalCategory

section Comb

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {G : Over X0} [GrpObj G] [IsCommMonObj G]

theorem smT_prod {κ : Type} (s : Finset κ) (a : S) (u : κ → (overAt x0 (DualNumber S) ⟶ G)) :
    smT x0 a (∏ i ∈ s, u i) = ∏ i ∈ s, smT x0 a (u i) := map_prod (smHom x0 a) u s

theorem smT_sum {κ : Type} (s : Finset κ) (c : κ → S) (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) :
    smT x0 (∑ i ∈ s, c i) v = ∏ i ∈ s, smT x0 (c i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, smT_add x0 v h0, ih]

theorem combT_combT {m m' : ℕ} (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (hv : ∀ j, smT x0 0 (v j) = 1)
    (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S) :
    combT x0 (fun i => combT x0 v (fun j => A j i)) N = combT x0 v (A.mulVec N) := by
  simp only [combT, smT_prod, smT_smT]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← smT_sum x0 _ _ _ (hv j)]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => _root_.mul_comm _ _

end Comb

section Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0}

theorem isCombAtG_mulVec {m m' : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (hv : ∀ j, IsTanAtG t x0 (v j))
    (w : Fin m' → (Sp (DualNumber S) ⟶ t.G.left)) (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S)
    (w' : Sp (DualNumber S) ⟶ t.G.left) (h1 : ∀ i, IsCombAtG t x0 v (fun j => A j i) (w i))
    (h2 : IsCombAtG t x0 w N w') : IsCombAtG t x0 v (A.mulVec N) w' := by
  have hw : w = fun i => (combT x0 (fun j => ovT (hv j)) (fun j => A j i)).left :=
    funext fun i => ((isCombAtG_iff t x0 (fun j => ovT (hv j)) _ _).1 (h1 i)).symm
  subst hw
  rw [isCombAtG_iff, combT_combT x0 _ (fun j => smT_zero_ovT (hv j))] at h2
  exact (isCombAtG_iff t x0 (fun j => ovT (hv j)) _ _).2 h2

end Group

theorem isCombAt_mulVec (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ}
    (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hv : ∀ j, IsTanAt x (v j)) {m' : ℕ}
    (w : Fin m' → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S)
    (w' : (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hw : ∀ i, IsCombAt x v (fun j => A j i) (w i))
    (hw' : IsCombAt x w N w') : IsCombAt x v (A.mulVec N) w' :=
  isCombAtG_mulVec (t := Xo.univ.t) (x0 := x) v hv w A N w' hw hw'

end GlobalTheory.TangentLinear
