import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFLinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLinC

theorem gs_sum' {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hm : r z ∈ U) {K : Type} (S : Finset K)
    (a : K → Γ(Y, U)) : gs r z U (∑ i ∈ S, a i) = ∑ i ∈ S, gs r z U (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := gs_add r z U hm 0 0
    rw [add_zero] at h
    simpa using h
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, gs_add r z U hm, ih]

theorem sval_lincomb {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ}
    {t : Fin n → LB.Sec (LB.LinComb L φ ε)} {t' : LB.Sec (LB.LinComb L φ ε)} (a : Fin n → Γ(Y, ⊤))
    (h : ∀ j, t'.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (a i) * (t i).f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval t' r z J = ∑ i, gs r z ⊤ (a i) * sval (t i) r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ?_
  refine (gs_sum' _ _ _ hm _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  exact (gs_mul _ _ _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm (a i)))

theorem expF_lincomb : (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k n : ℕ) (c : Fin n → F) (t : Fin n → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s : Fin n → Raw D F k) (t' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s' : Raw D F k), (∀ i, U.ExpF F k (t i) (s i)) → (∀ j, t'.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (t i).f j) → (∀ α j, (s' α).f j = ∑ i, DegPre.constBF D F (c i) _ * (s i α).f j) → U.ExpF F k t' s') := by
  intro V _ _ _ _ D A G _ _ U F _ _ k n c t s t' s' H ht hs
  choose m a σ f h1 h2 h3 using H
  let e : Fin (Fintype.card (Σ i, Fin (m i))) ≃ (Σ i, Fin (m i)) := (Fintype.equivFin _).symm
  refine ⟨_, fun p => c (e p).1 * a (e p).1 (e p).2, fun p => σ (e p).1 (e p).2, fun p => f (e p).1 (e p).2,
    fun p => h1 _ _, fun Z rA y rG e1 e2 z JA JG hA hG => ?_, fun α Z rF rB e0 z J hJ => ?_⟩
  · rw [e.sum_comp (fun q => gs rA z ⊤ (scal (fst (TFK (R := V) F) A.A).left (c q.1 * a q.1 q.2)) *
      sval (σ q.1 q.2) rG z JG), Fintype.sum_sigma,
      sval_lincomb (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left) (ε := fun _ => (k : ℤ))
        (fun i => scal (fst (TFK (R := V) F) A.A).left (c i)) ht rA z hA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ExpLin.gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h2 i Z rA y rG e1 e2 z JA JG hA hG]
    ring
  · rw [e.sum_comp (fun q => gs rF z ⊤ (scal (fst (TF (R := V) F) D.P.A).left (c q.1 * a q.1 q.2)) *
      sval (f q.1 q.2 α) rB z J), Fintype.sum_sigma]
    refine (sval_lincomb (fun i => scal (fst (TF (R := V) F) D.P.A).left (c i)) (hs α) rF z hJ).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ExpLin.gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h3 i α Z rF rB e0 z J hJ]

end GlobalTheory.UU.ExpLinC
end
