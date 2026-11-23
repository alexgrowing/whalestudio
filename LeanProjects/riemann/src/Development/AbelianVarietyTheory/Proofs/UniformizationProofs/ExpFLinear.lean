import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLin

theorem sval_comb {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t t' t'' : LB.Sec (LB.LinComb L φ ε)} (a : Γ(Y, ⊤))
    (h : ∀ j, t''.f j = (Y.presheaf.map (homOfLE le_top).op).hom a * t.f j + t'.f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval t'' r z J = gs r z ⊤ a * sval t r z J + sval t' r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ?_
  refine (gs_add _ _ _ hm _ _).trans (congrArg (· + _) ((gs_mul _ _ _ hm _ _).trans (congrArg (· * _) ?_)))
  exact gs_res r z le_top hm a

theorem gs_scal_mul {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (a b : R) : gs r z ⊤ (scal p (a * b)) = gs r z ⊤ (scal p a) * gs r z ⊤ (scal p b) := by
  rw [← gs_mul r z ⊤ trivial]
  simp only [scal, map_mul]

theorem sum_append {α β M : Type*} [AddCommMonoid M] {n m : ℕ} (g : α → β → M) (c : Fin n → α) (c' : Fin m → α)
    (s : Fin n → β) (s' : Fin m → β) :
    ∑ i, g (Fin.append c c' i) (Fin.append s s' i) = ∑ i, g (c i) (s i) + ∑ i, g (c' i) (s' i) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem expF_linear : (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' t'' s s' s'' (c : F), U.ExpF F k t s → U.ExpF F k t' s' → (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) → (∀ α j, (s'' α).f j = DegPre.constBF D F c _ * (s α).f j + (s' α).f j) → U.ExpF F k t'' s'') := by
  intro V _ _ _ _ D A G _ _ U F _ _ k t t' t'' s s' s'' c ⟨n, a, σ, f, h1, h2, h3⟩ ⟨m, a', σ', f', h1', h2', h3'⟩ ht hs
  refine ⟨n + m, Fin.append (fun i => c * a i) a', Fin.append σ σ', Fin.append f f', fun i => ?_,
    fun Z rA y rG e1 e2 z JA JG hA hG => ?_, fun α Z rF rB e z J hJ => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact h1 i
    · simp only [Fin.append_right]; exact h1' i
  · rw [sum_append (fun x y => gs rA z ⊤ (scal (fst (TFK (R := V) F) A.A).left x) * sval y rG z JG),
      ← h2' Z rA y rG e1 e2 z JA JG hA hG]
    simp only [gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h2 Z rA y rG e1 e2 z JA JG hA hG,
      sval_comb (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left) (ε := fun _ => (k : ℤ))
        (scal (fst (TFK (R := V) F) A.A).left c) ht rA z hA]
    ring
  · rw [sum_append (fun x (y : ∀ α, SecBT D (𝟙_ _) k α) =>
      gs rF z ⊤ (scal (fst (TF (R := V) F) D.P.A).left x) * sval (y α) rB z J), ← h3' α Z rF rB e z J hJ]
    simp only [gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h3 α Z rF rB e z J hJ]
    exact sval_comb (scal (fst (TF (R := V) F) D.P.A).left c) (hs α) rF z hJ

end GlobalTheory.UU.ExpLin
end
