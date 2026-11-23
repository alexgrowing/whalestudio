import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLin

def secComb {X : Scheme.{0}} {L : LB X} {n : ℕ} (b : Fin n → Γ(X, ⊤)) (t : Fin n → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (b i) * (t i).f j
  compat := fun i j => by
    simp only [map_sum, map_mul, (t _).compat, DVR.SecOps.resTop_res, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _

theorem sval_secComb {X Y T Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {n : ℕ} (p : Y ⟶ T) (c : Fin n → Γ(T, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (secComb (fun i => p.appTop.hom (c i)) t) r z J = ∑ i, gs (r ≫ p) z ⊤ (c i) * sval (t i) r z J := by
  rw [DVR.SectionScalarValuation.sval_lin (s := secComb (fun i => p.appTop.hom (c i)) t) (fun i => p.appTop.hom (c i)) t
    (fun _ => rfl) r z hJ]
  exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (gs_pull r p z ⊤ trivial (c i))

theorem sum_comb {S X : Type} [CommRing S] [DecidableEq X] {n : ℕ} (w : S) (c a : Fin n → S) (s : Fin n → Finset X)
    (b : Fin n → X → S) (t : X → S) (h₀ : ∀ i, ∀ α ∉ s i, b i α = 0) (h : ∀ i, w * a i = ∑ α ∈ s i, b i α * t α) :
    w * ∑ i, c i * a i = ∑ α ∈ Finset.univ.biUnion s, (∑ i, c i * b i α) * t α := by
  simp only [Finset.sum_mul]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, h i, Finset.mul_sum]
  simp only [_root_.mul_assoc]
  refine Finset.sum_subset (Finset.subset_biUnion_of_mem s (Finset.mem_univ i)) fun α _ hα => ?_
  rw [h₀ i α hα, zero_mul, mul_zero]

theorem expT_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k n : ℕ) (c : Fin n → Γ(T.left, ⊤)) (σ : Fin n → U.SecGT T k) (f : Fin n → ∀ α, SecBT D T k α), (∀ i, U.ExpT T k (σ i) (f i)) → ∃ (σ' : U.SecGT T k) (f' : ∀ α, SecBT D T k α), U.ExpT T k σ' f' ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ' r z J = ∑ i, gs (r ≫ (fst T G).left) z ⊤ (c i) * sval (σ i) r z J) ∧ ∀ α (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J → sval (f' α) r z J = ∑ i, gs (r ≫ (fst T D.P.A).left) z ⊤ (c i) * sval (f i α) r z J := by
  classical
  intro R _ _ I D A G _ _ U T k n c σ f h
  refine ⟨secComb (fun i => (fst T G).left.appTop.hom (c i)) σ,
    fun α => secComb (fun i => (fst T D.P.A).left.appTop.hom (c i)) (fun i => f i α), fun e => ?_,
    fun Z r z J hJ => sval_secComb _ c σ r z hJ, fun α Z r z J hJ => sval_secComb _ c (fun i => f i α) r z hJ⟩
  choose s hs using fun i => h i e
  refine ⟨Finset.univ.biUnion s, fun Z x rG rB h₁ h₂ h₃ z JG J hG hJ => ⟨fun α hα => ?_, ?_⟩⟩
  · rw [sval_secComb _ c (fun i => f i α) rB z hJ]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hs i Z x rG rB h₁ h₂ h₃ z JG J hG hJ).1 α
      (fun hi => hα (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hi⟩)), mul_zero]
  · rw [sval_secComb _ c σ rG z hG]
    refine Eq.trans ?_ (Finset.sum_congr rfl fun α _ =>
      (congrArg (· * _) (sval_secComb (fst T D.P.A).left c (fun i => f i α) rB z hJ)).symm)
    rw [h₃]
    exact sum_comb _ _ _ s (fun i α => sval (f i α) rB z J) _
      (fun i => (hs i Z x rG rB h₁ h₂ h₃ z JG J hG hJ).1) (fun i => (hs i Z x rG rB h₁ h₂ h₃ z JG J hG hJ).2)

end GlobalTheory.UU.ExpLin
end
