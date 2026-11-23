import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gs_linSum {Y Z : Scheme.{0}} {R : Type} [CommRing R] (p : Y ⟶ Sp R) {I : Type} [Fintype I] (a : I → R)
    (r : Z ⟶ Y) (z : Z) (W : Y.Opens) (hm : r z ∈ W) (f : I → Γ(Y, W)) :
    gs r z W (∑ i, constFn p W (a i) * f i) = ∑ i, cst (r ≫ p) z (a i) * gs r z W (f i) := by
  have e : ∀ (b : I → Γ(Y, W)), gs r z _ (∑ i, b i) = ∑ i, gs r z _ (b i) := fun b => by
    simp only [gs_eq r z _ hm, map_sum]
  rw [e]
  exact Finset.sum_congr rfl fun i _ => (gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_constFn p _ r z hm _) rfl)

theorem isLin_iff_of_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ (I : Type) [Fintype I] (b : I → LB.Sec (LB.LinComb L ψ ε)) (φ : I → (Φ.H 1).Sec) (b₀ : LB.Sec (LB.LinComb L ψ ε)) (φ₀ : (Φ.H 1).Sec) (a : I → k), (∀ i, UFib.Red Φ c t (b i) (φ i)) → UFib.Red Φ c t b₀ φ₀ → (IsLin Φ.E.B.hom b a b₀ ↔ IsLin Φ.G.hom φ a φ₀) := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t _ I _ b φ b₀ φ₀ a hb hb₀
  have pick : ∀ (y : Φ.G.left) (l : Φ.N₀.ι), y ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l →
      ∃ J, Good L y J ∧ J (𝟙 _ ≫ Φ.D.q.left ≫ π) = c.idx l := fun y l hy => by
    obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : PUnit => 𝟙 _ ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
      (fun _ _ _ => rfl) (fun _ => c.le l hy)
    exact ⟨J, hJ, e PUnit.unit⟩
  have hw : (𝟙 _ ≫ Φ.D.q.left) ≫ Φ.E.B.hom = 𝟙 _ ≫ Φ.G.hom := by
    rw [Category.assoc, Over.w]
  constructor
  · intro h l
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := pick y l hy
    refine (hb₀ _ (𝟙 _) y J hJ l hy e).trans (Eq.trans ?_ (gs_linSum Φ.G.hom a (𝟙 _) y _ hy _).symm)
    have m := hJ.mem ψ (𝟙 _ ≫ Φ.D.q.left)
    have e₁ : sval b₀ (𝟙 _ ≫ Φ.D.q.left) y J =
        ∑ i, cst (𝟙 _ ≫ Φ.G.hom) y (a i) * sval (b i) (𝟙 _ ≫ Φ.D.q.left) y J := by
      rw [← hw]
      exact (congrArg (gs _ y _) (h _)).trans (gs_linSum Φ.E.B.hom a _ y _ m _)
    rw [e₁, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (mul_assoc _ _ _).trans (congrArg _ (hb i _ (𝟙 _) y J hJ l hy e).symm)
  · intro h j
    have := Φ.D.q_flat
    have := Φ.D.q_surjective
    apply GlobalTheory.FunDescent.app_injective Φ.D.q.left
    refine fn_ext fun y hy => ?_
    refine (gs_pull (𝟙 _) Φ.D.q.left y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) Φ.D.q.left y _ hy _).symm)
    refine Eq.trans ?_ (gs_linSum Φ.E.B.hom a (𝟙 _ ≫ Φ.D.q.left) y _ hy _).symm
    obtain ⟨l, hl⟩ := exists_chart Φ.isLB (Φ.D.q.left y)
    obtain ⟨J, hJ, e⟩ := pick y l hl
    have m := hJ.mem ψ (𝟙 _ ≫ Φ.D.q.left)
    have e₁ : sval b₀ (𝟙 _ ≫ Φ.D.q.left) y J =
        ∑ i, cst (𝟙 _ ≫ Φ.G.hom) y (a i) * sval (b i) (𝟙 _ ≫ Φ.D.q.left) y J := by
      refine (Units.mul_left_inj (val t (𝟙 _) y J)).1 ?_
      refine (hb₀ _ (𝟙 _) y J hJ l hl e).symm.trans ((congrArg (gs _ y _) (h l)).trans
        ((gs_linSum Φ.G.hom a (𝟙 _) y _ hl _).trans ?_))
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (congrArg _ (hb i _ (𝟙 _) y J hJ l hl e)).trans (mul_assoc _ _ _).symm
    refine (sec_trans b₀ (𝟙 _ ≫ Φ.D.q.left) y (j := j) hy m).trans ((congrArg _ e₁).trans ?_)
    rw [Finset.mul_sum, hw]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (mul_left_comm _ _ _).trans (congrArg _ (sec_trans (b i) (𝟙 _ ≫ Φ.D.q.left) y (j := j) hy m).symm)

end GlobalTheory.ZH.UFib
end
