import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem linearOn_of_forall_inRCone {O : Type} [CommRing O] (χ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m n : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin n → LinearMap.BilinForm ℤ X}
    (hχ : χ.LinearOn γ) (h : ∀ j, InRCone γ (γ' j)) : χ.LinearOn γ' := by
  intro c hc
  choose a ha he using h
  have hpt : ∀ j x y, (γ' j x y : ℝ) = ∑ i, a j i * (γ i x y : ℝ) := by
    intro j x y
    have := LinearMap.congr_fun₂ (he j) x y
    simpa [LinearMap.sum_apply] using this
  have hev : ∀ j, χ.evalZ (γ' j) = ∑ i, a j i * χ.evalZ (γ i) := by
    intro j
    rw [← hχ (a j) (ha j)]
    simp only [InvFun.evalZ, hpt]
  have e : (fun x y => ∑ j, c j * (γ' j x y : ℝ)) = fun x y => ∑ i, (∑ j, c j * a j i) * (γ i x y : ℝ) := by
    funext x y
    simp only [hpt, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [e, hχ _ (fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (ha j i))]
  simp only [hev, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem subordinate_of_isStarOf : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ w ψ' : InvFun O),
    IsStarOf bar q ψ w ψ' → Subordinate bar q ψ' ψ := by
  intro O _ bar q ψ w ψ' hs χ hχ X _ _ _ _ hX n γ' hγ'
  rcases hs.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, -, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, -, -, -, hβ₀, -, -, hin⟩
  · exact linearOn_of_forall_inRCone χ (hχ X hX m γ hγ) hin
  · refine linearOn_of_forall_inRCone χ (hχ X hX m γ hγ) fun j => inRCone_trans (fun k => ?_) (hin j)
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa using hβ₀
    · simpa using inRCone_self γ (s k)

example : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ w ψ' : InvFun O), IsStarOf bar q ψ w ψ' → Subordinate bar q ψ' ψ :=
  subordinate_of_isStarOf

end GlobalTheory.PolFan
