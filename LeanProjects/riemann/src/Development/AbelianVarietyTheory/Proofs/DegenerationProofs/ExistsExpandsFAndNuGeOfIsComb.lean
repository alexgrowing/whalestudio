import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionLinearCombIffExpansionSum
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem exists_expandsF_and_nuGe_of_isComb : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k : ℕ), 1 ≤ k → (∀ t : SecA A F k, ∃ σ, U.ExpandsF F k w₀ t σ) ∧ ∀ (I : Type) [Fintype I] (c : I → F) (s : I → SecA A F k) (t : SecA A F k) (q r : ℚ), IsComb s c t → (∀ i, (q : WithTop ℚ) ≤ v (c i)) → (∀ i σ, U.ExpandsF F k w₀ (s i) σ → NuGe D Q F v k σ r) → ∀ σ, U.ExpandsF F k w₀ t σ → NuGe D Q F v k σ (r + q) := by
  intro hL V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ hw k hk
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨h₁, -⟩ := (expBijF_and_expandsF_lin hL V _ hA D A G hG U).1 F k hk w₀ hw
  refine ⟨fun t => (h₁ t).exists, ?_⟩
  intro I _ c s t q r ht hq hs σ hσ
  choose Φ hΦ using fun i => (h₁ (s i)).exists
  have e := (GlobalTheory.TestFibre.isComb_iff_expandsF_sum hL V _ hA D A G hG U F k hk w₀ hw I s Φ c t hΦ).1 ht
  obtain rfl : σ = ∑ i, c i • Φ i := (h₁ t).unique hσ e
  refine Finset.sum_induction _ (fun x => NuGe D Q F v k x (r + q)) (fun a b ha hb => ?_) ?_ fun i _ => ?_
  · exact NuGe.add Q (s := a) (s' := b) (fun _ _ => rfl) ha hb
  · intro χ
    exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
      fun j => by rw [Finset.univ_eq_empty, Finset.sum_empty]; rfl⟩
  · exact NuGe.smul Q (hq i) ((isSmul_iff (c i) (Φ i) _).2 rfl) (hs i _ (hΦ i))

end GlobalTheory.ZH
