import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToUnitCompLeft
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanAlg

open ConstTerm

theorem core {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    {R₀ : Type} [CommRing R₀] [IsDomain R₀] {D₀ : Out.DegPre R₀} {S₀ : Type} [CommRing S₀] {σ₀ : Sp S₀ ⟶ Sp R₀}
    (κ : R →+* S) (ρ : S₀ →+* S) {φ : D.toPre.P.A.left ⟶ D₀.P.A.left}
    (w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)) (g : Out.GtPt D.toPre (Over.mk (spMap κ)))
    (g₀ : Out.GtPt D₀ (Over.mk σ₀)) {α : D.toPre.X} {α₀ : D₀.X}
    (hg : GenRelR (A := S) w (g.s α) (LB.pullGen _ _ _ (g₀.s α₀) (spMap ρ))) {j : ℕ} (s₀ : D₀.SecB j α₀)
    (f : D.toPre.SecB j α) (r : R)
    (hf : ∀ (p : Sp S ⟶ D.toPre.P.A.left) (jf : Fin 4 → D.toPre.P.L.ι) (j₀ : Fin 4 → D₀.P.L.ι),
      p ≫ D.toPre.P.A.hom = spMap κ →
      (∀ i, ⊤ ≤ (p ≫ D.toPre.famφB α i) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
      ∃ t : Fin 4 → Sˣ, (∀ i, (t i : S) = valR (p ≫ D.toPre.famφB α i) _ (w.s (fun _ => j₀ i, jf i)).val) ∧
        (∏ i, t i ^ Out.DegPre.famε j i : Sˣ) * valR p (LB.wchart D.toPre.P.L (D.toPre.famφB α) jf) (f.f jf) =
          κ r * valR (p ≫ φ) (LB.wchart D₀.P.L (D₀.famφB α₀) j₀) (s₀.f j₀))
    (jM : D.toPre.P.L.ι) (jf jt : Fin 4 → D.toPre.P.L.ι) (k : Fin 4 → D₀.P.L.ι)
    (hj : FormalValue.CohCharts g α jM jf jt)
    (cg : ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀) k) :
    valR (A := S) g.b.left _ (w.s (fun _ => k 2, jM)).val ^ j *
        (FormalValue.famVal g f jf * FormalValue.coordVal g α jt) =
      κ r * ρ (valR (A := S₀) g₀.b.left (LB.wchart D₀.P.L (D₀.famφB α₀) ![k 2, k 0, k 1, k 3])
        (s₀.f ![k 2, k 0, k 1, k 3]) *
        valR (A := S₀) (𝟙 _) (LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀) k) ((g₀.s α₀).s k).val) := by
  have hφ : ∀ i, FormalValue.coordφ g α i ≫ φ =
      spMap ρ ≫ (show Sp S₀ ⟶ _ from Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀ i) := hg.1
  have hq : ∀ i, FormalValue.basePt g ≫ D.toPre.famφB α i = FormalValue.coordφ g α (![2, 0, 1, 3] i) :=
    comp_famφB D.toPre g.b α
  have hq₀ := comp_famφB D₀ g₀.b α₀
  have ejf : ∀ i, jf i = jt (![2, 0, 1, 3] i) := fun i => hj.2.2 (.inr (.inl i)) (.inr (.inr _)) (hq i)
  have ejM : jM = jt 2 := hj.2.2 (.inl PUnit.unit) (.inr (.inr 2)) rfl
  have hk : ∀ i, ⊤ ≤ (show Sp S₀ ⟶ _ from Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀ i) ⁻¹ᵁ D₀.P.L.U (k i) :=
    fun i => cg.trans (LB.wchart_le _ _ _ i)
  have ek : ![k 2, k 0, k 1, k 3] = fun i => k (![2, 0, 1, 3] i) := by
    funext i; fin_cases i <;> rfl
  rw [ek]
  subst ejM
  obtain rfl : jf = fun i => jt (![2, 0, 1, 3] i) := funext ejf
  have hd : ∀ i, ⊤ ≤ FormalValue.coordφ g α i ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => k i, jt i) :=
    fun i => le_div _ (hφ i ▸ FormalValue.top_le_comp (hk i) _) (hj.2.1.trans (LB.wchart_le _ _ _ i))
  obtain ⟨t, ht, e₁⟩ := hf (FormalValue.basePt g) (fun i => jt (![2, 0, 1, 3] i)) (fun i => k (![2, 0, 1, 3] i))
    (Over.w g.b) (fun i => by rw [hq i]; exact hd _)
  simp only [hq] at ht
  have cf : ⊤ ≤ (show Sp S₀ ⟶ _ from g₀.b.left) ⁻¹ᵁ D₀.P.L.wchart (D₀.famφB α₀) (fun i => k (![2, 0, 1, 3] i)) :=
    fun z hz => Set.mem_iInter.2 fun i =>
      (congrArg (fun q => q z ∈ D₀.P.L.U (k (![2, 0, 1, 3] i))) (hq₀ i)).mpr (hk _ hz)
  have e₂ : valR (FormalValue.basePt g ≫ φ) _ (s₀.f fun i => k (![2, 0, 1, 3] i)) = _ :=
    (congrArg (fun q => valR q _ (s₀.f fun i => k (![2, 0, 1, 3] i))) (hφ 2)).trans
      (FormalValue.valR_spMap ρ (show Sp S₀ ⟶ _ from g₀.b.left) _ cf _)
  have e₃ : FormalValue.coordVal g α jt = _ := (hg.2 jt k hd).trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun i _ => valR_zpow _ _ (hd i) _ (![t 1, t 2, t 0, t 3] i)
      (by fin_cases i; exacts [ht 1, ht 2, ht 0, ht 3]) _)
    (valR_pullGen ρ (g₀.s α₀) k cg))
  have e₅ : (t 0 : S) ^ j * ∏ i, ((![t 1, t 2, t 0, t 3] i ^ (-Out.DegPre.gtε i) : Sˣ) : S) =
      ((∏ i, t i ^ Out.DegPre.famε j i : Sˣ) : S) := by
    rw [← Units.coe_prod, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← prod_factors t j]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  replace e₁ := e₁.trans (congrArg (κ r * ·) e₂)
  refine (congrArg₂ (fun a b => a ^ j * (_ * b)) (ht 0).symm e₃).trans ?_
  rw [← e₅] at e₁
  rw [map_mul, ← _root_.mul_assoc (κ r)]
  refine Eq.trans ?_ (congrArg (· * _) e₁)
  exact (congrArg (_ * ·) (_root_.mul_left_comm _ _ _)).trans
    ((_root_.mul_assoc _ _ _).symm.trans (_root_.mul_assoc _ _ _).symm)

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (j : ℕ) (x : a.D₀.X) (s₀ : a.D₀.SecB j x) (f : W.P.D.toPre.SecB j (W.e x)) (r : ℂ⟦X⟧) (jM : W.P.D.toPre.P.L.ι) (jf jt : Fin 4 → W.P.D.toPre.P.L.ι) (jt₀ : Fin 4 → a.D₀.P.L.ι), TanRel W ν g₁ → IsConstMul W j x s₀ f r → FormalValue.CohCharts g₁ (W.e x) jM jf jt → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀ → valR (A := DualNumber ℂ⟦X⟧) g₁.b.left _ (W.w.s (fun _ => jt₀ 2, jM)).val ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e x) jt) = TrivSqZeroExt.inl r * constEps (valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB x) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀) ((ν.s x).s jt₀).val) := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W ν g₁ j x s₀ f r jM jf jt jt₀ hg hf hj hc
  have := isLocalRing_dual ℂ⟦X⟧
  exact core (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) constEps W.w g₁ ν (hg x) s₀ f r (fun p => hf _ p _) jM jf jt jt₀
    hj hc

end GlobalTheory.ConstTanAlg
