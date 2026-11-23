import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardChartsFormalTowerOfVeryAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerCechH1UniformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftSectionsOneLevelStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

theorem exists_lift_sections_tower : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (L : ∀ e, LB (Y e).left) (u : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))), (∀ e, (L e).IsLB ∧ (u e).IsGen) → LBIso (L 0) (GlobalTheory.AbLaw.pw H₀ k) → ∀ σ₀ : LB.Sec (L 0), ∃ σ : ∀ e, LB.Sec (L e), σ 0 = σ₀ ∧ ∀ e, Rel (β e) (u e) (σ (e + 1)) (σ e) := by
  intro R _ _ I Y β hY H₀ n s₀ hH hva
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_standard_charts_formalTower_of_veryAmple R I Y β hY H₀ n s₀ hH hva
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.thickening_tower_cech_h1_uniform R I Y β hY n C
  refine ⟨k₀, fun k hk L u hL hL0 σ₀ => ?_⟩
  let γ : ∀ e, (Y 0).left ⟶ (Y e).left := fun e =>
    Nat.rec (motive := fun e => (Y 0).left ⟶ (Y e).left) (𝟙 _) (fun e g => g ≫ β e) e
  have hγs : ∀ e, γ e ≫ β e = γ (e + 1) := fun e => rfl
  have hP : (GlobalTheory.AbLaw.pw H₀ k).IsLB := isLB_pw hH _
  have hiso : ∀ e, LBIso ((L e).pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) := by
    intro e
    induction e with
    | zero => exact LBIso.chartPull (chartPullPull (L 0) (𝟙 _)) (chartPullId _) hL0
    | succ e ih =>
      refine LBIso.trans (pull_isLB (hL (e + 1)).1 _) (pull_isLB (hL e).1 _) hP ?_ ih
      exact LBIso.chartPull (chartPullSame (L (e + 1)) (fun _ => γ (e + 1)) (fun _ => β e) (fun _ => 1) (γ e)
        (fun _ => rfl)) (chartPullPull (L e) (γ e)) (LBIso.symm ⟨u e, (hL e).2⟩)
  have step : ∀ e (σ : LB.Sec (L e)), ∃ σ' : LB.Sec (L (e + 1)), Rel (β e) (u e) σ' σ := fun e σ =>
    GlobalTheory.T.thickeningTower_lift_sections_one_level R I Y β hY n C H₀ s₀ hH hC γ rfl hγs e k (hk₀ k hk (e + 1)) (L e) (L (e + 1)) (u e)
      (hL e).1 (hL (e + 1)).1 (hL e).2 (hiso (e + 1)) σ
  choose f hf using step
  let σ : ∀ e, LB.Sec (L e) := fun e => Nat.rec (motive := fun e => LB.Sec (L e)) σ₀ (fun e s => f e s) e
  exact ⟨σ, rfl, fun e => hf e (σ e)⟩

end GlobalTheory.FormalAlg
