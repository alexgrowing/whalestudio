import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoCrossPowersOfPullbackPowersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfCompatibleAdicReductionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem cross_cancel {G : Type} [CommGroup G] (a a' g : G) (p q : ℤ) :
    (a' * g ^ q) ^ p * ((a * g ^ p) ^ q)⁻¹ = a' ^ p * (a ^ q)⁻¹ := by
  rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm q p]
  group

theorem lbIso_pw_cross : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB) → ∀ (p q : ℤ) (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ (w : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) p) (A.pull (b e))) (w' : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) q) (A'.pull (b e))), (∀ e, (w e).IsGen ∧ (w' e).IsGen) → (∀ e z k l' l, b e z ∈ A.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ p) → (∀ e z k l' l, b e z ∈ A'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w' e) (𝟙 _) z k l = Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ q) → LBIso (GlobalTheory.AbLaw.pw A q) (GlobalTheory.AbLaw.pw A' p) := by
  intro R _ _ I hI X hX Y β b hb hβ N v hN p q A A' hA hA' w w' hg hv hv'
  choose c hc hcg using fun e =>
    GlobalTheory.T.exists_iso_cross_powers_of_pullback_powers X.left (Y e).left (b e) A A' (N e) p q (w e) (w' e) hA hA' (hN e) (hg e).1 (hg e).2
  refine GlobalTheory.T.lineBundleIso_of_compatible_adic_reductions R I hI X hX Y β b hb hβ (pw A q) (pw A' p) (isLB_pw hA q) (isLB_pw hA' p) c hc ?_
  intro e z k k' hk hk'
  obtain ⟨l, hl⟩ := exists_chart (hN e) z
  obtain ⟨l', hl'⟩ := exists_chart (hN (e + 1)) (β e z)
  have hz : b (e + 1) (β e z) = b e z := by
    rw [← Scheme.Hom.comp_apply, hβ e]
  have h1 := hcg (e + 1) (Y e).left (β e) z k k' l' (hz ▸ hk) (hz ▸ hk') hl'
  have h0 := hcg e (Y e).left (𝟙 _) z k k' l hk hk' hl
  rw [h1, h0, hv e z k l' l hk hl' hl, hv' e z k' l' l hk' hl' hl]
  exact (cross_cancel _ _ _ p q).symm

end GlobalTheory.FormalAlg
