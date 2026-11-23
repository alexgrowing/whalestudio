import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMapStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemSpanBoxFamilyPowerDegDataStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem pow_eq_one_of_multilinear {F M N : Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] {j : ℕ} (bx : MultilinearMap F (fun _ : Fin j => M) N)
    (hspan : ∀ S : N, S ∈ Submodule.span F {S' | ∃ s, S' = bx s})
    (U : Fin j → Module.End F M) (W : Module.End F N)
    (hW : ∀ s, W (bx s) = bx (fun i => U i (s i)))
    (hU : ∀ i, ∃ m : ℕ, 1 ≤ m ∧ U i ^ m = 1) : ∃ m : ℕ, 1 ≤ m ∧ W ^ m = 1 := by
  classical
  choose m hm hU using hU
  have hp : ∀ (n : ℕ) s, (W ^ n) (bx s) = bx (fun i => (U i ^ n) (s i)) := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [pow_succ', Module.End.mul_apply, ih, hW]
      simp only [pow_succ', Module.End.mul_apply]
  refine ⟨∏ i, m i, Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => by
    have := hm i; omega), LinearMap.ext fun S => ?_⟩
  refine LinearMap.eqOn_span' (s := {S' | ∃ s, S' = bx s}) ?_ (hspan S)
  rintro _ ⟨s, rfl⟩
  rw [hp]
  have : ∀ i, U i ^ (∏ i, m i) = 1 := fun i => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    rw [hc, pow_mul, hU, one_pow]
  simp only [this, Module.End.one_apply]

theorem finOrd_box : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (p' : QkPt D'.toPre F k) (p : Fin j → QkPt D.toPre F k), IsBoxQk pD F k p' p → ∀ (w : ∀ i, LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F (p i).g.b) (DegPre.lineε k))) (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε k))), (∀ i, (w i).IsGen) → w'.IsGen → (∀ (s s₁ : Fin j → Fam D.toPre F k) (S S₁ : Fam D'.toPre F k), (∀ i, PhiRel D.toPre F k (p i) (w i) (s i) (s₁ i)) → IsBoxFam pD F k S s → IsBoxFam pD F k S₁ s₁ → PhiRel D'.toPre F k p' w' S S₁) → ∀ ζ : Fin j → F, (∀ i, FinOrd D F k (p i) (w i) (ζ i)) → FinOrd D' F k p' w' (∏ i, ζ i) := by
  intro hL hL2 hL4 hT V _ _ _ _ j D D' pD F _ _ k hk p' p _ w w' hw hw' hc ζ h
  have hG := hL.globalFns
  obtain ⟨bx, hbx⟩ := GlobalTheory.T.exists_boxFamily_multilinear_map hG V j D.toPre D'.toPre pD F k
  have hspan := GlobalTheory.T.mem_span_boxFamily_powerDegData hL hL2 hL4 hT V j D D' pD F k hk
  simp only [hbx] at hspan
  choose Φ hΦ using fun i => phiFun_of_globalFns hG V _ D F k hk (p i) (w i) (hw i)
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG V _ D' F k hk p' w' hw'
  refine (ThetaFinOrd.finOrd_iff p' w' _ Φ' hΦ').2 (pow_eq_one_of_multilinear bx hspan
    (fun i => ζ i • Φ i) _ (fun s => ?_)
    (fun i => (ThetaFinOrd.finOrd_iff (p i) (w i) _ (Φ i) (hΦ i)).1 (h i)))
  have e := (hΦ' _ _).1 (hc s (fun i => Φ i (s i)) _ _ (fun i => (hΦ i _ _).2 rfl)
    ((hbx _ _).2 rfl) ((hbx _ _).2 rfl))
  simp only [LinearMap.smul_apply]
  rw [← e, MultilinearMap.map_smul_univ]

end GlobalTheory
