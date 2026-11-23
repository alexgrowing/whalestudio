import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedLogMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClosedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupremumTwistingOpensEqTopStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem dpow_mem_pdP {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (n : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow n x ∈ pdP δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

theorem dividedPowerFiltration_anti {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {r r' : ℕ} (h : r ≤ r') :
    pdP δ r' ≤ pdP δ r :=
  Ideal.span_le.2 fun _ ⟨l, hl, hr, hz⟩ => Ideal.subset_span ⟨l, hl, h.trans hr, hz⟩

theorem plogK_congr {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {s s' : ℕ} (h : s ≤ s')
    (hs : pdP δ s = ⊥) {x : B} (hx : x ∈ J) : plogK δ s x = plogK δ s' x := by
  unfold plogK
  refine Finset.sum_subset (Finset.range_mono h) fun k _ hk => ?_
  have hk' : s ≤ k + 1 := by simp at hk; omega
  have hm : δ.dpow (k + 1) x ∈ pdP δ s := dividedPowerFiltration_anti δ hk' (dpow_mem_pdP δ _ hx)
  rw [hs, Ideal.mem_bot] at hm
  rw [hm, mul_zero]

theorem plogK_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) {x : B} (hx : x ∈ J) :
    plogK δ s x ∈ J :=
  Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (δ.dpow_mem (Nat.succ_ne_zero k) hx)

section K
variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem r_sub_one_mem {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D)
    (σ : ComposableArrows C 2) : ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1) ∈ (g.obj (σ.obj (Fin.last 2))).J := GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ

theorem zK_cocycle {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D)
    (s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥) : CH.d _ 2 (zK Λ s) = 0 := GlobalTheory.T.cone_cocycle_closed Λ s hs

theorem zK_cls_eq {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ Λ' : CLiftK g D)
    (s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥) (hz : CH.d _ 2 (zK Λ s) = 0) (hz' : CH.d _ 2 (zK Λ' s) = 0) :
    (CH.cx _).cls (zK Λ s) hz = (CH.cx _).cls (zK Λ' s) hz' := GlobalTheory.T.cone_cocycle_class_independent Λ Λ' s hs hz hz'

omit [CharZero K] in

theorem zK_precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}
    (Λ : CLiftK g D) (h : C' ⥤ C) (s : ℕ) :
    zK (Λ.precomp h) s = (CH.Mor.restrict (g ⋙ O (smFun X q)) h).pullC 2 (zK Λ s) := by
  funext σ
  rfl

end K

theorem lift_exists {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X)
    (s : ℕ) : Nonempty (CLiftK (KS q s (𝒱D D)).ι D) := GlobalTheory.T.exists_cone_lift q D s

theorem sSup_𝒱D {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ)
    (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N) (h : IsTautologicalLineAt D N i) : sSup (𝒱D D) = ⊤ := GlobalTheory.T.supremum_twisting_opens_eq_top D N i h

end CrystallineSemistableComparison.Pb
