import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceFinitelyManyCellsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistCombinationSplitsSinglePlaceVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteLocalSupportExchangeDataTwistPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlacesGroupEqProductLocalGroupsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QFinSupp

theorem locK_congr {D : D7} {c : Comm D} {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle} (Q : QAt v χ) (j d d' : ℕ) (e : d = d')
    (h1 : j + d = Q.s + 1) (h2 : j + d' = Q.s + 1) :
    (Q.T.lev j d h1).J.map (Q.gl j d h1) = (Q.T.lev j d' h2).J.map (Q.gl j d' h2) := by
  subst e; rfl

theorem cells_at : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ (w.eQ j) Ψ₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  intro D c v t w F hc ht hv hW hF j σ h i a
  obtain ⟨T, hT⟩ := GlobalTheory.T.seeSaw_twistPlace_finitely_many_cells D c v t w F hc ht hv hW hF j σ h i a
  refine ⟨T, fun Ψ₁ hΨ g hg h₁ hh x hne => ?_⟩
  obtain ⟨f₁, hf₁, e⟩ := GlobalTheory.T.twistCombination_splits_singlePlace_vacuum D c v t w F hc hv hF j (by omega) i Ψ₁ hΨ
  rw [e] at hne
  exact hT f₁ hf₁ g hg h₁ hh x hne

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ T₁ : Finset (GA D (c.V (j + 1))), (∀ q ∈ T₁, q ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∀ α, ∀ g ∈ (w.ε j α).support, ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), flatBF (t.sBF j (σ + 1) h) (t.om j (g, x) (comb c.ψ _ _ (w.eQ j) Ψ₁)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧ ∃ q ∈ T₁, ∃ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, x = r * q * k := by
  intro D c v t w F hc ht hv hW hF j σ h
  classical
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_finite_local_support_exchangeData_twistPlaces D c v t w F hF j σ h
  choose T hT using fun i a => cells_at D c v t w F hc ht hv hW hF j σ h i a
  obtain ⟨P, hPH, hPat, hPdec⟩ := GlobalTheory.T.twistPlaces_group_eq_product_local_groups D c v t w F hF j σ h
  refine ⟨(Fintype.piFinset fun i => (A i).biUnion (T i)).image P, ?_, ?_⟩
  · intro q hq
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hq
    exact hPat y
  · intro Ψ₁ hΨ α g hg x hx hne
    obtain ⟨a, ha⟩ := hA α g hg
    obtain ⟨y, rfl, hy⟩ := hPdec x hx
    have key := fun i => hT i (a i) Ψ₁ hΨ _ (ha i).2 _ (hy i) (y i) (by simpa only [inv_mul_cancel_right] using hne)
    choose τ hτ r hr κ hκ hyeq using key
    have hyy : y = r * τ * κ := funext hyeq
    refine ⟨P r, hPH _ r hr, hPat r, P τ, Finset.mem_image.2 ⟨τ, Fintype.mem_piFinset.2 fun i =>
      Finset.mem_biUnion.2 ⟨a i, (ha i).1, hτ i⟩, rfl⟩, P κ, hPH _ κ fun i => ?_, by rw [hyy, map_mul, map_mul]⟩
    refine Subgroup.mem_iSup_of_mem i ?_
    rw [GlobalTheory.QuotientFiniteLevel.locK, locK_congr (F.Q i) (j + 1) _ (2 * σ + 2) (by have := (F.Q i).hs; omega) _ (by have := (F.Q i).hs; omega)]
    exact Subgroup.mem_map_of_mem _ (hκ i)

end GlobalTheory.QFinSupp
