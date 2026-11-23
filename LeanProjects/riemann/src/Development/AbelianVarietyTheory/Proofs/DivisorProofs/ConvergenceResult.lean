import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNormEqDrViaPower

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
open scoped TensorProduct NNReal

namespace GlobalTheory.HalfGeo

attribute [local instance] Over.cartesianMonoidalCategory

theorem map_minorAt {K L : Type} [CommRing K] [CommRing L] (f : K →+* L) {n g : ℕ} (M : Matrix (Fin n) (Fin g) K)
    (k : ℕ) (hk : k ≤ g) (σ : Fin k → Fin n) : f (minorAt M k hk σ) = minorAt (M.map f) k hk σ := by
  unfold minorAt
  rw [RingHom.map_det]
  rfl

theorem comp_mulVec {K L : Type} [CommRing K] [CommRing L] (f : K →+* L) {n g : ℕ} (M : Matrix (Fin n) (Fin g) K)
    (u : Fin g → K) : f ∘ M.mulVec u = (M.map f).mulVec (f ∘ u) := by
  funext r
  exact RingHom.map_mulVec f M u r

theorem convSt : ConvSt := by
  intro F _ _ v ε _ g J ν M M' hν h
  obtain ⟨h1, h2, h3, h4⟩ := h
  set io := ioOf (resP v) ε with hio
  set c := -Real.log (ε.w ((resP v : ℕ) : AlgebraicClosure F)) / Real.log (resP v) with hc_def
  have hw : ∀ z, ε.w z = ‖io z‖ ^ c := GlobalTheory.CovHt.Link.w_eq_norm_ioOf_rpow (resP v) v (residueCharacteristic_mem v) ε
  have hq := (Fact.out : (resP v).Prime)
  have hw1 : ε.w ((resP v : ℕ) : AlgebraicClosure F) < 1 := by
    have e1 : ((resP v : ℕ) : AlgebraicClosure F) =
        algebraMap F _ (algebraMap (𝓞 F) F ((resP v : ℕ) : 𝓞 F)) := by simp
    rw [e1, ε.w_alg]
    exact (v.adicAbv_coe_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 (residueCharacteristic_mem v)
  have hw0 : 0 < ε.w ((resP v : ℕ) : AlgebraicClosure F) := ε.w.pos (Nat.cast_ne_zero.2 hq.ne_zero)
  have hlp : 0 < Real.log (resP v) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hc : 0 < c := div_pos (neg_pos.2 (Real.log_neg hw0 hw1)) hlp
  have hexp : ∀ k, Real.exp (c * Real.log (ν k)) = ν k ^ c := fun k => by
    rw [Real.rpow_def_of_pos (hν k), mul_comm]
  have hle1 : ∀ z, ε.w z ≤ 1 ↔ ‖io z‖ ≤ 1 := fun z => by
    have e := Real.rpow_le_rpow_iff (x := ‖io z‖) (y := 1) (norm_nonneg _) zero_le_one hc
    rw [Real.one_rpow] at e
    rw [hw]
    exact e
  have hlt1 : ∀ z, ε.w z < 1 ↔ ‖io z‖ < 1 := fun z => by
    have e := Real.rpow_lt_rpow_iff (x := ‖io z‖) (y := 1) (norm_nonneg _) zero_le_one hc
    rw [Real.one_rpow] at e
    rw [hw]
    exact e
  have hJ : (J.map (Int.castRingHom (AlgebraicClosure F))).map io = J.map (Int.castRingHom ℂ_[resP v]) := by
    ext i j
    simp
  have hball : ∀ u : Fin g → AlgebraicClosure F, (∀ r, ε.w (M.mulVec u r) ≤ 1) →
      ∀ r, ‖(M.map io).mulVec (io ∘ u) r‖ ≤ 1 := fun u hu r => by
    rw [← RingHom.map_mulVec]
    exact (hle1 _).1 (hu r)
  refine ⟨fun k hk σ => ?_, fun k hk => ?_, fun u u' hu hu' => ?_, fun u hu r => ?_⟩
  · beta_reduce
    rw [hexp, hw, map_minorAt]
    exact Real.rpow_le_rpow (norm_nonneg _) (h1 k hk σ) hc.le
  · obtain ⟨σ, hσ⟩ := h2 k hk
    refine ⟨σ, ?_⟩
    beta_reduce
    rw [hexp, hw, map_minorAt]
    exact congrArg (· ^ c) hσ
  · beta_reduce
    rw [hlt1, RingHom.map_dotProduct, comp_mulVec, comp_mulVec, comp_mulVec, hJ]
    exact h3 _ _ (hball u hu) (hball u' hu')
  · beta_reduce
    rw [hlt1, map_sub, RingHom.map_mulVec, RingHom.map_mulVec]
    exact h4 _ (hball u hu) r

end GlobalTheory.HalfGeo
