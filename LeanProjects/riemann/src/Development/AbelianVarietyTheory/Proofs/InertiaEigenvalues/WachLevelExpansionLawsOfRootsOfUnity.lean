import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfConstantCoeffZero

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.Expansion

open PowerSeries GlobalTheory.HWL.Ser

section Generic

variable {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L] [Algebra ℤ_[l] O]
  [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] {v : AddValuation L (WithTop ℚ)}
  {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR}
    [Algebra Qp L] [TopologicalSpace L] {n : ℕ}

noncomputable def evOne (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
  (W.lev i ζ).comp (Pi.constAlgHom O (ZMod n) O⟦X⟧)

omit [CharZero L] [Algebra ℚ L] in

theorem lev_eq (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) (a : LetA O n) :
    W.lev i ζ a = evOne W i ζ (a i) := by
  have h := W.lev_letter i ζ (a - fun _ => a i) (by simp)
  rw [map_sub, sub_eq_zero] at h
  exact h

theorem evOne_X (W : LocWach PD L O v n) (i : ZMod n) {ζ : L} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    evOne W i ζ X = C ζ * exp L - 1 := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π i ζ h
  have hE : E = exp L := ode_unique 1 (by rw [h1, map_one, one_mul])
    (by rw [derivative_exp, map_one, one_mul]) (by rw [h0, constantCoeff_exp])
  rw [← hE, ← h2, lev_eq, add_sub_cancel_left]
  rfl

theorem levLaws_of_evLaw (W : LocWach PD L O v n) (hp : PD.p = l) (c : W.Gam → ℤ_[l])
    (hc : ∀ g, algebraMap ℤ_[l] O (c g) = (W.χΓ g : O)) (hφ : W.φ₀ = GlobalTheory.Cyc.phi l O)
    (hγ : ∀ g, W.γ₀ g = GlobalTheory.Cyc.act l O (c g))
    (hv : ∀ (c : ℤ_[l]) (j a : ℕ), (j : WithTop ℚ) ≤ v (algebraMap ℤ_[l] L c - (a : L)) →
      (l : ℤ_[l]) ^ j ∣ c - a) (H : EvLaw l (O := O) v inferInstance) : LevLaws W := by
  have hc' : ∀ g, algebraMap O L (W.χΓ g : O) = algebraMap ℤ_[l] L (c g) :=
    fun g => by rw [← hc, ← IsScalarTower.algebraMap_apply]
  have hpr : PD.p.Prime := hp ▸ (Fact.out : l.Prime)
  constructor
  · rintro g i ζ _ j a h hj rfl f
    rw [hc'] at hj ⊢
    have e : W.γA g f i = GlobalTheory.Fon.gam O (c g) (f i) := by
      rw [← GlobalTheory.Cyc.Series.act_eq, ← hγ]; rfl
    rw [lev_eq, lev_eq, e]
    exact ev_gam H (hp ▸ h.pow_eq_one) _ (hv _ j a hj) (evOne_X W i ⟨j, h⟩)
      (evOne_X W i (root_pow hpr ⟨j, h⟩ a)) (f i)
  · rintro i ζ ⟨j, h⟩ f
    have e : W.φA f i = GlobalTheory.Fon.gam O (l : ℤ_[l]) (f (i - 1)) := by
      rw [← GlobalTheory.Cyc.Series.act_eq, ← GlobalTheory.Cyc.phi, ← hφ]; rfl
    have := ev_gam H (j := j) (hp ▸ h.pow_eq_one) (l : ℤ_[l]) (a := l) (by simp) (evOne_X W i ⟨j, h⟩)
      (evOne_X W (i - 1) (root_pow hpr ⟨j, h⟩ l)) (f (i - 1))
    rw [map_natCast] at this
    rw [lev_eq, lev_eq, e, hp]
    exact this

end Generic

theorem levLaws : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; LevLaws W := by
  intro D HW l _ K s LL h W
  obtain ⟨χ, h1⟩ := exists_padic_char (LL := LL) (gamOf W ((HW l).W_s K s LL h))
  obtain ⟨_, hcomp, -, hu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hl : (l : ↥(OL LL)) ≠ 0 := fun h0 => by
    have h2 := congrArg (algebraMap ↥(OL LL) ↥LL.1) h0
    rw [map_natCast, map_zero] at h2
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2
  have key := fun g : W.Gam => GlobalTheory.Cyc.act_unique l ↥(OL LL) hl hu (W.γ₀ g) W.φ₀ (χ g : ℤ_[l])
    (by rw [W.φ₀_X, W.q₀_def, (D.loc l).PD_p K]) (W.γ₀_comm g) (W.γ₀_X g).1 ((W.γ₀_X g).2.trans (h1 g).symm)
  refine levLaws_of_evLaw W ((D.loc l).PD_p K) (fun g => χ g) h1 (key 1).1 (fun g => (key g).2) (dvd_of_le_v (D.loc l)) ?_
  convert evLaw_integers (D.loc l) LL using 1
  exact Algebra.algebra_ext _ _ fun r => PowerSeries.algebraMap_apply

end GlobalTheory.NL.Expansion
