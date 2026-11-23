import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetZ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLogG
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPowDivFactorialLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OnePlacePairs

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem expS_zero {κ : Type} : product_zeroth_first_parts.expS ℂ_[p] (0 : MvPowerSeries κ ℂ_[p]) = 1 := by
  have h := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (k := ℂ_[p]) (a := (0 : MvPowerSeries κ ℂ_[p])) (b := 0)
    (by simp) (by simp)
  rw [add_zero] at h
  have hu : IsUnit (PowerSeries.subst (0 : MvPowerSeries κ ℂ_[p]) (PowerSeries.exp ℂ_[p])) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_exp (by simp)]
    exact isUnit_one
  unfold product_zeroth_first_parts.expS
  exact hu.mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem expS_add {κ : Type} {f g : MvPowerSeries κ ℂ_[p]} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    product_zeroth_first_parts.expS ℂ_[p] (f + g) = product_zeroth_first_parts.expS ℂ_[p] f * product_zeroth_first_parts.expS ℂ_[p] g :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg

theorem expS_sum {κ ι : Type} (s : Finset ι) (f : ι → MvPowerSeries κ ℂ_[p]) (hf : ∀ i, constantCoeff (f i) = 0) :
    product_zeroth_first_parts.expS ℂ_[p] (∑ i ∈ s, f i) = ∏ i ∈ s, product_zeroth_first_parts.expS ℂ_[p] (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [expS_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, expS_add (hf i) (by rw [map_sum]; exact Finset.sum_eq_zero fun j _ => hf j), ih]

theorem padicExpSeries_doubleSum {κ α β : Type} [Fintype α] [Fintype β] (f : α → β → MvPowerSeries κ ℂ_[p])
    (hf : ∀ a b, constantCoeff (f a b) = 0) :
    product_zeroth_first_parts.expS ℂ_[p] (∑ a, ∑ b, f a b) = ∏ a, ∏ b, product_zeroth_first_parts.expS ℂ_[p] (f a b) := by
  rw [expS_sum _ _ (fun a => by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hf a b)]
  exact Finset.prod_congr rfl fun a _ => expS_sum _ _ (hf a)

theorem cc_logF : PowerSeries.constantCoeff (Formalism.MainNotions.GL3Theta.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.MainNotions.GL3Theta.logF, PowerSeries.coeff_mk]
  simp

theorem cc_plog {κ : Type} {u : MvPowerSeries κ ℂ_[p]} (hu : constantCoeff u = 0) :
    constantCoeff (PowerSeries.subst u (Formalism.MainNotions.GL3Theta.logF p)) = 0 := by
  rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hu, cc_logF]

theorem constantCoeff_bivariateSeriesSubstPair {κ : Type} {b0 : MvPowerSeries (Fin 2) ℂ_[p]} (hb0 : constantCoeff b0 = 0)
    {u v : MvPowerSeries κ ℂ_[p]} (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) :
    constantCoeff (GlobalTheory.ThBe0.at2 b0 u v) = 0 := by
  have h : ∀ i : Fin 2, constantCoeff (if i = 0 then u else v) = 0 := fun i => by split_ifs <;> assumption
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h hb0

theorem subst_powerSeriesEvalTwoGroups {κ κ' : Type} {φ : κ → MvPowerSeries κ' ℂ_[p]} (hφ : HasSubst φ) (b0 : MvPowerSeries (Fin 2) ℂ_[p])
    {u v : MvPowerSeries κ ℂ_[p]} (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) :
    subst φ (GlobalTheory.ThBe0.at2 b0 u v) = GlobalTheory.ThBe0.at2 b0 (subst φ u) (subst φ v) := by
  have h : ∀ i : Fin 2, constantCoeff (if i = 0 then u else v) = 0 := fun i => by split_ifs <;> assumption
  unfold GlobalTheory.ThBe0.at2
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h) hφ]
  congr 1
  funext i
  split_ifs <;> rfl

variable {n' : ℕ} [NeZero n']

theorem hasSubst_pair {r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) :
    HasSubst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem cc_jet {r0 r1 : ℕ} (v : ZMod n' × Fin r0 × Fin r1) : constantCoeff (jetLogG p n' v) = 0 := by
  rw [← GlobalTheory.BiextInhab.bridge p n' v.2 v.1]
  exact GlobalTheory.BeProps.constantCoeff_laAt _ _

theorem hasSubst_jet' {r0 r1 : ℕ} : HasSubst (jetLogG p n' (β := Fin r0 × Fin r1)) :=
  hasSubst_of_constantCoeff_zero cc_jet

theorem pair_eq {r0 r1 : ℕ} (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p])
    (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) (V : MvPowerSeries (ZMod n') ℂ_[p])
    (hb0 : constantCoeff b0 = 0) (hbv : constantCoeff bv = 0) (hx : ∀ r, constantCoeff (x r) = 0)
    (H : product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
      (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(subst (GlobalTheory.ThStr.laS p n') bv)))
    (a : Fin r0) (b : Fin r1) :
    product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0
                               (PowerSeries.subst (xiE x (Sum.inl ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p))
                               (PowerSeries.subst (xiE x (Sum.inr ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p)))) =
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V *
        product_zeroth_first_parts.expS ℂ_[p] (-(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv)) := by
  have hψ := hasSubst_pair (p := p) (n' := n') a b
  have hcL : constantCoeff (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
      (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = 0 := by
    rw [map_neg, map_sum, Finset.sum_eq_zero fun r _ => constantCoeff_bivariateSeriesSubstPair hb0 (cc_plog (hx _)) (cc_plog (hx _)), neg_zero]
  have hLa : HasSubst (GlobalTheory.ThStr.laS p n') := hasSubst_of_constantCoeff_zero GlobalTheory.BeProps.constantCoeff_laS
  have hcR : constantCoeff (-(subst (GlobalTheory.ThStr.laS p n') bv)) = 0 := by
    rw [map_neg, constantCoeff_subst_eq_zero hLa GlobalTheory.BeProps.constantCoeff_laS hbv, neg_zero]
  have e1 : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
      (product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p))))) =
      product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0
        (PowerSeries.subst (xiE x (Sum.inl ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (xiE x (Sum.inr ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p)))) := by
    rw [product_zeroth_first_parts.expS, product_zeroth_first_parts.expS, GlobalTheory.BeProps.subst_psubst hψ hcL, ← substAlgHom_apply hψ, map_neg, map_sum]
    congr 2
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [substAlgHom_apply, subst_powerSeriesEvalTwoGroups hψ b0 (cc_plog (hx _)) (cc_plog (hx _)),
      GlobalTheory.BeProps.subst_psubst hψ (hx _), GlobalTheory.BeProps.subst_psubst hψ (hx _)]
    rfl
  have e2 : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
      (V * product_zeroth_first_parts.expS ℂ_[p] (-(subst (GlobalTheory.ThStr.laS p n') bv))) =
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V *
        product_zeroth_first_parts.expS ℂ_[p] (-(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv)) := by
    have hn : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
        (-(subst (GlobalTheory.ThStr.laS p n') bv)) = -(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv) := by
      rw [← substAlgHom_apply hψ, map_neg, substAlgHom_apply, subst_comp_subst_apply hLa hψ]
      congr 2
      funext s
      exact GlobalTheory.BiextInhab.bridge p n' (a, b) s
    rw [product_zeroth_first_parts.expS, product_zeroth_first_parts.expS, ← substAlgHom_apply hψ, map_mul]
    simp only [substAlgHom_apply]
    rw [GlobalTheory.BeProps.subst_psubst hψ hcR, hn]
  rw [← e1, ← e2, H]

theorem integralW_pair {r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) {V : MvPowerSeries (ZMod n') ℂ_[p]}
    (hV : Formalism.MainNotions.GL3Theta.IntegralW V) :
    Formalism.MainNotions.GL3Theta.IntegralW (subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V) := by
  let e : ZMod n' ↪ ZMod n' × Fin r0 × Fin r1 := ⟨fun s => (s, a, b), fun x y h => (Prod.mk.inj h).1⟩
  have he : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V =
      rename e V := by
    rw [rename_eq_subst]; rfl
  rw [he]
  intro m
  by_cases hm : m ∈ Set.range (Finsupp.mapDomain (e : ZMod n' → ZMod n' × Fin r0 × Fin r1))
  · obtain ⟨n, rfl⟩ := hm
    rw [← Finsupp.embDomain_eq_mapDomain, coeff_embDomain_rename]
    exact hV n
  · rw [coeff_rename_eq_zero _ _ hm]
    exact zero_mem _

theorem cc_xiE {r0 r1 : ℕ} {x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]}
    (hx : ∀ r, constantCoeff (x r) = 0) (e : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : constantCoeff (xiE x e) = 0 := by
  rcases e with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · exact constantCoeff_subst_eq_zero (hasSubst_pair a b) (fun _ => constantCoeff_X _) (hx _)
  · exact constantCoeff_subst_eq_zero (hasSubst_pair a b) (fun _ => constantCoeff_X _) (hx _)

theorem sum_reorder {r0 r1 : ℕ} {M : Type*} [AddCommMonoid M] (f : Eidx n' r0 r1 → M) :
    ∑ e, f e = ∑ a : Fin r0, ∑ b : Fin r1, ∑ r : Fin (n' / 2), f (r, a, b) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]

theorem neg_doubleSum_eq_doubleSum_neg {α β M : Type*} [Fintype α] [Fintype β] [AddCommGroup M] (g : α → β → M) :
    -(∑ a, ∑ b, g a b) = ∑ a, ∑ b, -g a b := by
  simp [Finset.sum_neg_distrib]

theorem rhs_eq {r0 r1 : ℕ} (bv : MvPowerSeries (ZMod n') ℂ_[p]) (hbv : constantCoeff bv = 0) :
    subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1,
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) =
      ∏ a : Fin r0, ∏ b : Fin r1, product_zeroth_first_parts.expS ℂ_[p] (-(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv)) := by
  have hJ := hasSubst_jet' (p := p) (n' := n') (r0 := r0) (r1 := r1)
  have hc : constantCoeff (-(∑ a : Fin r0, ∑ b : Fin r1,
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) = 0 := by
    rw [map_neg, map_sum, Finset.sum_eq_zero fun a _ => ?_, neg_zero]
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => constantCoeff_subst_eq_zero (hasSubst_pair a b) (fun _ => constantCoeff_X _) hbv
  have e : subst (jetLogG p n' (β := Fin r0 × Fin r1)) (-(∑ a : Fin r0, ∑ b : Fin r1,
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) =
      ∑ a : Fin r0, ∑ b : Fin r1, -(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv) := by
    rw [← substAlgHom_apply hJ, map_neg, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [substAlgHom_apply, subst_comp_subst_apply (hasSubst_pair a b) hJ]
    congr 2
    funext s
    rw [subst_X hJ]
  rw [neg_one_smul, product_zeroth_first_parts.expS, GlobalTheory.BeProps.subst_psubst hJ hc, e]
  exact padicExpSeries_doubleSum _ fun a b => by
    rw [map_neg, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun s => cc_jet _) (fun s => cc_jet _) hbv,
      neg_zero]

end GlobalTheory.OnePlacePairs

namespace GlobalTheory.OnePlacePairs

open MvPowerSeries

theorem pairs_all : ∀ {p : ℕ} [Fact p.Prime] {n' : ℕ} [NeZero n'] (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) (V : MvPowerSeries (ZMod n') ℂ_[p]), MvPowerSeries.constantCoeff b0 = 0 → MvPowerSeries.constantCoeff bv = 0 → (∀ r, MvPowerSeries.constantCoeff (x r) = 0) → Formalism.MainNotions.GL3Theta.IntegralW V → product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(MvPowerSeries.subst (GlobalTheory.ThStr.laS p n') bv)) → ∀ (r0 r1 : ℕ), ∃ U2 : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U2‖ ≤ 1) ∧ product_zeroth_first_parts.expS ℂ_[p] (-(∑ e : Eidx n' r0 r1, GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (xiE x (Sum.inl e)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (xiE x (Sum.inr e)) (Formalism.MainNotions.GL3Theta.logF p)))) = U2 * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  intro p _ n' _ b0 bv x V hb0 hbv hx hV H r0 r1
  refine ⟨∏ a : Fin r0, ∏ b : Fin r1,
    subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V, fun m => ?_, ?_⟩
  · have hmem : (∏ a : Fin r0, ∏ b : Fin r1,
        subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V) ∈
        GlobalTheory.BiextInhab.serW p (ZMod n' × Fin r0 × Fin r1) :=
      Subring.prod_mem _ fun a _ => Subring.prod_mem _ fun b _ => GlobalTheory.BiextInhab.mem_serW.2 (integralW_pair a b hV)
    exact GlobalTheory.BeProps.norm_le_one_of_mem_Wp (GlobalTheory.BiextInhab.mem_serW.1 hmem m)
  · rw [rhs_eq bv hbv, ← Finset.prod_mul_distrib]
    simp only [← Finset.prod_mul_distrib]
    rw [sum_reorder, neg_doubleSum_eq_doubleSum_neg, padicExpSeries_doubleSum _ fun a b => by
      rw [map_neg, map_sum, Finset.sum_eq_zero fun r _ => constantCoeff_bivariateSeriesSubstPair hb0 (cc_plog (cc_xiE hx _)) (cc_plog (cc_xiE hx _)),
        neg_zero]]
    exact Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => pair_eq b0 bv x V hb0 hbv hx H a b

end GlobalTheory.OnePlacePairs
