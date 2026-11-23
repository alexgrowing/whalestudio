import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetZ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasSubstCoordZA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLogG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OnePlaceRead

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_psubst {K κ : Type} [CommRing K] {a : MvPowerSeries κ K} (ha : constantCoeff a = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) : constantCoeff (PowerSeries.subst a f) = 0 := by
  have h := GlobalTheory.BeProps.coeff_subst_range ha f 0
  simpa [hf] using h

theorem constantCoeff_padicLogSeries_unramified_eq_zero : PowerSeries.constantCoeff (FormalGroupSystem.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [FormalGroupSystem.logF]

theorem constantCoeff_logF_C : PowerSeries.constantCoeff (Formalism.MainNotions.GL3Theta.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Formalism.MainNotions.GL3Theta.logF]

theorem map_expS {ι : Type} {f : MvPowerSeries ι (FormalGroupSystem.K0 p)} (hf : constantCoeff f = 0) :
    MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (FormalGroupSystem.expS p f) =
      product_zeroth_first_parts.expS ℂ_[p] (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) f) := by
  have hf' : constantCoeff (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) f) = 0 := by
    simp [hf]
  ext n
  rw [coeff_map]
  unfold product_zeroth_first_parts.expS
  rw [GlobalTheory.BeProps.coeff_subst_range hf']
  have hd : (n.sum fun _ k => k) = n.degree := by
    simp [Finsupp.sum, Finsupp.degree_apply]
  rw [hd]
  change Formalism.L2.G.Pend.k0ToC p (∑ k ∈ Finset.range (n.degree + 1),
    ((k.factorial : FormalGroupSystem.K0 p))⁻¹ * MvPowerSeries.coeff n (f ^ k)) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_inv₀, map_natCast, PowerSeries.coeff_exp, ← map_pow, coeff_map]
  simp

theorem subst_bivariateSeries_difference_pair {τ : Type} {Eσ : Type} [Finite Eσ] (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p))
    {η : Eσ → MvPowerSeries τ ℂ_[p]} (hη : ∀ i, constantCoeff (η i) = 0) (i j : Eσ) :
    MvPowerSeries.subst η (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      (sub2 p be (MvPowerSeries.X i) (MvPowerSeries.X j))) =
      GlobalTheory.ThBe0.at2 (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be) (η i) (η j) := by
  have hs : HasSubst η := hasSubst_of_constantCoeff_zero hη
  have h2 : HasSubst (![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries Eσ (FormalGroupSystem.K0 p)) := by
    refine hasSubst_of_constantCoeff_zero fun s => ?_
    fin_cases s <;> simp
  have h2' : HasSubst (fun s => MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      ((![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries Eσ (FormalGroupSystem.K0 p)) s)) := by
    refine hasSubst_of_constantCoeff_zero fun s => ?_
    fin_cases s <;> simp
  unfold sub2 GlobalTheory.ThBe0.at2
  rw [map_subst h2, subst_comp_subst_apply h2' hs]
  congr 1
  funext s
  fin_cases s <;> simp [subst_X hs]

theorem read_thOne {n' r0 r1 : ℕ} {κ : Type} (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)) (hbe : BeProp p be)
    (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)) (J : Zidx n' r0 r1 → MvPowerSeries κ ℂ_[p])
    (ξ : Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → MvPowerSeries κ ℂ_[p])
    (hJ : ∀ z, MvPowerSeries.constantCoeff (J z) = 0) (hξ : ∀ i, MvPowerSeries.constantCoeff (ξ i) = 0)
    (h : ∀ i, MvPowerSeries.subst J (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 i)) =
      PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p)) :
    MvPowerSeries.subst J (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (thOne B be U)) =
      product_zeroth_first_parts.expS ℂ_[p] (-(∑ e : Eidx n' r0 r1, GlobalTheory.ThBe0.at2 (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be)
        (PowerSeries.subst (ξ (Sum.inl e)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (ξ (Sum.inr e)) (Formalism.MainNotions.GL3Theta.logF p)))) *
      MvPowerSeries.subst ξ (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inParam p U)) := by
  have hJs : HasSubst J := hasSubst_of_constantCoeff_zero hJ
  have hξs : HasSubst ξ := hasSubst_of_constantCoeff_zero hξ
  have ha := hasSubst_coordZ (r0 := r0) (r1 := r1) B
  have ha0 : ∀ i, constantCoeff (coordZ B (FormalGroupSystem.K0 p) 1 i : MvPowerSeries (Zidx n' r0 r1) (FormalGroupSystem.K0 p)) = 0 :=
    fun i => (ha.const_coeff i).eq_zero
  have ham : HasSubst (fun i => MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      (coordZ B (FormalGroupSystem.K0 p) 1 i : MvPowerSeries (Zidx n' r0 r1) (FormalGroupSystem.K0 p))) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [ha0 i]
  have hη0 : ∀ i, constantCoeff (PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p)) = 0 :=
    fun i => constantCoeff_psubst (hξ i) constantCoeff_logF_C
  have hηs : HasSubst (fun i => PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p)) :=
    hasSubst_of_constantCoeff_zero hη0

  have hbe0 : constantCoeff be = 0 := by
    by_contra hc
    have := (hbe.ab 0 (by simpa using hc)).1
    simp at this
  have hsub0 : ∀ e : Eidx n' r0 r1, constantCoeff (sub2 p be
      (MvPowerSeries.X (Sum.inl e) : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p))
      (MvPowerSeries.X (Sum.inr e))) = 0 := by
    intro e
    have h2 : ∀ s, constantCoeff ((![MvPowerSeries.X (Sum.inl e), MvPowerSeries.X (Sum.inr e)] :
        Fin 2 → MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)) s) = 0 := by
      intro s; fin_cases s <;> simp
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h2) h2 hbe0
  set Φ : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p) :=
    ∑ e : Eidx n' r0 r1, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) with hΦ
  have hΦ0 : constantCoeff (-Φ) = 0 := by
    rw [map_neg, hΦ, map_sum, Finset.sum_eq_zero fun e _ => hsub0 e, neg_zero]
  have hΦm : constantCoeff (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (-Φ)) = 0 := by
    rw [constantCoeff_map, hΦ0, map_zero]

  have hexp : MvPowerSeries.subst (fun i => PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p))
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (FormalGroupSystem.expS p (-Φ))) =
      product_zeroth_first_parts.expS ℂ_[p] (-(∑ e : Eidx n' r0 r1, GlobalTheory.ThBe0.at2 (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be)
        (PowerSeries.subst (ξ (Sum.inl e)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (ξ (Sum.inr e)) (Formalism.MainNotions.GL3Theta.logF p)))) := by
    rw [map_expS hΦ0]
    unfold product_zeroth_first_parts.expS
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp _ hη0 hΦm]
    congr 1
    rw [← coe_substAlgHom hηs, map_neg, map_neg, hΦ, map_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [coe_substAlgHom hηs]
    exact subst_bivariateSeries_difference_pair be hη0 _ _

  have hL0 : ∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, constantCoeff (PowerSeries.subst
      (MvPowerSeries.X i : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)) (FormalGroupSystem.logF p)) = 0 :=
    fun i => constantCoeff_psubst (by simp) constantCoeff_padicLogSeries_unramified_eq_zero
  have hLm : ∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (PowerSeries.subst
      (MvPowerSeries.X i : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)) (FormalGroupSystem.logF p)) =
      PowerSeries.subst (MvPowerSeries.X i) (Formalism.MainNotions.GL3Theta.logF p) := by
    intro i
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), map_X,
      Formalism.L2.G.Pend.logF_map]
  have hLc : ∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, constantCoeff (PowerSeries.subst
      (MvPowerSeries.X i : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) ℂ_[p]) (Formalism.MainNotions.GL3Theta.logF p)) = 0 :=
    fun i => constantCoeff_psubst (by simp) constantCoeff_logF_C
  have hcof : MvPowerSeries.subst ξ (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inParam p U)) =
      MvPowerSeries.subst (fun i => PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p))
        (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) U) := by
    unfold inParam
    rw [map_subst (hasSubst_of_constantCoeff_zero hL0)]
    simp_rw [hLm]
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hLc) hξs]
    congr 1
    funext i
    rw [GlobalTheory.BeProps.subst_psubst hξs (by simp), subst_X hξs]
  rw [hcof, ← hexp, ← subst_mul hηs, ← map_mul]
  unfold thOne ThZ
  rw [map_subst ha, subst_comp_subst_apply ham hJs]
  simp_rw [h]
  rfl

end GlobalTheory.OnePlaceRead

end
