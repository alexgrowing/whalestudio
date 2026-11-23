import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FrameL
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.FrameW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.TermsAtPtFiniteW.HeisW
  PI.TermsAtPtFiniteW.LeviW

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem sum_sub_delta (X : Matrix (Fin r) (Fin r) E) (g : Fin r → S.V) (a : Fin r) :
    ∑ c, X c a • g c - g a = ∑ c, (X c a - if c = a then 1 else 0) • g c := by
  simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem psiF_mem (Λ : Submodule (𝓞 E) S.V) (e f : Fin r → S.V) (U U' : Matrix (Fin r) (Fin r) E) (m : E)
    (hm : star m = m) (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 E, (o : E) = S.hT x y)
    (he : ∀ c, e c ∈ Λ) (hf : ∀ c, m • f c ∈ Λ)
    (hU : ∀ c a, ∃ o : 𝓞 E, (o : E) * m = U c a - if c = a then 1 else 0)
    (hU' : ∀ c a, ∃ o : 𝓞 E, (o : E) * m = U' c a - if c = a then 1 else 0)
    {v : S.V} (hv : v ∈ Λ) : psiF e f U U' v ∈ Λ := by
  rw [psiF_apply]
  refine Λ.add_mem (Λ.add_mem hv ?_) ?_
  · refine Submodule.sum_mem _ fun a _ => ?_
    rw [sum_sub_delta, Finset.smul_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨o, ho⟩ := hU c a
    rw [← ho, smul_smul]
    refine smul_memO Λ ?_ (he c)
    obtain ⟨o2, h2⟩ := hint _ (hf a) _ hv
    have hmf : S.hT (m • f a) v = m * S.hT (f a) v := by
      rw [LinearMap.map_smulₛₗ₂, starRingEnd_apply, hm, smul_eq_mul]
    refine ⟨o2 * o, ?_⟩
    have : ((o2 * o : 𝓞 E) : E) = (o2 : E) * (o : E) := rfl
    rw [this, h2, hmf]
    ring
  · refine Submodule.sum_mem _ fun a _ => ?_
    rw [sum_sub_delta, Finset.smul_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨o, ho⟩ := hU' c a
    rw [← ho]
    have : S.hT (e a) v • ((o : E) * m) • f c = (S.hT (e a) v * o) • (m • f c) := by
      rw [smul_smul, smul_smul, mul_assoc]
    rw [this]
    refine smul_memO Λ ?_ (hf c)
    obtain ⟨o2, h2⟩ := hint _ (he a) _ hv
    exact ⟨o2 * o, by rw [← h2]; rfl⟩

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem aaS_eq (D : D7) (a : Fin D.R.rS) :
    Formalism.L2.SG.Saturated.aaS D a = (ddS D ^ (D.R.rS - a.1))⁻¹ := by
  unfold Formalism.L2.SG.Saturated.aaS
  have hk : ((D.R.rS : ℤ) - (a : ℕ)) = ((D.R.rS - a.1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub a.2.le]
  rw [hk, zpow_neg, zpow_natCast]

theorem one_mem_aaS (D : D7) (a : Fin D.R.rS) : (1 : D.host.E) ∈ Formalism.L2.SG.Saturated.aaS D a := by
  rw [aaS_eq, FractionalIdeal.mem_inv_iff (pow_ne_zero _ (PI.SRW.ddS_ne D))]
  intro y hy
  rw [one_mul]
  have : ddS D ^ (D.R.rS - a.1) ≤ 1 := by
    unfold ddS
    rw [← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one
  exact this hy

theorem norm_mem_ddS (D : D7) :
    ((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) : ℕ) : D.host.E) ∈ ddS D := by
  unfold ddS
  rw [FractionalIdeal.mem_coeIdeal]
  refine ⟨((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) : ℕ) : 𝓞 D.host.E), ?_, map_natCast _ _⟩
  have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
    (Ideal.absNorm_mem (differentIdeal ℤ (𝓞 D.host.F)))
  rwa [map_natCast] at this

theorem m_mem_aaS_inv (D : D7) (a : Fin D.R.rS) :
    (((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F))) ^ D.R.rS : ℕ) : D.host.E) ∈
      (Formalism.L2.SG.Saturated.aaS D a)⁻¹ := by
  rw [aaS_eq, inv_inv]
  set N := Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F))
  have hNk : ((N : D.host.E)) ^ (D.R.rS - a.1) ∈ ddS D ^ (D.R.rS - a.1) := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow]
    exact Submodule.pow_mem_pow _ (FractionalIdeal.mem_coe.mpr (norm_mem_ddS D)) _
  have h1 : ((N : D.host.E)) ^ (D.R.rS - a.1) ∈ ((ddS D ^ (D.R.rS - a.1) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) :=
    FractionalIdeal.mem_coe.mpr hNk
  have h2 := Submodule.smul_mem _ ((N : 𝓞 D.host.E) ^ a.1) h1
  rw [Algebra.smul_def, map_pow, map_natCast, ← pow_add, Nat.add_sub_cancel' a.2.le] at h2
  push_cast
  exact FractionalIdeal.mem_coe.mp h2

theorem frame_fin (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (b : 𝓞 D.host.E)
    (B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (hB : UpB b B)
    (nH nL : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hnHe : ∀ j, nH (F0.e j) = F0.e j)
    (hnHz : nH F0.z = F0.z + ∑ c, ((B (Fin.castSucc c) (Fin.last D.R.rS) : 𝓞 D.host.E) : D.host.E) • F0.e c)
    (hnLe : ∀ i, nL (F0.e i) = ∑ c, ((B (Fin.castSucc c) (Fin.castSucc i) : 𝓞 D.host.E) : D.host.E) • F0.e c)
    (hnLz : nL F0.z = F0.z) (j : Fin (D.R.rS + 1)) :
    (nH * nL) (frame (lf D F0) j) = ∑ c, ((B c j : 𝓞 D.host.E) : D.host.E) • frame (lf D F0) c := by
  have hfe : ∀ i, frame (lf D F0) (Fin.castSucc i) = F0.e i := fun i => by
    simp [frame, Formalism.MainNotions.S.FlagG.fvec]
  have hfz : frame (lf D F0) (Fin.last D.R.rS) = F0.z := by
    simp [frame, Formalism.MainNotions.S.FlagG.fvec]
  rw [LinearEquiv.mul_apply]
  induction j using Fin.lastCases with
  | last =>
    rw [hfz, hnLz, hnHz, Fin.sum_univ_castSucc, hfz, (hB _ _).2.1 rfl]
    simp only [hfe]
    rw [add_comm]
    congr 1
    simp
  | cast i =>
    rw [hfe, hnLe, map_sum, Fin.sum_univ_castSucc, hfz, (hB _ _).1 (Fin.castSucc_lt_last i)]
    simp only [map_smul, hnHe, hfe]
    simp

end D7

end PI.TermsAtPtFiniteW.FrameW
