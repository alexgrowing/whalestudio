import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoeffProdRename

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen

open Finset

section Supp

variable {R σ Pl : Type} [CommRing R]

def SuppOn (π : σ → Pl) (v : Pl) : Subring (MvPowerSeries σ R) where
  carrier := {f | ∀ m, MvPowerSeries.coeff m f ≠ 0 → ∀ x ∈ m.support, π x = v}
  mul_mem' := by
    classical
    intro f g hf hg m hm x hx
    rw [MvPowerSeries.coeff_mul] at hm
    obtain ⟨ab, hab, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [← hab] at hx
    rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
    · exact hf _ (left_ne_zero_of_mul hne) x h
    · exact hg _ (right_ne_zero_of_mul hne) x h
  one_mem' := by
    classical
    intro m hm x hx
    rw [MvPowerSeries.coeff_one] at hm
    split_ifs at hm with h
    · subst h; simp at hx
    · exact absurd rfl hm
  add_mem' := by
    intro f g hf hg m hm x hx
    rw [map_add] at hm
    by_cases h : MvPowerSeries.coeff m f = 0
    · rw [h, zero_add] at hm; exact hg m hm x hx
    · exact hf m h x hx
  zero_mem' := by
    intro m hm
    exact absurd (map_zero _) hm
  neg_mem' := by
    intro f hf m hm x hx
    rw [map_neg, neg_ne_zero] at hm
    exact hf m hm x hx

theorem mem_SuppOn {π : σ → Pl} {v : Pl} {f : MvPowerSeries σ R} :
    f ∈ SuppOn π v ↔ ∀ m, MvPowerSeries.coeff m f ≠ 0 → ∀ x ∈ m.support, π x = v := Iff.rfl

theorem X_mem {π : σ → Pl} {v : Pl} {x : σ} (h : π x = v) : (MvPowerSeries.X x : MvPowerSeries σ R) ∈ SuppOn π v := by
  classical
  intro m hm y hy
  rw [MvPowerSeries.coeff_X] at hm
  split_ifs at hm with hmx
  · subst hmx
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hy
    rw [hy]
    exact h
  · exact absurd rfl hm

theorem C_mem {π : σ → Pl} {v : Pl} (c : R) : (MvPowerSeries.C c : MvPowerSeries σ R) ∈ SuppOn π v := by
  classical
  intro m hm y hy
  rw [MvPowerSeries.coeff_C] at hm
  split_ifs at hm with h0
  · subst h0
    simp at hy
  · exact absurd rfl hm

theorem subst_mem {τ : Type} {π : σ → Pl} {π' : τ → Pl} {v : Pl} {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) {f : MvPowerSeries σ R} (hf : f ∈ SuppOn π v)
    (h : ∀ s, π s = v → a s ∈ SuppOn π' v) : MvPowerSeries.subst a f ∈ SuppOn π' v := by
  classical
  intro e he x hx
  rw [MvPowerSeries.coeff_subst ha] at he
  by_contra hxv
  apply he
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : MvPowerSeries.coeff d f = 0
  · rw [hd, zero_smul]
  · have hprod : (d.prod fun s n => a s ^ n) ∈ SuppOn π' v := by
      unfold Finsupp.prod
      exact Subring.prod_mem _ fun s hs => Subring.pow_mem _ (h s ((mem_SuppOn.mp hf) d hd s hs)) _
    have h0 : MvPowerSeries.coeff e (d.prod fun s n => a s ^ n) = 0 := by
      by_contra hne
      exact hxv ((mem_SuppOn.mp hprod) e hne x hx)
    rw [h0, smul_zero]

theorem map_mem {R' : Type} [CommRing R'] (φ : R →+* R') {π : σ → Pl} {v : Pl} {f : MvPowerSeries σ R}
    (hf : f ∈ SuppOn π v) : MvPowerSeries.map φ f ∈ SuppOn π v := by
  intro m hm x hx
  rw [MvPowerSeries.coeff_map] at hm
  exact (mem_SuppOn.mp hf) m (fun h0 => hm (by rw [h0, map_zero])) x hx

end Supp

def resP {R Pl : Type} [CommRing R] {ι : Pl → Type} (v : Pl) (f : MvPowerSeries (Σ v, ι v) R) : MvPowerSeries (ι v) R :=
  fun m => MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) f

theorem coeff_resP {R Pl : Type} [CommRing R] {ι : Pl → Type} (v : Pl) (f : MvPowerSeries (Σ v, ι v) R) (m : ι v →₀ ℕ) :
    MvPowerSeries.coeff m (resP v f) = MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) f := rfl

theorem eq_atP {R Pl : Type} [CommRing R] {ι : Pl → Type} [Fintype Pl] [DecidableEq Pl] (v : Pl)
    (f : MvPowerSeries (Σ v, ι v) R) (hf : f ∈ SuppOn (Sigma.fst : (Σ v, ι v) → Pl) v) :
    f = atP v (resP v f) := by
  classical
  ext n
  have h2 : ∀ m : ι v →₀ ℕ, (eqv (ι := ι)).symm (Pi.single v m) =
      Finsupp.embDomain (Function.Embedding.sigmaMk v) m := by
    intro m
    rw [AddEquiv.symm_apply_eq, eqv_embDomain]
  by_cases hn : MvPowerSeries.coeff n f = 0
  · rw [hn]
    by_cases h : ∃ m, n = eqv.symm (Pi.single v m)
    · obtain ⟨m, rfl⟩ := h
      rw [coeff_atP_single, coeff_resP, ← h2]
      exact hn.symm
    · push_neg at h
      exact (coeff_atP_eq_zero v _ n h).symm
  · have hsupp := (mem_SuppOn.mp hf) n hn
    have hn' : n = eqv.symm (Pi.single v (eqv n v)) := by
      rw [AddEquiv.eq_symm_apply]
      funext w
      ext i
      by_cases hw : w = v
      · subst hw
        rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hw, Finsupp.coe_zero, Pi.zero_apply,
          Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply]
        by_contra hne
        exact hw (hsupp ⟨w, i⟩ (Finsupp.mem_support_iff.mpr hne))
    calc MvPowerSeries.coeff n f
        = MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) (eqv n v)) f := by
          rw [← h2, ← hn']
      _ = MvPowerSeries.coeff n (atP v (resP v f)) := by
          rw [← coeff_resP, ← coeff_atP_single v (resP v f) (eqv n v), ← hn']

theorem jp_subst_expand {K A σ τ : Type} [CommRing K] [CommRing A] [Algebra K A] (Q : MvPolynomial σ A)
    (F : MvPowerSeries σ K) (a : τ → MvPowerSeries σ K) (ha : MvPowerSeries.HasSubst a) (U : MvPowerSeries τ K) :
    ∃ B : Finset (τ →₀ ℕ), jp Q (F * MvPowerSeries.subst a U) =
      ∑ β ∈ B, MvPowerSeries.coeff β U • jp Q (F * β.prod fun s e => a s ^ e) := by
  classical
  refine ⟨Q.support.biUnion fun κ => (Finset.HasAntidiagonal.antidiagonal κ).biUnion fun pq =>
    (MvPowerSeries.coeff_subst_finite ha U pq.2).toFinset, ?_⟩
  set B := Q.support.biUnion fun κ => (Finset.HasAntidiagonal.antidiagonal κ).biUnion fun pq =>
    (MvPowerSeries.coeff_subst_finite ha U pq.2).toFinset with hB
  have hq : ∀ κ ∈ Q.support, ∀ pq ∈ Finset.HasAntidiagonal.antidiagonal κ,
      MvPowerSeries.coeff pq.2 (MvPowerSeries.subst a U) =
        ∑ β ∈ B, MvPowerSeries.coeff β U * MvPowerSeries.coeff pq.2 (β.prod fun s e => a s ^ e) := by
    intro κ hκ pq hpq
    rw [MvPowerSeries.coeff_subst ha, finsum_eq_sum_of_support_subset (s := B)]
    · simp only [smul_eq_mul]
    · intro β hβ
      rw [Finset.mem_coe, hB, Finset.mem_biUnion]
      exact ⟨κ, hκ, Finset.mem_biUnion.mpr ⟨pq, hpq,
        (MvPowerSeries.coeff_subst_finite ha U pq.2).mem_toFinset.mpr hβ⟩⟩
  have hκ : ∀ κ ∈ Q.support, MvPowerSeries.coeff κ (F * MvPowerSeries.subst a U) =
      ∑ β ∈ B, MvPowerSeries.coeff β U * MvPowerSeries.coeff κ (F * β.prod fun s e => a s ^ e) := by
    intro κ hκ
    rw [MvPowerSeries.coeff_mul]
    simp_rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun pq hpq => ?_
    rw [hq κ hκ pq hpq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  unfold jp
  have hL : ∑ κ ∈ Q.support, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ (F * MvPowerSeries.subst a U)) •
        MvPolynomial.coeff κ Q =
      ∑ κ ∈ Q.support, ∑ β ∈ B, (((fac κ : ℕ) : K) * (MvPowerSeries.coeff β U *
        MvPowerSeries.coeff κ (F * β.prod fun s e => a s ^ e))) • MvPolynomial.coeff κ Q := by
    refine Finset.sum_congr rfl fun κ hκ' => ?_
    rw [hκ κ hκ', Finset.mul_sum, Finset.sum_smul]
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [smul_smul]
  congr 1
  ring

end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
