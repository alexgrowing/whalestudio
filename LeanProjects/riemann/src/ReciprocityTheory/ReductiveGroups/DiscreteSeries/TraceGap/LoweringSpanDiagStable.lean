import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemTensorFockOfCoeffs
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ConeNorm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARKinv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

section Low

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ X}

theorem dot_add_right_alt (c : ℂ) {μ : Fin n → ℝ} {v : X} (h : IsKHWVec ε A μ v) : IsKHWVec ε A μ (c • v) :=
  ⟨fun a => by rw [map_smul, h.1 a, smul_comm], fun a b h1 h2 => by rw [map_smul, h.2 a b h1 h2, smul_zero]⟩

theorem highestWeight_sub {μ : Fin n → ℝ} {v w : X} (hv : IsKHWVec ε A μ v) (hw : IsKHWVec ε A μ w) :
    IsKHWVec ε A μ (v - w) :=
  ⟨fun a => by rw [map_sub, hv.1 a, hw.1 a, smul_sub],
    fun a b h1 h2 => by rw [map_sub, hv.2 a b h1 h2, hw.2 a b h1 h2, sub_zero]⟩

variable (hK : ∀ a b c d, ε a = ε b → ε c = ε d →
  A a b * A c d - A c d * A a b = (if b = c then A a d else 0) - (if d = a then A c b else 0))
include hK

theorem loweringWord_weight {μ : Fin n → ℝ} {y : X} (hy : ∀ a, A a a y = (μ a : ℂ) • y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ (a : Fin n),
      A a a (lowWord A y l) = (lowWt μ l a : ℂ) • lowWord A y l
  | [], _, a => by simpa [lowWord, lowWt] using hy a
  | p :: l, hl, a => by
    obtain ⟨c, d⟩ := p
    have hcd : IsKLow ε (c, d) := hl _ (List.mem_cons_self ..)
    have hl' : ∀ p ∈ l, IsKLow ε p := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have h := congrArg (fun Y : Module.End ℂ X => Y (lowWord A y l)) (hK a a c d rfl hcd.2)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [loweringWord_weight hy l hl' a, map_smul, sub_eq_iff_eq_add] at h
    simp only [lowWord, lowWt]
    rw [h]
    simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases hac : a = c <;> by_cases had : a = d
    · subst hac; subst had; simp
    · subst hac
      simp only [if_neg had, if_neg (Ne.symm had), LinearMap.zero_apply, sub_zero]
      push_cast
      module
    · subst had
      simp only [if_neg hac, LinearMap.zero_apply, zero_sub]
      push_cast
      module
    · simp [hac, had, Ne.symm had]

theorem loweringSpan_diag_stable {μ : Fin n → ℝ} {y : X} (hy : ∀ a, A a a y = (μ a : ℂ) • y)
    (a : Fin n) : ∀ x ∈ kLowSpan ε A y, A a a x ∈ kLowSpan ε A y := by
  have : kLowSpan ε A y ≤ (kLowSpan ε A y).comap (A a a) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨l, hl, rfl⟩
    show A a a (lowWord A y l) ∈ kLowSpan ε A y
    rw [loweringWord_weight hK hy l hl a]
    exact Submodule.smul_mem _ _ (lowWord_mem hl)
  exact fun x hx => this hx

theorem loweringWord_mem_span_of_ge {μ : Fin n → ℝ} {y : X} (hy : ∀ a, A a a y = (μ a : ℂ) • y)
    {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) {a b : Fin n} (hab : b ≤ a) (hε : ε a = ε b) :
    A a b (lowWord A y l) ∈ kLowSpan ε A y := by
  rcases hab.lt_or_eq with h | rfl
  · exact kLowSpan_low_stable (c := a) (d := b) ⟨h, hε⟩ _ (lowWord_mem hl)
  · exact loweringSpan_diag_stable hK hy b _ (lowWord_mem hl)

theorem loweringWord_raise_mem_span {μ : Fin n → ℝ} {y : X} (hy : IsKHWVec ε A μ y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ a b : Fin n, a < b → ε a = ε b →
      A a b (lowWord A y l) ∈ kLowSpan ε A y
  | [], _, a, b, hab, hε => by
    simp only [lowWord]
    rw [hy.2 a b hab hε]
    exact Submodule.zero_mem _
  | p :: l, hl, a, b, hab, hε => by
    obtain ⟨c, d⟩ := p
    have hcd : IsKLow ε (c, d) := hl _ (List.mem_cons_self ..)
    have hl' : ∀ p ∈ l, IsKLow ε p := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have ih := loweringWord_raise_mem_span hy l hl'
    have key : ∀ a' b' : Fin n, ε a' = ε b' → A a' b' (lowWord A y l) ∈ kLowSpan ε A y := by
      intro a' b' h'
      rcases lt_or_ge a' b' with h | h
      · exact ih a' b' h h'
      · exact loweringWord_mem_span_of_ge hK hy.1 hl' h h'
    have h := congrArg (fun Y : Module.End ℂ X => Y (lowWord A y l)) (hK a b c d hε hcd.2)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [sub_eq_iff_eq_add] at h
    simp only [lowWord]
    rw [h]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) (kLowSpan_low_stable hcd _ (ih a b hab hε))
    · split_ifs with hbc
      · subst hbc; exact key a d (hε.trans hcd.2)
      · simp
    · split_ifs with hda
      · subst hda; exact key c b (hcd.2.trans hε)
      · simp

theorem loweringSpan_kStable {μ : Fin n → ℝ} {y : X} (hy : IsKHWVec ε A μ y) :
    IsKStableSub ε A (kLowSpan ε A y) := by
  intro a b hab
  rcases lt_or_ge a b with h | h
  · have : kLowSpan ε A y ≤ (kLowSpan ε A y).comap (A a b) := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨l, hl, rfl⟩
      exact loweringWord_raise_mem_span hK hy l hl a b h hab
    exact fun x hx => this hx
  · rcases h.lt_or_eq with h | rfl
    · exact kLowSpan_low_stable ⟨h, hab⟩
    · exact loweringSpan_diag_stable hK hy.1 b

end Low

section Weights

theorem highestWeight_smul (u v w : Fin n → ℝ) : dot u (v + w) = dot u v + dot u w := by
  unfold dot
  simp [mul_add, sum_add_distrib]

theorem dot_positiveRootSum (lam : Fin n → ℝ) (Ph : Finset (Fin n × Fin n)) :
    dot lam (phSum Ph) = ∑ x ∈ Ph, (lam x.1 - lam x.2) := by
  unfold dot phSum
  simp only [Finset.sum_apply, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  have := Lap.LemK.cone_norm_dot_root lam x.1 x.2 1
  simpa using this

theorem normSq_nonneg_alt (u : Fin n → ℝ) : 0 ≤ nsq u := by
  unfold nsq dot
  exact sum_nonneg fun i _ => mul_self_nonneg (u i)

end Weights

section Form

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem highestWeight_extraction {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {V : Submodule ℂ M}
    (hcone : ∀ (μ : Fin n → ℝ) (w : M), w ∈ genSub E V → w ≠ 0 → IsKHWVec ε E μ w →
      Lap.LemK.InRootCone (μ - lowK ε lam))
    (hcas : ∀ v ∈ genSub E V, casimir E v = ((casVal lam : ℝ) : ℂ) • v)
    {y : TensorProduct ℂ M (Fock n)} (hyT : y ∈ tensFock (genSub E V)) (hyP : y ∈ physicalSubspace ε)
    (hyD : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y = 0) (hy0 : y ≠ 0) {μ : Fin n → ℝ}
    (hy : IsKHWVec ε (diagE ε (eT E) cpT cmT) μ y) :
    μ = gaW ε lam ∧ tco (sIdx ε) y ≠ 0 ∧ IsKHWVec ε E (lowK ε lam) (tco (sIdx ε) y) := by
  have hfun : (fun a b => TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b)) = diagE ε (eT E) cpT cmT := by
    funext a b
    rw [diagE, signedAction_tensor]
    rfl
  have hy' := hy
  rw [← hfun] at hy'
  obtain ⟨s, hs0, hsK⟩ := khw_extract ε hlam hy' hy0
  have hsP : s ⊆ lfPhysModes ε := support_subset_physicalModes hyP hs0
  have hwM : tcoef ((fockBasis n).coord s) y ∈ genSub E V := tcoef_mem hyT _
  have hν := hcone _ _ hwM hs0 hsK
  have hPh : IsPosNC ε (gcPh ε s) := gc_isPosNC ε hsP
  have hwt : fockWt ε s = rhoHol ε - rhoN ε + phSum (gcPh ε s) := gc_wt_eq ε hsP
  have hcasT : casimir (eT (n := n) E) y = ((casVal lam : ℝ) : ℂ) • y := by
    rw [ssh_casimir_eT]
    obtain ⟨x, rfl⟩ := hyT
    have hcomp : casimir E ∘ₗ (genSub E V).subtype = ((casVal lam : ℝ) : ℂ) • (genSub E V).subtype := by
      ext v
      simp [hcas v v.2]
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, hcomp, TensorProduct.map_smul_left,
      LinearMap.smul_apply]
  have hKv : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((μ - rhoHol ε) + rhoHol ε) y := by
    rw [sub_add_cancel]; exact hy
  have h2 := two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hKv hcasT
  rw [Module.End.mul_apply, hyD, map_zero, smul_zero] at h2
  have hc0 := (smul_eq_zero.mp h2.symm).resolve_right hy0
  have hreal : nsq (μ - rhoHol ε + rhoC ε) = nsq lam := by
    have h3 : nsq (μ - rhoHol ε + rhoC ε) - nsq (rho n) - casVal lam = 0 := by exact_mod_cast hc0
    unfold casVal at h3
    linarith
  have hsplit : μ - rhoHol ε + rhoC ε = lam + ((μ - fockWt ε s - lowK ε lam) + phSum (gcPh ε s)) := by
    rw [hwt]
    funext a
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsplit, carU_nsq_add, highestWeight_smul, dot_positiveRootSum] at hreal
  have hdb : 0 ≤ dot lam (μ - fockWt ε s - lowK ε lam) := Lap.LemK.cone_norm_dot_nonneg lam _ hlam.antitone hν
  have hdp : 0 ≤ ∑ x ∈ gcPh ε s, (lam x.1 - lam x.2) :=
    sum_nonneg fun x hx => sub_nonneg.2 (hlam.antitone (hPh x hx).1.le)
  have hnn := normSq_nonneg_alt ((μ - fockWt ε s - lowK ε lam) + phSum (gcPh ε s))
  have hPh0 : gcPh ε s = ∅ := by
    by_contra hne
    have : 0 < ∑ x ∈ gcPh ε s, (lam x.1 - lam x.2) :=
      sum_pos (fun x hx => sub_pos.2 (hlam (hPh x hx).1)) (nonempty_iff_ne_empty.2 hne)
    linarith
  have hγ : (μ - fockWt ε s - lowK ε lam) + phSum (gcPh ε s) = 0 :=
    Lap.LemK.cone_norm_eq_zero _ (by linarith)
  have hp0 : phSum (gcPh ε s) = 0 := by rw [hPh0]; simp [phSum]
  rw [hp0, add_zero] at hγ
  rw [hp0, add_zero] at hwt
  have hss : s = sIdx ε := by rw [sIdx_eq]; exact gc_Ph_empty hPh0
  have hμ : μ = gaW ε lam := by
    funext a
    have ha := congrFun hγ a
    have hw := congrFun hwt a
    simp only [gaW, lowK, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at ha hw ⊢
    linarith
  subst hss
  refine ⟨hμ, hs0, ?_⟩
  have hwt2 : μ - fockWt ε (sIdx ε) = lowK ε lam := by
    rw [hwt, hμ]
    funext a
    simp only [gaW, lowK, Pi.add_apply, Pi.sub_apply]
    ring
  rw [← hwt2]
  exact hsK

theorem highestWeight_uniqueness {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M}
    (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hcone : ∀ (μ : Fin n → ℝ) (w : M), w ∈ genSub E V → w ≠ 0 → IsKHWVec ε E μ w →
      Lap.LemK.InRootCone (μ - lowK ε lam))
    (hcas : ∀ v ∈ genSub E V, casimir E v = ((casVal lam : ℝ) : ℂ) • v)
    (hlowK : ∀ w ∈ genSub E V, IsKHWVec ε E (lowK ε lam) w → w ∈ V)
    {y z : TensorProduct ℂ M (Fock n)} (hyT : y ∈ tensFock (genSub E V)) (hyP : y ∈ physicalSubspace ε)
    (hyD : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y = 0) {μ : Fin n → ℝ}
    (hy : IsKHWVec ε (diagE ε (eT E) cpT cmT) μ y)
    (hzT : z ∈ tensFock (genSub E V)) (hzP : z ∈ physicalSubspace ε)
    (hzD : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) z = 0) (hz0 : z ≠ 0) {ν : Fin n → ℝ}
    (hz : IsKHWVec ε (diagE ε (eT E) cpT cmT) ν z) :
    ∃ c : ℂ, y = c • z := by
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0, zero_smul]⟩
  obtain ⟨hμ, hy1, hyK⟩ := highestWeight_extraction hlam hE hcone hcas hyT hyP hyD hy0 hy
  obtain ⟨hν, hz1, hzK⟩ := highestWeight_extraction hlam hE hcone hcas hzT hzP hzD hz0 hz
  obtain ⟨c, hc⟩ := khw_line_of_irr hE hU hV (hlowK _ (tcoef_mem hyT _) hyK) (hlowK _ (tcoef_mem hzT _) hzK)
    hyK hzK hz1
  refine ⟨c, ?_⟩
  by_contra hne
  have hd0 : y - c • z ≠ 0 := sub_ne_zero.2 hne
  rw [hμ] at hy
  rw [hν] at hz
  have hK := highestWeight_sub hy (dot_add_right_alt c hz)
  have hDd : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) (y - c • z) = 0 := by
    rw [map_sub, map_smul, hyD, hzD, smul_zero, sub_zero]
  have := highestWeight_extraction hlam hE hcone hcas (sub_mem hyT (Submodule.smul_mem _ _ hzT))
    (sub_mem hyP (Submodule.smul_mem _ _ hzP)) hDd hd0 hK
  apply this.2.1
  show tcoef ((fockBasis n).coord (sIdx ε)) (y - c • z) = 0
  rw [map_sub, map_smul]
  exact sub_eq_zero.2 hc

end Form

end ReciprocityTheory.ChartRestriction.DS.TRGap
