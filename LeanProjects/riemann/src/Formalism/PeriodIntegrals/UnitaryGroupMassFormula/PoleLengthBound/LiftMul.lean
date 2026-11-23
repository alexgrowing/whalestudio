import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.LeOrdASmulOsK
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseOrderBound.CompositionalInverseSymm

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

section

variable {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la)

def IntD (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (f : Lw X la G.w) : Prop :=
  ∀ γ : Idx D j G.N →₀ ℕ, ∃ g : ↥(Frac0 X la G.w), (g : Lw X la G.w) = hasse X la G.w γ f ∧
    ∀ ζ : PtsG G la, 0 ≤ ord (unifO X la G.N) ζ (toOsK X la G.w g)

variable {Q}

theorem ord_sum_nonneg (hC : Q.InCurve) (ζ : PtsG G la) {ι : Type*} (s : Finset ι) (f : ι → OsK X la G.w)
    (h : ∀ i ∈ s, 0 ≤ ord (unifO X la G.N) ζ (f i)) : 0 ≤ ord (unifO X la G.N) ζ (∑ i ∈ s, f i) := by
  classical
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, ord_zero ζ hU]; exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
      (ord_add ζ hU _ _)

theorem ord_mul_nonneg (hC : Q.InCurve) (ζ : PtsG G la) {x y : OsK X la G.w} (hx : 0 ≤ ord (unifO X la G.N) ζ x)
    (hy : 0 ≤ ord (unifO X la G.N) ζ y) : 0 ≤ ord (unifO X la G.N) ζ (x * y) := by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  rw [ord_mul ζ hU]
  exact add_nonneg hx hy

theorem ord_prod_nonneg (hC : Q.InCurve) (ζ : PtsG G la) {ι : Type*} (s : Finset ι) (f : ι → OsK X la G.w)
    (h : ∀ i ∈ s, 0 ≤ ord (unifO X la G.N) ζ (f i)) : 0 ≤ ord (unifO X la G.N) ζ (∏ i ∈ s, f i) := by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  refine Finset.prod_induction f (fun x => 0 ≤ ord (unifO X la G.N) ζ x) (fun x y hx hy => ord_mul_nonneg hC ζ hx hy)
    ?_ h
  rw [ord_one ζ hU]

theorem ord_pow_nonneg (hC : Q.InCurve) (ζ : PtsG G la) {x : OsK X la G.w} (hx : 0 ≤ ord (unifO X la G.N) ζ x)
    (n : ℕ) : 0 ≤ ord (unifO X la G.N) ζ (x ^ n) := by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  rw [ord_pow ζ hU]
  exact nsmul_nonneg hx n

theorem intD_mul (hC : Q.InCurve) {f1 f2 : Lw X la G.w} (h1 : IntD G la f1) (h2 : IntD G la f2) :
    IntD G la (f1 * f2) := by
  intro γ
  choose g1 hg1 ho1 using h1
  choose g2 hg2 ho2 using h2
  refine ⟨∑ q ∈ antidiagonal γ, g1 q.1 * g2 q.2, ?_, fun ζ => ?_⟩
  · show _ = PI.HJP.H X la G.w γ (f1 * f2)
    rw [PI.HJP.H_mul]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hg1, hg2]
    rfl
  · rw [map_sum]
    refine ord_sum_nonneg hC ζ _ _ fun q _ => ?_
    rw [map_mul]
    exact ord_mul_nonneg hC ζ (ho1 _ ζ) (ho2 _ ζ)

theorem intD_one (hC : Q.InCurve) : IntD G la (1 : Lw X la G.w) := by
  classical
  have hU := isUnif_of_curve Q hC
  intro γ
  refine ⟨if γ = 0 then 1 else 0, ?_, fun ζ => ?_⟩
  · show _ = MvPowerSeries.coeff γ (tayLc X la G.w 1)
    rw [map_one, MvPowerSeries.coeff_one]
    split_ifs <;> rfl
  · have := isDVRAt_of_curve Q hC ζ
    split_ifs
    · rw [map_one, ord_one ζ hU]
    · rw [map_zero, ord_zero ζ hU]; exact le_top

theorem intD_prod (hC : Q.InCurve) {ι : Type*} (s : Finset ι) (f : ι → Lw X la G.w) (h : ∀ i ∈ s, IntD G la (f i)) :
    IntD G la (∏ i ∈ s, f i) :=
  Finset.prod_induction f (fun x => IntD G la x) (fun _ _ hx hy => intD_mul hC hx hy) (intD_one hC) h

theorem intD_pow (hC : Q.InCurve) {f : Lw X la G.w} (hf : IntD G la f) (n : ℕ) : IntD G la (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact intD_one hC
  | succ n ih => rw [pow_succ]; exact intD_mul hC ih hf

theorem intD_sfr (hC : Q.InCurve) (u : Fin G.N → OsK X la G.w) (hu : uSpec G la u)
    (ho : ∀ (ζ : PtsG G la) col, 0 ≤ ord (unifO X la G.N) ζ (u col)) (i : Fin (WeightFamilies.dimY D j + 1)) :
    IntD G la (sfr X la G.w i : Lw X la G.w) := by
  classical
  have hU := isUnif_of_curve Q hC
  choose fk hfk1 hfk2 using hu
  choose mq hmq hfq using fun q : Idx D j G.N →₀ ℕ => PI.HasseOrdBdW.compositionalInverseSymm X la G.w 1 q
  intro γ
  set c : (Idx D j G.N →₀ ℕ) → Fin G.N → Kp X la G.N :=
    fun q k => algebraMap (Op X la G.N) (Kp X la G.N) (hasseOp X la G.N q (Tv X la G.N (i, k))) with hc
  refine ⟨∑ q ∈ antidiagonal γ, (mq q.2 : ↥(Frac0 X la G.w)) *
      ((∑ k, c q.1 k • fk k) * ∏ k, fk k ^ q.2 ((0 : Fin (WeightFamilies.dimY D j + 1)), k)), ?_, fun ζ => ?_⟩
  · have e0 : (sfr X la G.w i : Lw X la G.w) =
        algebraMap (Rp X la G.N) (Lw X la G.w) (sec X la G.w i) * w0inv X la G.w ^ 1 := by
      rw [coe_sfr, frac_apply]
    show _ = PI.HJP.H X la G.w γ (sfr X la G.w i : Lw X la G.w)
    rw [e0, PI.HJP.H_mul]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    have hA : PI.HJP.H X la G.w q.1 (algebraMap (Rp X la G.N) (Lw X la G.w) (sec X la G.w i)) =
        algebraMap (Rp X la G.N) (Lw X la G.w) (∑ k, c q.1 k • emb X la G.N (X.inc wL (G.w k))) := by
      exact (hasse_algebraMap X la G.w q.1 (sec X la G.w i)).trans
        (congrArg (algebraMap (Rp X la G.N) (Lw X la G.w)) (by rw [hasseRp_sec]))
    have hB : PI.HJP.H X la G.w q.2 (w0inv X la G.w ^ 1) = (mq q.2 : Lw X la G.w) *
        algebraMap (Rp X la G.N) (Lw X la G.w) (∏ k, emb X la G.N (X.inc wL (G.w k)) ^ q.2 (0, k)) *
          w0inv X la G.w ^ (1 + q.2.sum fun _ n => n) := hfq q.2
    rw [hA, hB]
    by_cases hm : mq q.2 = 0
    · simp [hm]
    · have hn := hmq q.2 hm
      simp only [hfk1, map_sum, map_prod, map_pow, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply (Kp X la G.N) (Rp X la G.N) (Lw X la G.w)]
      rw [← hn, pow_add, ← Finset.prod_pow_eq_pow_sum]
      simp only [mul_pow, Finset.prod_mul_distrib]
      have e1 : ∀ (A E : Fin G.N → Lw X la G.w) (y : Lw X la G.w),
          ∑ k, A k * (E k * y) = (∑ k, A k * E k) * y := fun A E y => by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
      rw [e1]
      ring
  · rw [map_sum]
    refine ord_sum_nonneg hC ζ _ _ fun q _ => ?_
    have := isDVRAt_of_curve Q hC ζ
    rw [map_mul, map_mul, map_intCast]
    refine ord_mul_nonneg hC ζ (ord_nonneg ζ hU (intCast_mem _ _)) (ord_mul_nonneg hC ζ ?_ ?_)
    · rw [map_sum]
      refine ord_sum_nonneg hC ζ _ _ fun k _ => ?_
      rw [map_smul, hfk2, hc, algebraMap_smul, Algebra.smul_def]
      exact ord_mul_nonneg hC ζ (ord_nonneg ζ hU (Subalgebra.algebraMap_mem _ _)) (ho ζ k)
    · rw [map_prod]
      refine ord_prod_nonneg hC ζ _ _ fun k _ => ?_
      rw [map_pow, hfk2]
      exact ord_pow_nonneg hC ζ (ho ζ k) _

theorem intD_yPow (hC : Q.InCurve) (u : Fin G.N → OsK X la G.w) (hu : uSpec G la u)
    (ho : ∀ (ζ : PtsG G la) col, 0 ≤ ord (unifO X la G.N) ζ (u col)) (α : Fin (WeightFamilies.dimY D j) → ℕ) :
    IntD G la (yPow X la G.w α : Lw X la G.w) := by
  have e : (yPow X la G.w α : Lw X la G.w) = ∏ i, (sfr X la G.w i.succ : Lw X la G.w) ^ α i := by
    unfold yPow
    push_cast
    rfl
  rw [e]
  exact intD_prod hC _ _ fun i _ => intD_pow hC (intD_sfr hC u hu ho i.succ) _

theorem good_mul (hC : Q.InCurve) {T : ℕ} {f : ↥(Frac0 X la G.w)} (hf : IntD G la (f : Lw X la G.w))
    {x : ↥(HK X la G.w wF)} (hx : GoodP Q T (fun _ => 0) x) : GoodP Q T (fun _ => 0) (f • x) := by
  choose g hg ho using hf
  have hP := hasse_preserves_kernel G la
  intro β hβ ζ
  rw [rD_eq G la β _ (hP β _ (f • x).2)]
  have e : (⟨_, hP β _ (f • x).2⟩ : ↥(HK X la G.w wF)) =
      ∑ q ∈ antidiagonal β, g q.1 • (⟨_, hP q.2 _ x.2⟩ : ↥(HK X la G.w wF)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    show PI.HJP.H X la G.w β ((f : Lw X la G.w) * (x : Lw X la G.w)) = _
    rw [PI.HJP.H_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Submodule.coe_smul]
    exact (congrArg (· * hasse X la G.w q.2 (x : Lw X la G.w)) (hg q.1)).symm
  rw [e, map_sum]
  refine le_ordA_sum Q hC ζ _ _ _ fun q hq => ?_
  rw [LinearMap.map_smul, ← algebraMap_smul (OsK X la G.w) (g q.1)]
  refine le_ordA_smul_OsK Q hC ζ _ (ho q.1 ζ) _ _ ?_
  have hq2 : (q.2.sum fun _ n => n) ≤ a0 D j T - 1 := by
    rw [mem_antidiagonal] at hq
    rw [PI.HJP.sum_eq_degree] at hβ ⊢
    have : Finsupp.degree β = Finsupp.degree q.1 + Finsupp.degree q.2 := by rw [← hq, map_add]
    omega
  have := hx q.2 hq2 ζ
  rwa [rD_eq G la q.2 x (hP q.2 _ x.2)] at this

end

theorem liftMul_of {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (T : ℕ) (hC : Q.InCurve)
    (h3 : UnitCols G la) : LiftMul G la Q T := by
  obtain ⟨u, hu, -, ho⟩ := h3
  intro x α hx
  by_cases ha : 0 < a0 D j T
  · have hg := good_of_mem_AAp hC ha hx x rfl
    have hg' := good_mul hC (intD_yPow (Q := Q) hC u hu ho α) hg
    have hP := hasse_preserves_kernel G la
    refine Submodule.subset_span ⟨yPow X la G.w α • x, ⟨fun β _ => hP β _ (yPow X la G.w α • x).2, fun β hβ ζ => ?_⟩, rfl⟩
    have := hg' β hβ ζ
    rwa [rD_eq G la β _ (hP β _ (yPow X la G.w α • x).2)] at this
  · have h0 : ∀ y : ↥(HK X la G.w wF), toWK X la G.w wF (a0 D j T) y = 0 := fun y => by
      rw [toWK_eq_zero_iff, show a0 D j T = 0 by omega, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    rw [h0]
    exact Submodule.zero_mem _

end PI.PoleLengthCount
