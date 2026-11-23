import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsVeryAmpleZFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u v w

namespace VeryAmpleZExtend

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem prod_mem_pow {r : ℕ} (H : SubSystem S x Ω) {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ H.secs)
    (I : Chart x) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.card_empty]; exact one_mem_twistMod_zero I
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_comm]
    have h1 : h a ∈ (H.pow 1).sub I := by
      rw [SubSystem.pow_sub, pow_one]
      exact (Submodule.restrictScalars_mem _ _ _).mp ((Submodule.mem_iInf _).mp (hh a) I)
    exact AmpleTwistLocal.mul_mem_pow H I ih 1 h1

omit [Module S E] [IsScalarTower S Ω E] in

theorem smul_mem_twist_pow (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {a b : ℕ} {z : E}
    {w : Ω} (hz : z ∈ (F.twist (H.pow a)).sub I) (hw : w ∈ (H.pow b).sub I) :
    w • z ∈ (F.twist (H.pow (a + b))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => w • z ∈ (F.twist (H.pow (a + b))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, AmpleTwistLocal.mul_mem_pow H I hq b hw, y, hy, ?_⟩
    rw [smul_smul, mul_comm]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro z z' _ _ hz hz'; rw [smul_add]; exact Submodule.add_mem _ hz hz'
  · intro t z _ hz
    have e : w • (t • z) = t • (w • z) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ t hz

omit [Module S E] [IsScalarTower S Ω E] in

theorem gen_smul {r : ℕ} (F : SubSystem S x E) (H : SubSystem S x Ω) {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (I : Chart x) (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) {c : Ω} {a : ℕ}
    (hc : c * h j ^ a ∈ (H.pow a).sub I) {y : E}
    (hy : ∃ m : ℕ, xProd J ^ m • y ∈ (F.twist (H.pow (J.1.card * m))).sub I) :
    ∃ m : ℕ, xProd J ^ m • (c • y) ∈ (F.twist (H.pow (J.1.card * m))).sub I := by
  classical
  obtain ⟨m, hm⟩ := hy
  have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
  have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
  have hw := AmpleTwistLocal.mul_mem_pow H I hc _
    (AmpleTwistLocal.pow_mem_pow H I (prod_mem_pow H hh I (J.1.erase j)) a)
  refine ⟨m + a, ?_⟩
  have e1 : xProd J ^ (m + a) • (c • y) =
      (c * h j ^ a * (∏ l ∈ J.1.erase j, h l) ^ a) • (xProd J ^ m • y) := by
    rw [smul_smul, smul_smul, hJ]
    congr 1
    ring
  have e2 : J.1.card * (m + a) = J.1.card * m + (a + (J.1.erase j).card * a) := by
    rw [← hcard]; ring
  rw [e1, e2]
  exact smul_mem_twist_pow F H I hm hw

theorem proof : VeryAmpleZExtend.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hh J j hj c hc K hK f hf
  classical
  have key : ∀ I : Chart x, ∀ᶠ M in atTop, c ^ M • f ∈ secsOnZChart F.toSubSystem H h I J := by
    intro I
    obtain ⟨a, ha⟩ := Set.mem_iInter.mp hc I
    rw [one_mul] at ha
    obtain ⟨e, n, hn⟩ := hK I
    rw [one_mul] at hn
    change c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n ∈ (H.pow n).sub I at hn

    have hfU := F.mono K (AmpleAffineGen.unionChart I K) (AmpleAffineGen.subset_unionChart_right I K) f hf
    obtain ⟨t, ht, htf⟩ := (F.mem_iff I (AmpleAffineGen.unionChart I K)
      (AmpleAffineGen.subset_unionChart_left I K) f).mp hfU
    obtain ⟨v, hv⟩ := ht.exists_left_inv
    obtain ⟨D, hD⟩ := AmpleAffineGen.exists_pow_mul_mem I K v.2
    have hv' : (v : Ω) * (t : Ω) = 1 := congrArg Subtype.val hv
    have hρf : AmpleAffineGen.chartRatio I K ^ D • f ∈ F.sub I := by
      have e1 : AmpleAffineGen.chartRatio I K ^ D • f =
          (⟨_, hD⟩ : chartRing S x I) • ((t : Ω) • f) := by
        rw [Subalgebra.smul_def, smul_smul]
        congr 1
        change _ = AmpleAffineGen.chartRatio I K ^ D * (v : Ω) * (t : Ω)
        rw [mul_assoc, hv', mul_one]
      rw [e1]
      exact Submodule.smul_mem _ _ htf

    have hP := prod_mem_pow H hh I (J.1.erase j)
    have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
    have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
    have hz : (c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n) ^ D •
        (AmpleAffineGen.chartRatio I K ^ D • f) ∈ (F.toSubSystem.twist (H.pow (n * D))).sub I :=
      Submodule.subset_span ⟨_, AmpleTwistLocal.pow_mem_pow H I hn D, _, hρf, rfl⟩
    have hz2 := smul_mem_twist_pow F.toSubSystem H I hz
      (AmpleTwistLocal.pow_mem_pow H I hP (n * D))
    have h0 : ∃ m : ℕ, xProd J ^ m • (c ^ (e * D) • f) ∈
        (F.toSubSystem.twist (H.pow (J.1.card * m))).sub I := by
      refine ⟨n * D, ?_⟩
      have e1 : xProd J ^ (n * D) • (c ^ (e * D) • f) =
          (∏ l ∈ J.1.erase j, h l) ^ (n * D) • ((c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n) ^ D •
            (AmpleAffineGen.chartRatio I K ^ D • f)) := by
        rw [smul_smul, smul_smul, smul_smul, hJ]
        congr 1
        have hr := AmpleAffineGen.chartRatio_mul_chartRatio I K
        calc (h j * ∏ l ∈ J.1.erase j, h l) ^ (n * D) * c ^ (e * D)
            = (∏ l ∈ J.1.erase j, h l) ^ (n * D) * ((c ^ e * h j ^ n) ^ D *
                (AmpleAffineGen.chartRatio K I * AmpleAffineGen.chartRatio I K) ^ D) := by
              rw [hr, one_pow, mul_one]; ring
          _ = _ := by ring
      have e2 : J.1.card * (n * D) = n * D + (J.1.erase j).card * (n * D) := by
        rw [← hcard]; ring
      rw [e1, e2]
      exact hz2

    have hstep : ∀ q : ℕ, ∃ m : ℕ, xProd J ^ m • (c ^ (e * D + q) • f) ∈
        (F.toSubSystem.twist (H.pow (J.1.card * m))).sub I := by
      intro q
      induction q with
      | zero => exact h0
      | succ q ih =>
        rw [← Nat.add_assoc, pow_succ', ← smul_smul]
        exact gen_smul F.toSubSystem H hh I J hj ha ih
    refine eventually_atTop.mpr ⟨e * D, fun M hM => ?_⟩
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hM
    exact Submodule.subset_span (hstep q)
  exact (eventually_all.mpr key).mono fun M hM => (Submodule.mem_iInf _).mpr hM

end VeryAmpleZExtend

end

end GroundTheory.Heights₂.Heights.Kleiman
