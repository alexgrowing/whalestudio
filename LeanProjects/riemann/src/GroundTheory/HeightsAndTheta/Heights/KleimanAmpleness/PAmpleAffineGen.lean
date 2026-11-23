import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleTwistLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace AmpleAffineGen

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

def unionChart (I J : Chart x) : Chart x :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩

theorem subset_unionChart_left (I J : Chart x) : I.1 ⊆ (unionChart I J).1 :=
  Finset.subset_union_left

theorem subset_unionChart_right (I J : Chart x) : J.1 ⊆ (unionChart I J).1 :=
  Finset.subset_union_right

theorem xProd_ne_zero (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)

def chartRatio (I J : Chart x) : Ω := xProd J ^ I.1.card / xProd I ^ J.1.card

theorem chartRatio_mul_chartRatio (I J : Chart x) : chartRatio J I * chartRatio I J = 1 := by
  rw [chartRatio, chartRatio, div_mul_div_comm, mul_comm (xProd I ^ _),
    div_self (mul_ne_zero (pow_ne_zero _ (xProd_ne_zero J)) (pow_ne_zero _ (xProd_ne_zero I)))]

theorem pow_mul_cancel {u p q y : Ω} (hpq : p * q = 1) (e D : ℕ) :
    (u ^ e * p) ^ D * (q ^ D * y) = u ^ (e * D) * y := by
  calc (u ^ e * p) ^ D * (q ^ D * y) = u ^ (e * D) * (p * q) ^ D * y := by ring
    _ = u ^ (e * D) * y := by rw [hpq, one_pow, mul_one]

def monoProd (T : Finset (Fin (N + 1))) : Poly S N := ∏ i ∈ T, X i

theorem monoProd_isHomogeneous (T : Finset (Fin (N + 1))) :
    (monoProd (S := S) T).IsHomogeneous T.card := by
  have := IsHomogeneous.prod T (fun i => (X i : Poly S N)) (fun _ => 1)
    (fun i _ => isHomogeneous_X S i)
  simpa [monoProd] using this

theorem monoProd_mem_monos {T I : Finset (Fin (N + 1))} (h : T ⊆ I) :
    monoProd (S := S) T ∈ monos I :=
  prod_mem fun _ hi => X_mem_monos (h hi)

theorem aeval_monoProd (T : Finset (Fin (N + 1))) :
    aeval x (monoProd (S := S) T) = ∏ i ∈ T, x i := by
  simp [monoProd, map_prod]

theorem chartRatio_mem (I J : Chart x) : chartRatio I J ∈ chartRing S x I :=
  ⟨monoProd J.1 ^ I.1.card, monoProd I.1 ^ J.1.card, J.1.card * I.1.card,
    pow_mem (monoProd_mem_monos subset_rfl) _, (monoProd_isHomogeneous J.1).pow _,
    by rw [mul_comm]; exact (monoProd_isHomogeneous I.1).pow _,
    by simp only [chartRatio, xProd, map_pow, aeval_monoProd]⟩

theorem exists_pow_mul_mem (I J : Chart x) {c : Ω} (hc : c ∈ chartRing S x (unionChart I J)) :
    ∃ D : ℕ, chartRatio I J ^ D * c ∈ chartRing S x I := by
  classical
  have := (algebraMap S Ω).domain_nontrivial
  obtain ⟨i₀, hi₀⟩ := I.2.1
  have hx₀ : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  obtain ⟨a, ha⟩ : ∃ a, I.1.card = a + 1 :=
    ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos I.2.1.card_pos).symm⟩
  obtain ⟨b, hb⟩ : ∃ b, J.1.card = b + 1 :=
    ⟨J.1.card - 1, (Nat.succ_pred_eq_of_pos J.2.1.card_pos).symm⟩
  have hI0 : ∏ i ∈ I.1, x i ≠ 0 := xProd_ne_zero I

  have hWmul : ∀ w w' : Ω, (∃ D : ℕ, chartRatio I J ^ D * w ∈ chartRing S x I) →
      (∃ D : ℕ, chartRatio I J ^ D * w' ∈ chartRing S x I) →
      ∃ D : ℕ, chartRatio I J ^ D * (w * w') ∈ chartRing S x I := by
    rintro w w' ⟨D, hD⟩ ⟨D', hD'⟩
    refine ⟨D + D', ?_⟩
    have e : chartRatio I J ^ (D + D') * (w * w') =
        (chartRatio I J ^ D * w) * (chartRatio I J ^ D' * w') := by ring
    rw [e]; exact mul_mem hD hD'

  have hgen : ∀ i ∈ (unionChart I J).1,
      ∃ D : ℕ, chartRatio I J ^ D * (x i₀ / x i) ∈ chartRing S x I := by
    intro i hi
    by_cases hiI : i ∈ I.1
    · refine ⟨0, X i₀, X i, 1, X_mem_monos hiI, isHomogeneous_X S i₀, isHomogeneous_X S i, ?_⟩
      simp
    · have hiJ : i ∈ J.1 := by
        rcases Finset.mem_union.mp hi with h | h
        · exact absurd h hiI
        · exact h
      have hxi : x i ≠ 0 := (mem_support x).mp (J.2.2 hiJ)
      have hcard : (J.1.erase i).card = b := by rw [Finset.card_erase_of_mem hiJ, hb]; rfl
      refine ⟨1, X i₀ * monoProd (J.1.erase i) * monoProd J.1 ^ a, monoProd I.1 ^ J.1.card,
        (a + 1) * (b + 1), pow_mem (monoProd_mem_monos subset_rfl) _, ?_, ?_, ?_⟩
      · have h1 := ((isHomogeneous_X S i₀).mul (monoProd_isHomogeneous (S := S) (J.1.erase i))).mul
          ((monoProd_isHomogeneous (S := S) J.1).pow a)
        rw [hcard, hb] at h1
        convert h1 using 1
        ring
      · have h1 := (monoProd_isHomogeneous (S := S) I.1).pow J.1.card
        rw [ha, hb] at h1
        rw [hb]
        exact h1
      · have hJ : ∏ l ∈ J.1, x l = x i * ∏ l ∈ J.1.erase i, x l :=
          (Finset.mul_prod_erase J.1 (fun l => x l) hiJ).symm
        simp only [chartRatio, xProd, map_mul, map_pow, aeval_X, aeval_monoProd, ha, hJ]
        field_simp
        ring
  have hmon : ∀ s ∈ monos (S := S) (unionChart I J).1, ∃ e : ℕ, s.IsHomogeneous e ∧
      ∃ D : ℕ, chartRatio I J ^ D * (x i₀ ^ e / aeval x s) ∈ chartRing S x I := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨i, hi, rfl⟩ := hs
      refine ⟨1, isHomogeneous_X S i, ?_⟩
      rw [pow_one, aeval_X]
      exact hgen i hi
    | one =>
      refine ⟨0, isHomogeneous_one _ _, 0, ?_⟩
      rw [pow_zero, map_one, div_one, pow_zero, one_mul]
      exact one_mem _
    | mul s s' _ _ h h' =>
      obtain ⟨e, he, hW⟩ := h
      obtain ⟨e', he', hW'⟩ := h'
      refine ⟨e + e', he.mul he', ?_⟩
      have : x i₀ ^ (e + e') / aeval x (s * s') =
          (x i₀ ^ e / aeval x s) * (x i₀ ^ e' / aeval x s') := by
        rw [pow_add, map_mul, mul_div_mul_comm]
      rw [this]
      exact hWmul _ _ hW hW'
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hc
  obtain ⟨e', he', D, hD⟩ := hmon s hs
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (unionChart I J) hs
  have hee : e' = e := he'.inj_right hse (fun h => hs0 (by rw [h, map_zero]))
  subst hee
  refine ⟨D, ?_⟩
  have hf0 : aeval x f / x i₀ ^ e' ∈ chartRing S x I :=
    ⟨f, X i₀ ^ e', e', pow_mem (X_mem_monos hi₀) _, hf, isHomogeneous_X_pow i₀ e',
      by rw [map_pow, aeval_X]⟩
  have : chartRatio I J ^ D * (aeval x f / aeval x s) =
      (aeval x f / x i₀ ^ e') * (chartRatio I J ^ D * (x i₀ ^ e' / aeval x s)) := by
    field_simp
  rw [this]
  exact mul_mem hf0 hD

theorem exists_pow_mul_mem_sub (M : SubFamily S x Ω) (I J : Chart x) {y : Ω}
    (hy : y ∈ M.sub (unionChart I J)) : ∃ D : ℕ, chartRatio I J ^ D * y ∈ M.sub I := by
  obtain ⟨a, ha, hay⟩ := (M.mem_iff I (unionChart I J) (subset_unionChart_left I J) y).mp hy
  obtain ⟨v, hv⟩ := ha.exists_left_inv
  obtain ⟨D, hD⟩ := exists_pow_mul_mem I J v.2
  refine ⟨D, ?_⟩
  have hv' : (v : Ω) * (a : Ω) = 1 := congrArg Subtype.val hv
  have e : chartRatio I J ^ D * y = (⟨_, hD⟩ : chartRing S x I) • ((a : Ω) • y) := by
    rw [chartRing_smul_def, smul_eq_mul]
    calc chartRatio I J ^ D * y = chartRatio I J ^ D * ((v : Ω) * a) * y := by rw [hv', mul_one]
      _ = _ := by ring
  rw [e]
  exact Submodule.smul_mem _ _ hay

theorem exists_pow_mul_mem_of_eq (L : LineBundle S x) {F : SubSystem S x Ω}
    (hL : L.toSubSystem = F) (I J : Chart x) {y : Ω} (hy : y ∈ F.sub (unionChart I J)) :
    ∃ D : ℕ, chartRatio I J ^ D * y ∈ F.sub I := by
  subst hL
  exact exists_pow_mul_mem_sub L.toSubFamily I J hy

theorem tensorProd_powBundle (Q H : LineBundle S x) (c : ℕ) :
    (Q.tensorProd (H.powBundle c)).toSubSystem = Q.toSubSystem.twist (H.toSubSystem.pow c) := by
  change Q.toSubSystem.twist (H.powBundle c).toSubSystem = _
  rw [LineBundle.powBundle_toSubSystem]

def ampleSubalg (H : SubSystem S x Ω) (m : ℕ) (h : Ω) (I : Chart x)
    (hh : h ∈ (H.pow m).sub I) : Subalgebra S Ω where
  carrier := ampleChart H m h I
  mul_mem' := by
    rintro a b ⟨n, hn⟩ ⟨n', hn'⟩
    refine ⟨n + n', ?_⟩
    have e : a * b * h ^ (n + n') = a * h ^ n * (b * h ^ n') := by ring
    rw [e, Nat.mul_add]
    exact AmpleTwistLocal.mul_mem_pow H I hn _ hn'
  add_mem' := by
    rintro a b ⟨n, hn⟩ ⟨n', hn'⟩
    refine ⟨n + n', ?_⟩
    have e : (a + b) * h ^ (n + n') = a * h ^ n * h ^ n' + b * h ^ n' * h ^ n := by ring
    rw [e, Nat.mul_add]
    refine add_mem (AmpleTwistLocal.mul_mem_pow H I hn _ (AmpleTwistLocal.pow_mem_pow H I hh n')) ?_
    rw [Nat.add_comm (m * n)]
    exact AmpleTwistLocal.mul_mem_pow H I hn' _ (AmpleTwistLocal.pow_mem_pow H I hh n)
  algebraMap_mem' s := ⟨0, by
    rw [pow_zero, mul_one, Nat.mul_zero]
    change _ ∈ twistMod S x 0 I
    have := Submodule.smul_mem (twistMod S x 0 I) (algebraMap S (chartRing S x I) s)
      (one_mem_twistMod_zero I)
    rwa [chartRing_smul_def, mul_one] at this⟩

theorem mem_ampleSubalg_of_mem_chartRing {H : SubSystem S x Ω} {m : ℕ} {h : Ω} {I : Chart x}
    (hh : h ∈ (H.pow m).sub I) {a : Ω} (ha : a ∈ chartRing S x I) : a ∈ ampleSubalg H m h I hh :=
  ⟨0, by
    rw [pow_zero, mul_one, Nat.mul_zero]
    change _ ∈ twistMod S x 0 I
    have := Submodule.smul_mem (twistMod S x 0 I) (⟨a, ha⟩ : chartRing S x I)
      (one_mem_twistMod_zero I)
    rwa [chartRing_smul_def, mul_one] at this⟩

theorem ampleChart_mono {H : SubSystem S x Ω} {m : ℕ} {h : Ω} {I K : Chart x} (hIK : I.1 ⊆ K.1)
    {a : Ω} (ha : a ∈ ampleChart H m h I) : a ∈ ampleChart H m h K :=
  let ⟨n, hn⟩ := ha
  ⟨n, (H.pow (m * n)).mono I K hIK _ hn⟩

theorem ampleChart_eventually {H : SubSystem S x Ω} {m : ℕ} {h : Ω} {I : Chart x}
    (hh : h ∈ (H.pow m).sub I) {a : Ω} (ha : a ∈ ampleChart H m h I) :
    ∀ᶠ e in Filter.atTop, a * h ^ e ∈ (H.pow (m * e)).sub I := by
  obtain ⟨n, hn⟩ := ha
  refine Filter.eventually_atTop.mpr ⟨n, fun e he => ?_⟩
  have h1 := AmpleTwistLocal.mul_mem_pow H I hn _ (AmpleTwistLocal.pow_mem_pow H I hh (e - n))
  have e1 : a * h ^ n * h ^ (e - n) = a * h ^ e := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' he]
  have e2 : m * n + m * (e - n) = m * e := by rw [← Nat.mul_add, Nat.add_sub_cancel' he]
  rwa [e1, e2] at h1

theorem ampleChart_loc (H : LineBundle S x) {m : ℕ} {h : Ω} (I J : Chart x) {a : Ω}
    (ha : a ∈ ampleChart H.toSubSystem m h (unionChart I J)) :
    ∃ D : ℕ, chartRatio I J ^ D * a ∈ ampleChart H.toSubSystem m h I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨D, hD⟩ := exists_pow_mul_mem_of_eq (H.powBundle (m * n))
    (LineBundle.powBundle_toSubSystem H _) I J hn
  exact ⟨D, n, by rw [mul_assoc]; exact hD⟩

def secChart (Q H : SubSystem S x Ω) (m b : ℕ) (h : Ω) (I : Chart x) : Set Ω :=
  {z | ∃ k : ℕ, z * h ^ k ∈ (Q.twist (H.pow (b + m * k))).sub I}

theorem secChart_smul {Q H : SubSystem S x Ω} {m b : ℕ} {h : Ω} {I : Chart x} {a z : Ω}
    (ha : a ∈ ampleChart H m h I) (hz : z ∈ secChart Q H m b h I) : a * z ∈ secChart Q H m b h I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨k, hk⟩ := hz
  refine ⟨k + n, ?_⟩
  have h1 := AmpleTwistLocal.mul_mem_twist_pow Q H I hk hn
  have e1 : z * h ^ k * (a * h ^ n) = a * z * h ^ (k + n) := by ring
  have e2 : b + m * k + m * n = b + m * (k + n) := by rw [Nat.mul_add, Nat.add_assoc]
  rwa [e1, e2] at h1

theorem secChart_mono {Q H : SubSystem S x Ω} {m b : ℕ} {h : Ω} {I K : Chart x} (hIK : I.1 ⊆ K.1)
    {z : Ω} (hz : z ∈ secChart Q H m b h I) : z ∈ secChart Q H m b h K :=
  let ⟨k, hk⟩ := hz
  ⟨k, (Q.twist (H.pow (b + m * k))).mono I K hIK _ hk⟩

theorem mem_secChart_of_mem {Q H : SubSystem S x Ω} {m b : ℕ} {h : Ω} {I : Chart x} {z : Ω}
    (hz : z ∈ (Q.twist (H.pow b)).sub I) : z ∈ secChart Q H m b h I :=
  ⟨0, by rwa [pow_zero, mul_one, Nat.mul_zero, Nat.add_zero]⟩

theorem secChart_loc (Q H : LineBundle S x) {m b : ℕ} {h : Ω} (I J : Chart x) {z : Ω}
    (hz : z ∈ secChart Q.toSubSystem H.toSubSystem m b h (unionChart I J)) :
    ∃ D : ℕ, chartRatio I J ^ D * z ∈ secChart Q.toSubSystem H.toSubSystem m b h I := by
  obtain ⟨k, hk⟩ := hz
  obtain ⟨D, hD⟩ := exists_pow_mul_mem_of_eq (Q.tensorProd (H.powBundle (b + m * k)))
    (tensorProd_powBundle Q H _) I J hk
  exact ⟨D, k, by rw [mul_assoc]; exact hD⟩

theorem secChart_le_span (Q H : LineBundle S x) (m b : ℕ) {h : Ω} (h0 : h ≠ 0) (J : Chart x)
    (hh : h ∈ (H.pow m).sub J) {G : Set Ω}
    (hG : Submodule.span (chartRing S x J) G = (Q.twist (H.pow b)).sub J) {z : Ω}
    (hz : z ∈ secChart Q.toSubSystem H.toSubSystem m b h J) :
    z ∈ Submodule.span (ampleSubalg H.toSubSystem m h J hh) G := by
  obtain ⟨k, hk⟩ := hz
  have hF : ∀ y ∈ (Q.twist (H.pow b)).sub J,
      y ∈ Submodule.span (ampleSubalg H.toSubSystem m h J hh) G := by
    intro y hy
    rw [← hG] at hy
    induction hy using Submodule.span_induction with
    | mem g hg => exact Submodule.subset_span hg
    | zero => exact Submodule.zero_mem _
    | add _ _ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
    | smul a y _ h1 =>
      rw [chartRing_smul_def]
      exact Submodule.smul_mem _
        (⟨a, mem_ampleSubalg_of_mem_chartRing hh a.2⟩ : ampleSubalg H.toSubSystem m h J hh) h1
  have hdec : (Q.twist (H.pow (b + m * k))).sub J =
      (H.pow (m * k)).sub J * (Q.twist (H.pow b)).sub J := by
    simp only [SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub, pow_add]
    ring
  rw [hdec] at hk
  have key : ∀ y ∈ (H.pow (m * k)).sub J * (Q.twist (H.pow b)).sub J,
      y / h ^ k ∈ Submodule.span (ampleSubalg H.toSubSystem m h J hh) G := by
    intro y hy
    refine Submodule.mul_induction_on hy (fun w hw f hf => ?_) (fun y y' h1 h2 => ?_)
    · have hB : w / h ^ k ∈ ampleSubalg H.toSubSystem m h J hh :=
        ⟨k, by rwa [div_mul_cancel₀ _ (pow_ne_zero _ h0)]⟩
      have : w * f / h ^ k = (⟨_, hB⟩ : ampleSubalg H.toSubSystem m h J hh) • f := by
        rw [Subalgebra.smul_def, smul_eq_mul]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (hF f hf)
    · rw [add_div]
      exact Submodule.add_mem _ h1 h2
  have := key _ hk
  rwa [mul_div_cancel_right₀ _ (pow_ne_zero _ h0)] at this

end AmpleAffineGen

open AmpleAffineGen in

theorem AmpleAffineGen.proof : AmpleAffineGen.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q b j h0
  classical
  have hh : ∀ I : Chart x, A.h j ∈ (H.pow A.m).sub I := fun I =>
    (Submodule.mem_iInf _).mp (A.mem_secs j) I
  obtain ⟨n, a, c, J, ha, hc, hsum, hrat⟩ := A.affine j h0
  have haB : ∀ k I, a k ∈ ampleSubalg H.toSubSystem A.m (A.h j) I (hh I) := fun k I =>
    Set.mem_iInter.mp (ha k) I
  have hcB : ∀ k I, c k ∈ ampleSubalg H.toSubSystem A.m (A.h j) I (hh I) := fun k I =>
    Set.mem_iInter.mp (hc k) I

  have hfg : ∀ k, ∃ G : Finset Ω,
      Submodule.span (chartRing S x (J k)) (G : Set Ω) = (Q.twist (H.pow b)).sub (J k) := by
    intro k
    obtain ⟨G, hG⟩ := (Q.tensorProd (H.powBundle b)).fg (J k)
    refine ⟨G, ?_⟩
    rw [hG, tensorProd_powBundle]
  choose G hG using hfg

  have stepA : ∀ k, ∀ γ ∈ G k, ∀ I : Chart x, ∀ᶠ M in Filter.atTop,
      c k ^ M * γ ∈ secChart Q.toSubSystem H.toSubSystem A.m b (A.h j) I := by
    intro k γ hγ I
    have h1 : γ ∈ secChart Q.toSubSystem H.toSubSystem A.m b (A.h j) (unionChart I (J k)) :=
      secChart_mono (subset_unionChart_right I (J k))
        (mem_secChart_of_mem (by rw [← hG k]; exact Submodule.subset_span hγ))
    obtain ⟨D, hD⟩ := secChart_loc Q H I (J k) h1
    obtain ⟨e, he⟩ := hrat k I
    have h2 : c k ^ (e * D) * γ ∈ secChart Q.toSubSystem H.toSubSystem A.m b (A.h j) I := by
      have := secChart_smul
        (pow_mem (show _ ∈ ampleSubalg H.toSubSystem A.m (A.h j) I (hh I) from he) D) hD
      rwa [show c k ^ e * (xProd I ^ (J k).1.card / xProd (J k) ^ I.1.card) = c k ^ e * chartRatio (J k) I
        from rfl, pow_mul_cancel (chartRatio_mul_chartRatio I (J k))] at this
    refine Filter.eventually_atTop.mpr ⟨e * D, fun M hM => ?_⟩
    have : c k ^ M * γ = c k ^ (M - e * D) * (c k ^ (e * D) * γ) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hM]
    rw [this]
    exact secChart_smul (pow_mem (hcB k I) _) h2
  have stepA' : ∀ᶠ M in Filter.atTop, ∀ k, ∀ γ ∈ G k, ∀ I : Chart x,
      c k ^ M * γ ∈ secChart Q.toSubSystem H.toSubSystem A.m b (A.h j) I := by
    rw [Filter.eventually_all]
    intro k
    rw [Filter.eventually_all_finset]
    intro γ hγ
    rw [Filter.eventually_all]
    exact stepA k γ hγ
  obtain ⟨M₀, hM₀⟩ := stepA'.exists

  set T : Finset Ω := Finset.univ.biUnion fun k => (G k).image fun γ => c k ^ M₀ * γ with hTdef
  have hTmem : ∀ k, ∀ γ ∈ G k, c k ^ M₀ * γ ∈ T := fun k γ hγ =>
    Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image.mpr ⟨γ, hγ, rfl⟩⟩
  have hT : ∀ t ∈ T, ∀ I : Chart x, t ∈ secChart Q.toSubSystem H.toSubSystem A.m b (A.h j) I := by
    intro t ht I
    obtain ⟨k, -, ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp ht
    exact hM₀ k γ hγ I

  have stepC : ∀ (I : Chart x) (z : Ω),
      z ∈ secChart Q.toSubSystem H.toSubSystem A.m b (A.h j) I →
      z ∈ Submodule.span (ampleSubalg H.toSubSystem A.m (A.h j) I (hh I)) (T : Set Ω) := by
    intro I z hz
    set B := ampleSubalg H.toSubSystem A.m (A.h j) I (hh I) with hBdef
    set V := Submodule.span B (T : Set Ω) with hVdef
    have hk : ∀ k, ∃ E, c k ^ E * z ∈ V := by
      intro k
      obtain ⟨D, hD⟩ := secChart_loc Q H (J k) I
        (secChart_mono (subset_unionChart_right (J k) I) hz)
      have hspan := secChart_le_span Q H A.m b h0 (J k) (hh (J k)) (hG k) hD
      have hP : ∀ y ∈ Submodule.span (ampleSubalg H.toSubSystem A.m (A.h j) (J k) (hh (J k)))
          (G k : Set Ω), ∃ E, c k ^ E * y ∈ V := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem γ hγ => exact ⟨M₀, Submodule.subset_span (by exact_mod_cast hTmem k γ hγ)⟩
        | zero => exact ⟨0, by rw [mul_zero]; exact V.zero_mem⟩
        | add y y' _ _ h1 h2 =>
          obtain ⟨E, hE⟩ := h1
          obtain ⟨E', hE'⟩ := h2
          refine ⟨E + E', ?_⟩
          have : c k ^ (E + E') * (y + y') =
              (⟨c k ^ E', pow_mem (hcB k I) _⟩ : B) • (c k ^ E * y) +
              (⟨c k ^ E, pow_mem (hcB k I) _⟩ : B) • (c k ^ E' * y') := by
            simp only [Subalgebra.smul_def, smul_eq_mul]
            ring
          rw [this]
          exact V.add_mem (V.smul_mem _ hE) (V.smul_mem _ hE')
        | smul β y _ h1 =>
          obtain ⟨E, hE⟩ := h1
          obtain ⟨D', hD'⟩ := ampleChart_loc H I (J k)
            (ampleChart_mono (subset_unionChart_right I (J k)) β.2)
          obtain ⟨e, he⟩ := hrat k I
          have hβ : c k ^ (e * D') * β ∈ B := by
            have := mul_mem (pow_mem (show _ ∈ B from he) D') (show _ ∈ B from hD')
            rwa [show c k ^ e * (xProd I ^ (J k).1.card / xProd (J k) ^ I.1.card) =
              c k ^ e * chartRatio (J k) I from rfl,
              pow_mul_cancel (chartRatio_mul_chartRatio I (J k))] at this
          refine ⟨e * D' + E, ?_⟩
          have : c k ^ (e * D' + E) * (β • y) = (⟨_, hβ⟩ : B) • (c k ^ E * y) := by
            simp only [Subalgebra.smul_def, smul_eq_mul]
            ring
          rw [this]
          exact V.smul_mem _ hE
      obtain ⟨E, hE⟩ := hP _ hspan
      refine ⟨E, ?_⟩
      have hr : chartRatio I (J k) ^ D ∈ B :=
        mem_ampleSubalg_of_mem_chartRing (hh I) (pow_mem (chartRatio_mem I (J k)) D)
      have : c k ^ E * z = (⟨_, hr⟩ : B) • (c k ^ E * (chartRatio (J k) I ^ D * z)) := by
        rw [Subalgebra.smul_def, smul_eq_mul]
        calc c k ^ E * z = c k ^ E * (chartRatio (J k) I * chartRatio I (J k)) ^ D * z := by
              rw [chartRatio_mul_chartRatio, one_pow, mul_one]
          _ = _ := by ring
      rw [this]
      exact V.smul_mem _ hE
    choose E hE using hk
    set E₀ := Finset.univ.sup E with hE₀
    have hbig : ∀ k, c k ^ E₀ * z ∈ V := by
      intro k
      have hle : E k ≤ E₀ := Finset.le_sup (Finset.mem_univ k)
      have : c k ^ E₀ * z = (⟨c k ^ (E₀ - E k), pow_mem (hcB k I) _⟩ : B) • (c k ^ E k * z) := by
        rw [Subalgebra.smul_def, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [this]
      exact V.smul_mem _ (hE k)

    let cB : Fin n → B := fun k => ⟨c k, hcB k I⟩
    let aB : Fin n → B := fun k => ⟨a k, haB k I⟩
    have hspan : Ideal.span (Set.range cB) = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have : (1 : B) = ∑ k, aB k * cB k := Subtype.ext (by simp [aB, cB, hsum])
      rw [this]
      exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
    have hpow := Ideal.span_pow_eq_top _ hspan E₀
    have hle : Ideal.span ((fun y : B => y ^ E₀) '' Set.range cB) ≤
        V.comap (LinearMap.toSpanSingleton B Ω z) := by
      rw [Ideal.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.toSpanSingleton_apply,
        Subalgebra.smul_def, smul_eq_mul, SubmonoidClass.coe_pow, cB]
      exact hbig k
    rw [hpow, top_le_iff] at hle
    have h1 : (1 : B) ∈ V.comap (LinearMap.toSpanSingleton B Ω z) := hle ▸ Submodule.mem_top
    simpa using h1
  refine ⟨T.card, fun t => (T.equivFin.symm t : Ω), fun t I => hT _ (T.equivFin.symm t).2 I,
    fun I z k hz => ?_⟩
  obtain ⟨f, hf⟩ := Submodule.mem_span_finset'.mp (stepC I z ⟨k, hz⟩)
  have hev : ∀ᶠ e in Filter.atTop, ∀ t : Fin T.card,
      (f (T.equivFin.symm t) : Ω) * A.h j ^ e ∈ (H.pow (A.m * e)).sub I := by
    rw [Filter.eventually_all]
    intro t
    exact ampleChart_eventually (hh I) (f (T.equivFin.symm t)).2
  obtain ⟨e, he⟩ := hev.exists
  refine ⟨e, fun t => (f (T.equivFin.symm t) : Ω), he, ?_⟩
  rw [← hf, ← Equiv.sum_comp T.equivFin.symm]
  simp only [Subalgebra.smul_def, smul_eq_mul]

end

end GroundTheory.Heights₂.Heights.Kleiman
