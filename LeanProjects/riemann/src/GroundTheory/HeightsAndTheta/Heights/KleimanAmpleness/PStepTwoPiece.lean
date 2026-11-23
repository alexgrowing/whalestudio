import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StepTwoPieceSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace StepTwo.Piece

section CechIso

variable {n : ℕ} {U : Finset (Fin n)} {R : Type*} [CommRing R]

theorem subsingleton_H_one_iff {G : Cell U → Type*} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
    {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J} :
    Subsingleton (Cech.H G ρ 1) ↔
      ∀ z : Cech.Cochain G 1, Cech.d G ρ 1 z = 0 → ∃ w : Cech.Cochain G 0, Cech.d G ρ 0 w = z := by
  unfold Cech.H
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
  constructor
  · intro h z hz
    exact h (LinearMap.mem_ker.mpr hz)
  · intro h z hz
    exact h z (LinearMap.mem_ker.mp hz)

theorem H_subsingleton_of_zero {G : Cell U → Type*} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
    (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J) (h : ∀ I, Subsingleton (G I)) (i : ℕ) :
    Subsingleton (Cech.H G ρ i) := by
  have h2 : Subsingleton (Cech.Cochain G i) := by
    unfold Cech.Cochain; infer_instance
  unfold Cech.H
  refine Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun z _ => ?_)
  have hz : z = 0 := Subtype.ext (h2.elim _ _)
  rw [hz]
  exact Submodule.zero_mem _

theorem subsingleton_H_one_of_equiv {G G' : Cell U → Type*} [∀ I, AddCommGroup (G I)]
    [∀ I, Module R (G I)] [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
    {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J} {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}
    (φ : ∀ I, G I ≃ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m))
    (hG : Subsingleton (Cech.H G ρ 1)) : Subsingleton (Cech.H G' ρ' 1) := by
  rw [subsingleton_H_one_iff] at hG ⊢
  intro z hz
  let ψ : ∀ I, G' I →ₗ[R] G I := fun I => ((φ I).symm : G' I →ₗ[R] G I)
  let χ : ∀ I, G I →ₗ[R] G' I := fun I => ((φ I) : G I →ₗ[R] G' I)
  have hψ : ∀ I J h m, ψ J (ρ' I J h m) = ρ I J h (ψ I m) := by
    intro I J h m
    apply (φ J).injective
    change φ J ((φ J).symm (ρ' I J h m)) = φ J (ρ I J h ((φ I).symm m))
    rw [hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hχ : ∀ I J h m, χ J (ρ I J h m) = ρ' I J h (χ I m) := hφ
  obtain ⟨w, hw⟩ := hG (Cech.mapC ψ 1 z) (by rw [← Cech.mapC_d ψ hψ 1 z, hz, map_zero])
  refine ⟨Cech.mapC χ 0 w, ?_⟩
  rw [← Cech.mapC_d χ hχ 0 w, hw]
  funext I
  change φ I.1 ((φ I.1).symm (z I)) = z I
  exact LinearEquiv.apply_symm_apply _ _

end CechIso

section Chart

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem twist_sub_def {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
    (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Submodule.span (chartRing S x I) {z | ∃ q ∈ Q.sub I, ∃ y ∈ F.sub I, z = q • y} :=
  rfl

theorem zpow_mem_twistMod (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (k : ℤ) :
    x i ^ k ∈ twistMod S x k I := by
  rw [twistMod_eq_span k I hi]
  exact Submodule.mem_span_singleton_self _

theorem exists_eq_of_mem_twistMod (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) {k : ℤ} {z : Ω}
    (hz : z ∈ twistMod S x k I) : ∃ b : chartRing S x I, z = (b : Ω) * x i ^ k := by
  rw [twistMod_eq_span k I hi, Submodule.mem_span_singleton] at hz
  obtain ⟨b, rfl⟩ := hz
  exact ⟨b, rfl⟩

theorem mul_mem_twist_twistSys (Q : SubSystem S x Ω) (I : Chart x) {k m : ℤ} {z o : Ω}
    (hz : z ∈ (Q.twist (twistSys S x k)).sub I) (ho : o ∈ twistMod S x m I) :
    z * o ∈ (Q.twist (twistSys S x (k + m))).sub I := by
  rw [SubSystem.twist_sub_eq_mul_of_line] at hz ⊢
  rw [← twistSys_sub_mul k m I]
  have h : z * o ∈ ((twistSys S x k).sub I * Q.sub I) * (twistSys S x m).sub I :=
    Submodule.mul_mem_mul hz ho
  rwa [mul_assoc, mul_comm (Q.sub I), ← mul_assoc] at h

theorem zpow_mul_mem_twist (Q : SubSystem S x Ω) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (k : ℤ)
    {q : Ω} (hq : q ∈ Q.sub I) : x i ^ k * q ∈ (Q.twist (twistSys S x k)).sub I :=
  Submodule.subset_span ⟨x i ^ k, zpow_mem_twistMod I hi k, q, hq, rfl⟩

theorem mul_mem_twistMod_of_dual (Q : SubSystem S x Ω) (I : Chart x) {k : ℤ} {q' z : Ω}
    (hq' : ∀ a ∈ Q.sub I, q' * a ∈ chartRing S x I) (hz : z ∈ (Q.twist (twistSys S x k)).sub I) :
    q' * z ∈ twistMod S x k I := by
  rw [SubSystem.twist_sub_eq_mul_of_line] at hz
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem o ho a ha =>
    rw [mul_comm o a, ← mul_assoc]
    exact (twistMod S x k I).smul_mem (⟨q' * a, hq' a ha⟩ : chartRing S x I) ho
  | add a _ b _ ha hb =>
    rw [mul_add]
    exact add_mem ha hb

theorem one_mem_idealMod {pp : Ideal (Poly S N)} (I : Chart x) {j : Fin (N + 1)} (hj : j ∈ I.1)
    (hX : (X j : Poly S N) ∈ pp) : (1 : Ω) ∈ idealMod (x := x) pp I :=
  Submodule.subset_span ⟨X j, X j, 1, hX, X_mem_monos hj, isHomogeneous_X S j, isHomogeneous_X S j, by
    rw [aeval_X, div_self ((mem_support x).mp (I.2.2 hj))]⟩

theorem mem_twist_idealSys_of_X_mem (F : SubSystem S x Ω) {pp : Ideal (Poly S N)} (I : Chart x)
    {j : Fin (N + 1)} (hj : j ∈ I.1) (hX : (X j : Poly S N) ∈ pp) {q : Ω} (hq : q ∈ F.sub I) :
    q ∈ (F.twist (idealSys x pp)).sub I :=
  Submodule.subset_span ⟨1, one_mem_idealMod I hj hX, q, hq, (one_smul Ω q).symm⟩

end Chart

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

omit [IsScalarTower S Ω E] in

theorem zpow_smul_mem_tilde (M : FinGradedSub (S := S) (x := x) E) (I : Chart x) {i : Fin (N + 1)}
    (hi : i ∈ I.1) {a : ℤ} {n : E} (hn : n ∈ M.piece a) : x i ^ (-a) • n ∈ M.tilde 0 I := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · refine Submodule.subset_span ⟨n, X i ^ k, k, k, pow_mem (X_mem_monos hi) k, isHomogeneous_X_pow i k, hn,
      sub_self _, ?_⟩
    rw [map_pow, aeval_X, zpow_neg, zpow_natCast]
  · have h1 := M.smul_mem k (-k) (X i ^ k) n (isHomogeneous_X_pow i k) hn
    rw [neg_add_cancel] at h1
    refine Submodule.subset_span ⟨aeval x (X i ^ k : Poly S N) • n, 1, 0, 0, one_mem _, isHomogeneous_one _ _,
      h1, by simp, ?_⟩
    rw [map_one, inv_one, one_smul, neg_neg, map_pow, aeval_X, zpow_natCast]

omit [IsScalarTower S Ω E] in

theorem exists_of_mem_tilde (M : FinGradedSub (S := S) (x := x) E) (I : Chart x) {c : ℤ} {y : E}
    (hy : y ∈ M.tilde c I) : ∃ (t : Poly S N) (d : ℕ), t ∈ monos I.1 ∧ t.IsHomogeneous d ∧
      ∃ n ∈ M.piece (d + c), y = (aeval x t)⁻¹ • n := by
  unfold FinGradedSub.tilde at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩ := hy
    exact ⟨s, e, hs, hse, m, by rwa [show (e : ℤ) + c = a by omega], rfl⟩
  | zero => exact ⟨1, 0, one_mem _, isHomogeneous_one _ _, 0, Submodule.zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨t, d, ht, htd, n, hn, rfl⟩ := hy
    obtain ⟨t', d', ht', htd', n', hn', rfl⟩ := hz
    have h0 := eval_ne_zero_of_mem_monos I ht
    have h0' := eval_ne_zero_of_mem_monos I ht'
    refine ⟨t * t', d + d', mul_mem ht ht', htd.mul htd', aeval x t' • n + aeval x t • n', ?_, ?_⟩
    · have h1 := M.smul_mem d' (d + c) t' n htd' hn
      have h2 := M.smul_mem d (d' + c) t n' htd hn'
      refine add_mem ?_ ?_
      · convert h1 using 2; push_cast; ring
      · convert h2 using 2; push_cast; ring
    · rw [smul_add, smul_smul, smul_smul, map_mul]
      congr 2
      · field_simp
      · field_simp
  | smul a y _ hy =>
    obtain ⟨t, d, ht, htd, n, hn, rfl⟩ := hy
    obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
    have h0 := eval_ne_zero_of_mem_monos I ht
    have hs0 := eval_ne_zero_of_mem_monos I hs
    refine ⟨s * t, e + d, mul_mem hs ht, hse.mul htd, aeval x f • n, ?_, ?_⟩
    · convert M.smul_mem e (d + c) f n hf hn using 2; push_cast; ring
    · change (a : Ω) • ((aeval x t)⁻¹ • n) = _
      rw [ha, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp

omit [IsScalarTower S Ω E] in

theorem zpow_mul_smul_mem_tilde (M : FinGradedSub (S := S) (x := x) E) (Q : SubSystem S x Ω) (I : Chart x)
    {i : Fin (N + 1)} (hi : i ∈ I.1) {c : ℤ} {q' : Ω} (hq' : ∀ a ∈ Q.sub I, q' * a ∈ chartRing S x I) {y : E}
    (hy : y ∈ ((M.tildeSys 0).twist (Q.twist (twistSys S x c))).sub I) :
    (x i ^ (-c) * q') • y ∈ M.tilde 0 I := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [twist_sub_def] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, m, hm, rfl⟩ := hy
    obtain ⟨b, hb⟩ := exists_eq_of_mem_twistMod I hi (mul_mem_twistMod_of_dual Q I hq' hw)
    rw [smul_smul, mul_assoc, hb]
    have h : x i ^ (-c) * ((b : Ω) * x i ^ c) = b := by
      rw [mul_left_comm, ← zpow_add₀ hxi, neg_add_cancel, zpow_zero, mul_one]
    rw [h]
    exact (M.tilde 0 I).smul_mem b hm
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul a y _ hy =>
    change (x i ^ (-c) * q') • ((a : Ω) • y) ∈ _
    rw [smul_smul, mul_comm _ (a : Ω), ← smul_smul]
    exact (M.tilde 0 I).smul_mem a hy

end Tilde

section Step

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (N₀ N₁ : FinGradedSub (S := S) (x := x) E) {g : E} {e : ℤ} (pp : Ideal (Poly S N)) (Q : SubSystem S x Ω)
  (c : ℤ)

omit [IsScalarTower S Ω E] in

theorem smul_mem_of_mem (hg : g ∈ N₁.piece e) (I : Chart x) {q : Ω}
    (hq : q ∈ (Q.twist (twistSys S x (c - e))).sub I) :
    q • g ∈ ((N₁.tildeSys 0).twist (Q.twist (twistSys S x c))).sub I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have h1 := mul_mem_twist_twistSys Q I hq (zpow_mem_twistMod I hi e)
  rw [sub_add_cancel] at h1
  refine Submodule.subset_span ⟨q * x i ^ e, h1, x i ^ (-e) • g, zpow_smul_mem_tilde N₁ I hi hg, ?_⟩
  rw [smul_smul, mul_assoc, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero, mul_one]

omit [IsScalarTower S Ω E] in

theorem smul_mem_of_mem_ideal
    (hiff : ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d)))
    (I : Chart x) {z : Ω} (hz : z ∈ ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)).sub I) :
    z • g ∈ ((N₀.tildeSys 0).twist (Q.twist (twistSys S x c))).sub I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [twist_sub_def] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨α, hα, w, hw, rfl⟩ := hz
    have hw' := mul_mem_twist_twistSys Q I hw (zpow_mem_twistMod I hi e)
    rw [sub_add_cancel] at hw'
    change α ∈ idealMod pp I at hα
    unfold idealMod at hα
    induction hα using Submodule.span_induction with
    | mem α hα =>
      obtain ⟨f, s, d, hf, hs, hfd, hsd, rfl⟩ := hα
      have hs0 := eval_ne_zero_of_mem_monos I hs
      have hfg := (hiff f d hfd).mp hf
      have hu : x i ^ d / aeval x s ∈ chartRing S x I :=
        ⟨X i ^ d, s, d, hs, isHomogeneous_X_pow i d, hsd, by rw [map_pow, aeval_X]⟩
      refine Submodule.subset_span ⟨(x i ^ d / aeval x s) * (w * x i ^ e),
        (Q.twist (twistSys S x c)).sub I |>.smul_mem (⟨_, hu⟩ : chartRing S x I) hw',
        x i ^ (-(e + d)) • aeval x f • g, zpow_smul_mem_tilde N₀ I hi hfg, ?_⟩
      rw [smul_smul, smul_smul, smul_eq_mul]
      congr 1
      rw [zpow_neg, zpow_add₀ hxi, zpow_natCast]
      field_simp
    | zero => rw [zero_smul, zero_smul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [add_smul, add_smul]; exact add_mem ha hb
    | smul a α _ hα =>
      change (((a : Ω) * α) • w) • g ∈ _
      rw [smul_eq_mul, mul_assoc, mul_smul]
      exact Submodule.smul_mem _ a hα
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | smul a z _ hz =>
    change ((a : Ω) • z) • g ∈ _
    rw [smul_assoc]
    exact Submodule.smul_mem _ a hz

def approx (I : Chart x) (F : Submodule (chartRing S x I) Ω) (G₀ : Submodule (chartRing S x I) E) (g : E) :
    Submodule (chartRing S x I) E where
  carrier := {y | ∃ q ∈ F, y - q • g ∈ G₀}
  add_mem' := by
    rintro y y' ⟨q, hq, hy⟩ ⟨q', hq', hy'⟩
    refine ⟨q + q', add_mem hq hq', ?_⟩
    have h : y + y' - (q + q') • g = (y - q • g) + (y' - q' • g) := by rw [add_smul]; abel
    rw [h]
    exact add_mem hy hy'
  zero_mem' := ⟨0, zero_mem _, by rw [zero_smul, sub_zero]; exact zero_mem _⟩
  smul_mem' := by
    rintro a y ⟨q, hq, hy⟩
    refine ⟨a • q, F.smul_mem a hq, ?_⟩
    have h : a • y - (a • q) • g = a • (y - q • g) := by
      rw [smul_sub]
      congr 1
      change ((a : Ω) * q) • g = (a : Ω) • (q • g)
      rw [mul_smul]
    rw [h]
    exact G₀.smul_mem a hy

theorem exists_sub_mem
    (hN : ∀ c, N₁.piece c = N₀.piece c ⊔ Submodule.span S
      {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • g})
    (I : Chart x) {y : E} (hy : y ∈ ((N₁.tildeSys 0).twist (Q.twist (twistSys S x c))).sub I) :
    y ∈ approx I ((Q.twist (twistSys S x (c - e))).sub I)
      (((N₀.tildeSys 0).twist (Q.twist (twistSys S x c))).sub I) g := by
  rw [twist_sub_def] at hy
  refine Submodule.span_le.mpr ?_ hy
  rintro _ ⟨w, hw, m, hm, rfl⟩
  change m ∈ N₁.tilde 0 I at hm
  unfold FinGradedSub.tilde at hm
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨n, s, a, d, hs, hsd, hn, had, rfl⟩ := hm
    have hs0 := eval_ne_zero_of_mem_monos I hs
    rw [hN a] at hn
    obtain ⟨n₀, hn₀, n₁, hn₁, rfl⟩ := Submodule.mem_sup.mp hn
    clear hn
    rw [smul_add, smul_add]
    refine add_mem ⟨0, zero_mem _, ?_⟩ ?_
    · rw [zero_smul, sub_zero]
      exact Submodule.subset_span ⟨w, hw, (aeval x s)⁻¹ • n₀,
        Submodule.subset_span ⟨n₀, s, a, d, hs, hsd, hn₀, had, rfl⟩, rfl⟩
    · induction hn₁ using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨f, d', hf, hd', rfl⟩ := hz
        have ho : aeval x f / aeval x s ∈ twistMod S x (-e) I :=
          Submodule.subset_span ⟨f, s, d, d', hs, hf, hsd, by omega, rfl⟩
        have h1 := mul_mem_twist_twistSys Q I hw ho
        rw [← sub_eq_add_neg] at h1
        refine ⟨w * (aeval x f / aeval x s), h1, ?_⟩
        have h2 : w • (aeval x s)⁻¹ • aeval x f • g - (w * (aeval x f / aeval x s)) • g = 0 := by
          rw [smul_smul, smul_smul, sub_eq_zero]
          congr 1
          field_simp
        rw [h2]
        exact zero_mem _
      | zero => rw [smul_zero, smul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [smul_add, smul_add]; exact add_mem ha hb
      | smul r z _ hz =>
        rw [smul_comm (aeval x s)⁻¹ r z, smul_comm w r]
        rw [← algebraMap_smul Ω r]
        exact Submodule.smul_mem _ (algebraMap S (chartRing S x I) r) hz
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a m _ hm =>
    change w • ((a : Ω) • m) ∈ _
    rw [smul_comm]
    exact Submodule.smul_mem _ a hm

end Step

section Kernel

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  (N₀ : FinGradedSub (S := S) (x := x) E) {g : E} {e : ℤ} {pp : Ideal (Poly S N)} (Q : LineBundle S x) (c : ℤ)

theorem mem_of_smul_mem (hpp : pp.IsPrime)
    (hiff : ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d)))
    (I : Chart x) {q : Ω} (hq : q ∈ (Q.twist (twistSys S x (c - e))).sub I)
    (hqg : q • g ∈ ((N₀.tildeSys 0).twist (Q.twist (twistSys S x c))).sub I) :
    q ∈ ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)).sub I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  by_cases hX : ∃ j ∈ I.1, (X j : Poly S N) ∈ pp
  · obtain ⟨j, hj, hXj⟩ := hX
    exact mem_twist_idealSys_of_X_mem _ I hj hXj hq
  push Not at hX
  have hmonos : ∀ t ∈ monos (S := S) I.1, t ∉ pp := by
    intro t ht
    induction ht using Submonoid.closure_induction with
    | mem a ha =>
      obtain ⟨j, hj, rfl⟩ := ha
      exact hX j hj
    | one => exact (Ideal.ne_top_iff_one pp).mp hpp.ne_top
    | mul a b _ _ ha hb =>
      intro hab
      rcases hpp.mem_or_mem hab with h | h
      exacts [ha h, hb h]
  obtain ⟨Q', hQ'⟩ := Q.invertible I
  have h1 : (1 : Ω) ∈ Q.sub I * Q' := by
    rw [hQ']
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have key : ∀ z ∈ Q.sub I * Q', z * q ∈ ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)).sub I := by
    intro z hz
    induction hz using Submodule.mul_induction_on' with
    | mem_mul_mem q₁ hq₁ q₂ hq₂ =>
      have hdual : ∀ a ∈ Q.sub I, q₂ * a ∈ chartRing S x I := by
        intro a ha
        have h2 : q₂ * a ∈ Q.sub I * Q' := by
          rw [mul_comm q₂ a]
          exact Submodule.mul_mem_mul ha hq₂
        rw [hQ'] at h2
        obtain ⟨b, hb⟩ := Submodule.mem_one.mp h2
        rw [← hb]
        exact b.2
      obtain ⟨β, hβ⟩ := exists_eq_of_mem_twistMod I hi (mul_mem_twistMod_of_dual _ I hdual hq)
      have hin := zpow_mul_smul_mem_tilde N₀ _ I hi hdual hqg
      have heq : x i ^ (-c) * q₂ * q = β * x i ^ (-e) := by
        rw [mul_assoc, hβ, mul_left_comm, ← zpow_add₀ hxi, show -c + (c - e) = -e by ring]
      have hβg : ((β : Ω) * x i ^ (-e)) • g ∈ N₀.tilde 0 I := by
        rw [← heq, mul_smul]
        exact hin
      have hβp : (β : Ω) ∈ idealMod (x := x) pp I := by
        obtain ⟨t, d', ht, htd, n, hn, hnt⟩ := exists_of_mem_tilde N₀ I hβg
        obtain ⟨h, s, d, hs, hh, hsd, hβs⟩ := β.2
        obtain ⟨k, l, hkl⟩ : ∃ k l : ℕ, e = k - l := ⟨e.toNat, (-e).toNat, by omega⟩
        have hs0 := eval_ne_zero_of_mem_monos I hs
        have ht0 := eval_ne_zero_of_mem_monos I ht
        have hz : x i ^ (-e) = x i ^ l / x i ^ k := by
          rw [hkl, neg_sub, zpow_sub₀ hxi, zpow_natCast, zpow_natCast]
        have heq2 : aeval x (h * t * X i ^ l) • g = aeval x (s * X i ^ k) • n := by
          calc aeval x (h * t * X i ^ l) • g
              = (aeval x s * aeval x t * x i ^ k) • (((β : Ω) * x i ^ (-e)) • g) := by
                rw [smul_smul, hβs, hz]
                congr 1
                simp only [map_mul, map_pow, aeval_X]
                field_simp
            _ = (aeval x s * aeval x t * x i ^ k) • ((aeval x t)⁻¹ • n) := by rw [hnt]
            _ = aeval x (s * X i ^ k) • n := by
                rw [smul_smul]
                congr 1
                simp only [map_mul, map_pow, aeval_X]
                field_simp
        have hmem : aeval x (h * t * X i ^ l) • g ∈ N₀.piece (e + ↑(d + d' + l)) := by
          have h2 := N₀.smul_mem (d + k) (d' + 0) (s * X i ^ k) n (hsd.mul (isHomogeneous_X_pow i k)) hn
          rw [heq2]
          convert h2 using 2
          push_cast
          omega
        have hp := (hiff _ _ ((hh.mul htd).mul (isHomogeneous_X_pow i l))).mpr hmem
        rcases hpp.mem_or_mem hp with h3 | h3
        · rcases hpp.mem_or_mem h3 with h4 | h4
          · rw [hβs]
            exact Submodule.subset_span ⟨h, s, d, h4, hs, hh, hsd, rfl⟩
          · exact absurd h4 (hmonos t ht)
        · exact absurd h3 (hmonos _ (pow_mem (X_mem_monos hi) l))
      refine Submodule.subset_span ⟨β, hβp, x i ^ (c - e) * q₁, zpow_mul_mem_twist Q.toSubSystem I hi _ hq₁, ?_⟩
      rw [smul_eq_mul, mul_assoc, hβ]
      ring
    | add a _ b _ ha hb =>
      rw [add_mul]
      exact add_mem ha hb
  simpa using key 1 h1

end Kernel

section Iso

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (N₀ N₁ : FinGradedSub (S := S) (x := x) E) {g : E} {e : ℤ} {pp : Ideal (Poly S N)} (Q : LineBundle S x)
  (c : ℤ)

def gMap (hg : g ∈ N₁.piece e) (I : Chart x) :
    (Q.twist (twistSys S x (c - e))).sub I →ₗ[S] ((N₁.tildeSys 0).twist (Q.twist (twistSys S x c))).sub I where
  toFun q := ⟨(q : Ω) • g, smul_mem_of_mem N₁ Q.toSubSystem c hg I q.2⟩
  map_add' a b := Subtype.ext (add_smul (a : Ω) b g)
  map_smul' r a := Subtype.ext (smul_assoc r (a : Ω) g)

def gBar (hg : g ∈ N₁.piece e)
    (hiff : ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d)))
    (I : Chart x) :
    ((Q.twist (twistSys S x (c - e))).sub I ⧸ SubSystem.quotSub (Q.twist (twistSys S x (c - e)))
      ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)) I) →ₗ[S]
    (((N₁.tildeSys 0).twist (Q.twist (twistSys S x c))).sub I ⧸ SubSystem.quotSub
      ((N₁.tildeSys 0).twist (Q.twist (twistSys S x c))) ((N₀.tildeSys 0).twist (Q.twist (twistSys S x c))) I) :=
  (SubSystem.quotSub _ _ I).mapQ (SubSystem.quotSub _ _ I) (gMap N₁ Q c hg I)
    (fun _ hy => smul_mem_of_mem_ideal N₀ pp Q.toSubSystem c hiff I hy)

theorem gBar_mk (hg : g ∈ N₁.piece e)
    (hiff : ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d)))
    (I : Chart x) (y : (Q.twist (twistSys S x (c - e))).sub I) :
    gBar N₀ N₁ Q c hg hiff I (Submodule.Quotient.mk y) = Submodule.Quotient.mk (gMap N₁ Q c hg I y) :=
  rfl

theorem gBar_bijective (hpp : pp.IsPrime) (hg : g ∈ N₁.piece e)
    (hN : ∀ c, N₁.piece c = N₀.piece c ⊔ Submodule.span S
      {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • g})
    (hiff : ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d)))
    (I : Chart x) : Function.Bijective (gBar N₀ N₁ Q c hg hiff I) := by
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    rw [gBar_mk, Submodule.Quotient.mk_eq_zero] at ha
    rw [Submodule.Quotient.mk_eq_zero]
    exact mem_of_smul_mem N₀ Q c hpp hiff I y.2 ha
  · intro b
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    obtain ⟨q, hq, hyq⟩ := exists_sub_mem N₀ N₁ Q.toSubSystem c hN I y.2
    refine ⟨Submodule.Quotient.mk ⟨q, hq⟩, ?_⟩
    rw [gBar_mk, Submodule.Quotient.eq]
    have h := neg_mem hyq
    rw [neg_sub] at h
    exact h

theorem gBar_comm (hg : g ∈ N₁.piece e)
    (hiff : ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d)))
    (I J : Chart x) (h : I.1 ⊆ J.1) (m) :
    gBar N₀ N₁ Q c hg hiff J (SubSystem.quotRes _ _ I J h m) =
      SubSystem.quotRes _ _ I J h (gBar N₀ N₁ Q c hg hiff I m) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rfl

end Iso

theorem proof : Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ N₀ N₁ g e pp hpp _ _ hg hN hiff Q c hH
  have hsrc : Subsingleton (SubSystem.quotH (Q.twist (twistSys S x (c - e)))
      ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)) 1) := by
    by_cases hrel : ∃ j, (X j : Poly S N) ∉ pp
    · exact hH hrel
    · push Not at hrel
      unfold SubSystem.quotH
      refine H_subsingleton_of_zero _ (fun I => ?_) 1
      obtain ⟨i, hi⟩ := I.2.1
      exact Submodule.Quotient.subsingleton_iff.mpr
        (eq_top_iff.mpr fun y _ => mem_twist_idealSys_of_X_mem _ I hi (hrel i) y.2)
  unfold SubSystem.quotH at hsrc ⊢
  exact subsingleton_H_one_of_equiv
    (fun I => LinearEquiv.ofBijective (gBar N₀ N₁ Q c hg hiff I) (gBar_bijective N₀ N₁ Q c hpp hg hN hiff I))
    (fun I J h m => gBar_comm N₀ N₁ Q c hg hiff I J h m) hsrc

end StepTwo.Piece

end

end GroundTheory.Heights₂.Heights.Kleiman
