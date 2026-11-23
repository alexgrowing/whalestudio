import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MatMapTmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Chevalley

theorem isArtinianRing_quotient_maximalIdeal_pow (B : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (k : ℕ) : IsArtinianRing (B ⧸ maximalIdeal B ^ k) := by
  have hdim : Ring.KrullDimLE 0 (B ⧸ maximalIdeal B ^ k) := by
    rw [Ring.krullDimLE_zero_iff]
    intro Q hQ
    have h1 : maximalIdeal B ^ k ≤ Q.comap (Ideal.Quotient.mk (maximalIdeal B ^ k)) :=
      fun x hx ↦ by simp [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    have h2 : maximalIdeal B = Q.comap (Ideal.Quotient.mk (maximalIdeal B ^ k)) :=
      (maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.IsPrime.le_of_pow_le h1)
    haveI h3 : (Q.comap (Ideal.Quotient.mk (maximalIdeal B ^ k))).IsMaximal :=
      h2 ▸ maximalIdeal.isMaximal B
    have h4 := Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk (maximalIdeal B ^ k)) Ideal.Quotient.mk_surjective
      (m := Q.comap (Ideal.Quotient.mk (maximalIdeal B ^ k))) (by simpa using h1)
    rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h4
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

theorem isArtinian_quotient_smul_top (B M : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M] (k : ℕ) :
    IsArtinian B (M ⧸ (maximalIdeal B ^ k • (⊤ : Submodule B M))) := by
  haveI := isArtinianRing_quotient_maximalIdeal_pow B k
  haveI : Module.Finite (B ⧸ maximalIdeal B ^ k) (M ⧸ (maximalIdeal B ^ k • (⊤ : Submodule B M))) :=
    Module.Finite.of_restrictScalars_finite B (B ⧸ maximalIdeal B ^ k) _
  exact isArtinian_of_surjective_algebraMap (R := B ⧸ maximalIdeal B ^ k) Ideal.Quotient.mk_surjective

end GlobalTheory.Chevalley

namespace GlobalTheory.Chevalley

theorem exists_le_sup_maximalIdeal_pow_smul (B M ι : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M] (K : ι → Submodule B M)
    [Nonempty ι] (hK : Directed (· ≥ ·) K) (k : ℕ) :
    ∃ i, ∀ j, K i ≤ K j ⊔ maximalIdeal B ^ k • (⊤ : Submodule B M) := by
  set P := maximalIdeal B ^ k • (⊤ : Submodule B M)
  haveI := isArtinian_quotient_smul_top B M k
  obtain ⟨_, ⟨i, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal
    (Set.range fun i ↦ (K i).map P.mkQ) (Set.range_nonempty _)
  refine ⟨i, fun j ↦ ?_⟩
  obtain ⟨l, hli, hlj⟩ := hK i j
  have hle : (K l).map P.mkQ ≤ (K i).map P.mkQ := Submodule.map_mono hli
  have heq : (K l).map P.mkQ = (K i).map P.mkQ := by
    by_contra hne
    exact hmin _ ⟨l, rfl⟩ (lt_of_le_of_ne hle hne)
  have h2 : (K i).map P.mkQ ≤ (K j).map P.mkQ := heq ▸ Submodule.map_mono hlj
  have h3 := Submodule.comap_mono (f := P.mkQ) h2
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ] at h3
  exact le_sup_right.trans (h3.trans (by rw [sup_comm]))

end GlobalTheory.Chevalley

namespace GlobalTheory.Chevalley

open TensorProduct Polynomial IsLocalRing in
private theorem isArtinian_quotient_maximalIdeal_pow_succ_smul (B M : Type) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (n : ℕ) : IsArtinian B (M ⧸ (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M))) := by
  have hmin : maximalIdeal B ∈ (maximalIdeal B ^ (n + 1)).minimalPrimes := by
    refine ⟨⟨(maximalIdeal.isMaximal B).isPrime, Ideal.pow_le_self (Nat.succ_ne_zero n)⟩, ?_⟩
    rintro q ⟨hq, hle⟩ -
    exact hq.le_of_pow_le hle
  have : IsArtinianRing (B ⧸ maximalIdeal B ^ (n + 1)) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  exact isArtinian_of_surjective_algebraMap
    (Ideal.Quotient.mk_surjective (I := maximalIdeal B ^ (n + 1)))

open TensorProduct Polynomial IsLocalRing in
private theorem mem_of_forall_mem_sup_maximalIdeal_pow_smul (B M : Type) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (K : Submodule B M) (x : M)
    (h : ∀ n, x ∈ K ⊔ maximalIdeal B ^ n • (⊤ : Submodule B M)) : x ∈ K := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M ⧸ K) (maximalIdeal B)
    (maximalIdeal.isMaximal B).ne_top
  have hx : K.mkQ x ∈ ⨅ n, maximalIdeal B ^ n • (⊤ : Submodule B (M ⧸ K)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (h n)
    have hmap : (maximalIdeal B ^ n • (⊤ : Submodule B M)).map K.mkQ ≤
        maximalIdeal B ^ n • (⊤ : Submodule B (M ⧸ K)) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    have hzq := hmap (Submodule.mem_map_of_mem hz)
    have hy0 : K.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hy
    rw [map_add, hy0, zero_add]
    exact hzq
  rw [hbot, Submodule.mem_bot] at hx
  exact (Submodule.Quotient.mk_eq_zero K).mp hx

open TensorProduct Polynomial IsLocalRing in
private theorem exists_limit_of_sub_mem_maximalIdeal_pow_smul (B M : Type) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [AddCommGroup M]
    [Module B M] [Module.Finite B M] (s : ℕ) (y : ℕ → M)
    (hy : ∀ k, y (k + 1) - y k ∈ maximalIdeal B ^ (s + k) • (⊤ : Submodule B M)) :
    ∃ x, ∀ k, x - y k ∈ maximalIdeal B ^ (s + k) • (⊤ : Submodule B M) := by
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := B) (M := M)
  have hlift : ∀ (J : Ideal B) (z : M), z ∈ J • (⊤ : Submodule B M) →
      ∃ c : Fin m → B, (∀ l, c l ∈ J) ∧ ∑ l, c l • g l = z := by
    intro J z hz
    rw [← hg, Submodule.mem_ideal_smul_span_iff_exists_sum] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, ha, (Finsupp.sum_fintype a (fun i c => c • g i) fun i => zero_smul B (g i)).symm⟩
  choose c hcI hcsum using fun k => hlift _ _ (hy k)
  obtain ⟨S, hS⟩ : ∃ S : Fin m → ℕ → B, ∀ l n, S l n = ∑ k ∈ Finset.range n, c k l :=
    ⟨_, fun _ _ => rfl⟩
  have hSdiff : ∀ l n p, n ≤ p → S l p - S l n ∈ maximalIdeal B ^ (s + n) := by
    intro l n p hnp
    rw [hS, hS, ← Finset.sum_range_add_sum_Ico _ hnp, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun k hk => ?_
    have hk' := (Finset.mem_Ico.mp hk).1
    exact Ideal.pow_le_pow_right (by omega) (hcI k l)
  have hprec : IsPrecomplete (maximalIdeal B) B := inferInstance
  have hlim : ∀ l, ∃ L, ∀ n, S l n - L ∈ maximalIdeal B ^ (s + n) := by
    intro l
    obtain ⟨L, hL⟩ := hprec.prec (f := S l) (fun {a b} hab => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, Submodule.neg_mem_iff]
      exact Ideal.pow_le_pow_right (by omega) (hSdiff l a b hab))
    refine ⟨L, fun n => ?_⟩
    have h1 := hL (s + n)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
    have h2 := hSdiff l n (s + n) (by omega)
    have e : S l n - L = (S l (s + n) - L) - (S l (s + n) - S l n) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.pow_le_pow_right (by omega) h1) h2
  choose L hL using hlim
  refine ⟨y 0 + ∑ l, L l • g l, fun k => ?_⟩
  have htel : ∑ l, S l k • g l = y k - y 0 := by
    simp only [hS, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp_rw [hcsum]
    exact Finset.sum_range_sub y k
  have e : y 0 + ∑ l, L l • g l - y k = -∑ l, (S l k - L l) • g l := by
    simp only [sub_smul, Finset.sum_sub_distrib, htel]
    abel
  rw [e, Submodule.neg_mem_iff]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem_smul (hL l k) Submodule.mem_top

open TensorProduct Polynomial IsLocalRing in

theorem _root_.GlobalTheory.Chevalley.exists_le_maximalIdeal_pow_smul_of_directed :
    ∀ (B M ι : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [IsAdicComplete (maximalIdeal B) B] [AddCommGroup M] [Module B M] [Module.Finite B M]
      (K : ι → Submodule B M), Nonempty ι → Directed (· ≥ ·) K → (⨅ i, K i) = ⊥ →
      ∀ N : ℕ, ∃ i, K i ≤ maximalIdeal B ^ N • (⊤ : Submodule B M) := by
  intro B M ι _ _ _ _ _ _ _ K hne hdir hbot N
  haveI := hne
  have hmin : ∀ n, ∃ j, ∀ i, K j ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) ≤
      K i ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n
    haveI := isArtinian_quotient_maximalIdeal_pow_succ_smul B M n
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ :=
      (wellFounded_lt (α := Submodule B (M ⧸ (maximalIdeal B ^ (n + 1) •
        (⊤ : Submodule B M))))).has_min
        (Set.range fun i => (K i).map (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ)
        (Set.range_nonempty _)
    refine ⟨j, fun i => ?_⟩
    obtain ⟨k, hki, hkj⟩ := hdir i j
    have hle := Submodule.map_mono (f := (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ) hkj
    have heq : (K k).map (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ =
        (K j).map (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ := by
      by_contra hne'
      exact hj _ ⟨k, rfl⟩ (lt_of_le_of_ne hle hne')
    have hji := Submodule.map_mono (f := (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ) hki
    rw [heq] at hji
    have hc := Submodule.comap_mono (f := (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ) hji
    rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ] at hc
    rwa [sup_comm (K j), sup_comm (K i)]
  choose j hj using hmin
  by_contra hcon
  push_neg at hcon
  have hE_step : ∀ n, ∀ x ∈ K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M),
      ∃ x' ∈ K (j (n + 1)) ⊔ maximalIdeal B ^ (n + 1 + 1) • (⊤ : Submodule B M),
        x - x' ∈ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hj n (j (n + 1)) hx)
    exact ⟨a, Submodule.mem_sup_left ha, by simpa using hb⟩
  have hE_anti : ∀ n, K (j (n + 1)) ⊔ maximalIdeal B ^ (n + 1 + 1) • (⊤ : Submodule B M) ≤
      K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := fun n =>
    (hj (n + 1) (j n)).trans
      (sup_le_sup_left (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) _)
  have hE_mono : ∀ n p, n ≤ p → K (j p) ⊔ maximalIdeal B ^ (p + 1) • (⊤ : Submodule B M) ≤
      K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n p hnp
    induction hnp with
    | refl => exact le_rfl
    | step _ ih => exact (hE_anti _).trans ih
  have hE_zero : ∀ x, (∀ n, x ∈ K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)) →
      x = 0 := by
    intro x hx
    have hmem : x ∈ ⨅ i, K i := Submodule.mem_iInf _ |>.mpr fun i =>
      mem_of_forall_mem_sup_maximalIdeal_pow_smul B M (K i) x fun n => by
        have hle : K i ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) ≤
            K i ⊔ maximalIdeal B ^ n • (⊤ : Submodule B M) :=
          sup_le_sup_left (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))) _
        exact hle (hj n i (hx n))
    rwa [hbot, Submodule.mem_bot] at hmem
  have hnot : ¬ K (j N) ⊔ maximalIdeal B ^ (N + 1) • (⊤ : Submodule B M) ≤
      maximalIdeal B ^ (N + 1) • (⊤ : Submodule B M) := fun h =>
    hcon (j N) ((le_sup_left.trans h).trans
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))))
  obtain ⟨x0, hx0, hx0P⟩ := SetLike.not_le_iff_exists.mp hnot
  choose f hf1 hf2 using hE_step
  let y : (k : ℕ) → {x // x ∈ K (j (N + k)) ⊔ maximalIdeal B ^ (N + k + 1) • (⊤ : Submodule B M)} :=
    fun k => Nat.rec (motive := fun k =>
        {x // x ∈ K (j (N + k)) ⊔ maximalIdeal B ^ (N + k + 1) • (⊤ : Submodule B M)})
      ⟨x0, hx0⟩ (fun k z => ⟨f (N + k) z.1 z.2, hf1 _ _ _⟩) k
  have hy_succ : ∀ k, (y (k + 1)).1 = f (N + k) (y k).1 (y k).2 := fun k => rfl
  obtain ⟨x, hx⟩ := exists_limit_of_sub_mem_maximalIdeal_pow_smul B M (N + 1)
    (fun k => (y k).1) (fun k => by
      have e : N + 1 + k = N + k + 1 := by omega
      rw [hy_succ, e, ← neg_sub, Submodule.neg_mem_iff]
      exact hf2 (N + k) (y k).1 (y k).2)
  have hxE : ∀ n, x ∈ K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n
    have e : N + 1 + n = N + n + 1 := by omega
    have hd := hx n
    rw [e] at hd
    have hk := Submodule.add_mem _ (y n).2 (Submodule.mem_sup_right hd)
    rw [add_sub_cancel] at hk
    exact hE_mono n (N + n) (by omega) hk
  have hx0' := hE_zero x hxE
  apply hx0P
  have h0 := hx 0
  rw [hx0', zero_sub, Submodule.neg_mem_iff] at h0
  exact h0

end GlobalTheory.Chevalley
