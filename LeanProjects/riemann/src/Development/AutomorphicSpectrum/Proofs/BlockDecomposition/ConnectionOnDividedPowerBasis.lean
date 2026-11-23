import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.QDerivative

variable {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]

lemma map_mem_of_repr (e : Module.Basis ℕ B M) (P : Submodule B M) (L : M →ₗ[B] M) (z : M)
    (h : ∀ k, L (e.repr z k • e k) ∈ P) : L z ∈ P := by
  have hz := e.linearCombination_repr z
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hz
  rw [← hz, map_sum]
  exact P.sum_mem fun k _ => h k

def grade (e : Module.Basis ℕ B M) (I : ℕ → Ideal B) (r : ℕ) : Submodule B M where
  carrier := {z | ∀ k, e.repr z k ∈ I (r - k)}
  add_mem' := by
    intro a b ha hb k
    simpa using (I (r - k)).add_mem (ha k) (hb k)
  zero_mem' := by
    intro k
    simp
  smul_mem' := by
    intro c x hx k
    simpa using (I (r - k)).mul_mem_left c (hx k)

lemma smul_mem_grade (e : Module.Basis ℕ B M) (I : ℕ → Ideal B) (r j : ℕ) {a : B}
    (ha : a ∈ I (r - j)) : a • e j ∈ grade e I r := by
  intro k
  by_cases h : j = k
  · subst h
    simpa using ha
  · simp [Finsupp.single_apply, h]

noncomputable def shift (e : Module.Basis ℕ B M) : Module.End B M :=
  e.constr B (fun k => e (k + 1))

@[simp] lemma shift_e (e : Module.Basis ℕ B M) (k : ℕ) : shift e (e k) = e (k + 1) := by
  simp [shift, Module.Basis.constr_basis]

noncomputable def raise (e : Module.Basis ℕ B M) : Module.End B M :=
  e.constr B (fun k => ((k + 1 : ℕ) : B) • e (k + 1))

@[simp] lemma raise_e (e : Module.Basis ℕ B M) (k : ℕ) :
    raise e (e k) = ((k + 1 : ℕ) : B) • e (k + 1) := by
  simp [raise, Module.Basis.constr_basis]

lemma raise_pow_e (e : Module.Basis ℕ B M) (n k : ℕ) :
    (raise e ^ n) (e k) = (((k + 1).ascFactorial n : ℕ) : B) • e (k + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, raise_e, smul_smul,
      Nat.ascFactorial_succ, ← add_assoc]
    congr 1
    push_cast
    ring

lemma pow_sub_mem (P : Submodule B M) (V U : Module.End B M) (hP : ∀ y ∈ P, V y ∈ P)
    (h : ∀ z, (V - U) z ∈ P) (n : ℕ) (z : M) : (V ^ n - U ^ n) z ∈ P := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have : (V ^ (n + 1) - U ^ (n + 1)) z = V ((V ^ n - U ^ n) z) + (V - U) ((U ^ n) z) := by
      simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, map_sub]
      abel
    rw [this]
    exact P.add_mem (hP _ (ih z)) (h _)

lemma exists_nilpotent_ideal (p q : B) (ν : ℕ → B) (hp : IsNilpotent p) (hq : IsNilpotent (q - 1))
    (hν : ∀ m, 2 ≤ m → IsNilpotent (ν m)) (hN : ∃ N, ∀ m, N ≤ m → ν m = 0) :
    ∃ J : Ideal B, IsNilpotent J ∧ p ∈ J ∧ q - 1 ∈ J ∧ ∀ m, 2 ≤ m → ν m ∈ J := by
  obtain ⟨N, hN⟩ := hN
  let S : Set B := {p, q - 1} ∪ ν '' {m | 2 ≤ m ∧ m < N}
  have hS : S.Finite :=
    (Set.toFinite _).union (((Set.finite_Iio N).subset fun m hm => hm.2).image ν)
  refine ⟨Ideal.span S, ?_, Ideal.subset_span (by simp [S]), Ideal.subset_span (by simp [S]), ?_⟩
  · rw [Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span hS), Ideal.span_le]
    rintro x (hx | ⟨m, hm, rfl⟩)
    · rcases hx with rfl | rfl
      · exact hp
      · exact hq
    · exact hν m hm.1
  · intro m hm
    by_cases hmN : m < N
    · exact Ideal.subset_span (Or.inr ⟨m, ⟨hm, hmN⟩, rfl⟩)
    · rw [hN m (not_lt.mp hmN)]
      exact Ideal.zero_mem _

lemma nilpotent_of_pow_mem (J : Ideal B) (hJ : IsNilpotent J) (A : Module.End B M)
    (h : ∀ z, A z ∈ J • (⊤ : Submodule B M)) : IsNilpotent A := by
  obtain ⟨L, hL⟩ := hJ
  have key : ∀ j z, (A ^ j) z ∈ (J ^ j) • (⊤ : Submodule B M) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro z
      rw [pow_succ A j, Module.End.mul_apply, pow_succ' J j, Submodule.mul_smul]
      have hy := h z
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro r hr n _
        rw [map_smul]
        exact Submodule.smul_mem_smul hr (ih n)
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
  refine ⟨L, ?_⟩
  ext z
  have := key L z
  rw [hL] at this
  simpa using this

lemma D_succ (e : Module.Basis ℕ B M) (q : B) (ν : ℕ → B) (D : M →ₗ[B] M) (hν1 : ν 1 = 1)
    (hD : ∀ k, D (e k) = (∑ i ∈ Finset.range k, q ^ i) • e k +
      ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • e (k - (m + 1))) (k : ℕ) :
    D (e (k + 1)) = (∑ i ∈ Finset.range (k + 1), q ^ i) • e (k + 1) +
      (∑ m ∈ Finset.range k, (ν (m + 2) * q ^ (k - (m + 1))) • e (k - (m + 1)) + q ^ k • e k) := by
  rw [hD (k + 1)]
  congr 1
  rw [Finset.sum_range_succ']
  simp [hν1, Nat.add_sub_add_right]

lemma sub_raise_mem (e : Module.Basis ℕ B M) (J : Ideal B) (q : B) (ν : ℕ → B) (D : M →ₗ[B] M)
    (hqJ : q - 1 ∈ J) (hνJ : ∀ m, 2 ≤ m → ν m ∈ J) (hν1 : ν 1 = 1)
    (hD : ∀ k, D (e k) = (∑ i ∈ Finset.range k, q ^ i) • e k +
      ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • e (k - (m + 1))) (z : M) :
    ((D * shift e - 1) - raise e) z ∈ J • (⊤ : Submodule B M) := by
  have hqpow : ∀ i : ℕ, q ^ i - 1 ∈ J := by
    intro i
    have := sub_dvd_pow_sub_pow q 1 i
    rw [one_pow] at this
    exact Ideal.mem_of_dvd J this hqJ
  have hs : ∀ {c : B} (x : M), c ∈ J → c • x ∈ J • (⊤ : Submodule B M) :=
    fun x hc => Submodule.smul_mem_smul hc trivial
  refine map_mem_of_repr e _ _ z fun k => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  have h : ((D * shift e - 1) - raise e) (e k) =
      (∑ i ∈ Finset.range (k + 1), (q ^ i - 1)) • e (k + 1) +
      (∑ m ∈ Finset.range k, (ν (m + 2) * q ^ (k - (m + 1))) • e (k - (m + 1)) +
        (q ^ k - 1) • e k) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply, shift_e, raise_e, Module.End.one_apply,
      D_succ e q ν D hν1 hD k, Finset.sum_sub_distrib, sub_smul, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, one_smul]
    abel
  rw [h]
  refine Submodule.add_mem _ (hs _ (J.sum_mem fun i _ => hqpow i)) (Submodule.add_mem _ ?_ (hs _ (hqpow k)))
  exact Submodule.sum_mem _ fun m _ => hs _ (J.mul_mem_right _ (hνJ _ (by omega)))

lemma raise_pow_mem (e : Module.Basis ℕ B M) (J : Ideal B) (p : ℕ) (hp : p ≠ 0) (hpJ : (p : B) ∈ J)
    (z : M) : (raise e ^ p) z ∈ J • (⊤ : Submodule B M) := by
  refine map_mem_of_repr e _ _ z fun k => ?_
  rw [map_smul, raise_pow_e]
  refine Submodule.smul_mem _ _ (Submodule.smul_mem_smul ?_ trivial)
  have hd : p ∣ (k + 1).ascFactorial p :=
    (Nat.dvd_factorial (Nat.pos_of_ne_zero hp) le_rfl).trans (Nat.factorial_dvd_ascFactorial _ _)
  exact Ideal.mem_of_dvd J (Nat.cast_dvd_cast hd) hpJ

lemma mul_shift_mem_grade (e : Module.Basis ℕ B M) (I : ℕ → Ideal B) (q : B) (ν : ℕ → B)
    (D : M →ₗ[B] M) (hmul : ∀ a c, I a * I c ≤ I (a + c)) (hanti : ∀ a c, a ≤ c → I c ≤ I a)
    (hνI : ∀ m, ν (m + 1) ∈ I m)
    (hD : ∀ k, D (e k) = (∑ i ∈ Finset.range k, q ^ i) • e k +
      ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • e (k - (m + 1)))
    (r : ℕ) (z : M) (hz : z ∈ grade e I r) : (D * shift e) z ∈ grade e I r := by
  refine map_mem_of_repr e _ _ z fun k => ?_
  have ha := hz k
  generalize e.repr z k = a at ha
  rw [map_smul, Module.End.mul_apply, shift_e, hD (k + 1), smul_add, Finset.smul_sum, smul_smul]
  refine Submodule.add_mem _ (smul_mem_grade e I r _ ?_) (Submodule.sum_mem _ fun m hm => ?_)
  · exact hanti _ _ (by omega) (Ideal.mul_mem_right _ _ ha)
  · rw [smul_smul]
    refine smul_mem_grade e I r _ ?_
    rw [← mul_assoc]
    refine Ideal.mul_mem_right _ _ ?_
    have hm' : m < k + 1 := Finset.mem_range.mp hm
    exact hanti _ _ (by omega) (hmul _ _ (Ideal.mul_mem_mul ha (hνI m)))

lemma shift_mem_grade (e : Module.Basis ℕ B M) (I : ℕ → Ideal B) (r : ℕ) (z : M)
    (hz : z ∈ grade e I r) : shift e z ∈ grade e I (r + 1) := by
  refine map_mem_of_repr e _ _ z fun k => ?_
  rw [map_smul, shift_e]
  refine smul_mem_grade e I (r + 1) (k + 1) ?_
  rw [Nat.add_sub_add_right]
  exact hz k

lemma exists_eq_add_shift (e : Module.Basis ℕ B M) (z : M) :
    ∃ (c : B) (z' : M), z = c • e 0 + shift e z' := by
  have h : (LinearMap.id : M →ₗ[B] M) z ∈
      Submodule.span B {e 0} ⊔ LinearMap.range (shift e) := by
    refine map_mem_of_repr e _ _ z fun k => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    cases k with
    | zero => exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    | succ k => exact Submodule.mem_sup_right ⟨e k, shift_e e k⟩
  obtain ⟨a, ha, b, ⟨z', rfl⟩, hab⟩ := Submodule.mem_sup.mp h
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  exact ⟨c, z', hab.symm⟩

theorem ker_and_surjective : ∀ {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (e : Module.Basis ℕ B M) (I : ℕ → Ideal B) (p : ℕ) (q : B) (ν : ℕ → B) (D : M →ₗ[B] M), p ≠ 0 → IsNilpotent (p : B) → IsNilpotent (q - 1) → (∀ a c, I a * I c ≤ I (a + c)) → (∀ a c, a ≤ c → I c ≤ I a) → ν 1 = 1 → (∀ m, ν (m + 1) ∈ I m) → (∀ m, 2 ≤ m → IsNilpotent (ν m)) → (∃ N, ∀ m, N ≤ m → ν m = 0) → (∀ k, D (e k) = (∑ i ∈ Finset.range k, q ^ i) • e k + ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • e (k - (m + 1))) → (∀ z, D z = 0 → ∃ c : B, z = c • e 0) ∧ ∀ (r : ℕ) (z : M), (∀ k, e.repr z k ∈ I (r - k)) → ∃ y, (∀ k, e.repr y k ∈ I (r + 1 - k)) ∧ D y = z := by
  intro B M _ _ _ e I p q ν D hp0 hpn hqn hmul hanti hν1 hνI hνn hνN hD
  obtain ⟨J, hJ, hpJ, hqJ, hνJ⟩ := exists_nilpotent_ideal (p : B) q ν hpn hqn hνn hνN
  have hstable : ∀ y ∈ J • (⊤ : Submodule B M), (D * shift e - 1) y ∈ J • (⊤ : Submodule B M) := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr n _
      rw [map_smul]
      exact Submodule.smul_mem_smul hr trivial
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  have hVp : ∀ z, ((D * shift e - 1) ^ p) z ∈ J • (⊤ : Submodule B M) := by
    intro z
    have h1 := pow_sub_mem _ (D * shift e - 1) (raise e) hstable
      (sub_raise_mem e J q ν D hqJ hνJ hν1 hD) p z
    have h2 := raise_pow_mem e J p hp0 hpJ z
    have h3 := Submodule.add_mem _ h1 h2
    simpa using h3
  have hV : IsNilpotent (D * shift e - 1 : Module.End B M) :=
    (nilpotent_of_pow_mem J hJ _ hVp).of_pow
  have hW : IsNilpotent (1 - D * shift e : Module.End B M) := by
    rw [← neg_sub]
    exact hV.neg
  obtain ⟨n, hn⟩ := hW
  set T : Module.End B M := D * shift e with hTdef
  set Wm : Module.End B M := 1 - T with hWm
  have h1W : 1 - Wm = T := by simp [hWm]
  set R : Module.End B M := ∑ i ∈ Finset.range n, Wm ^ i with hR
  have hTR : T * R = 1 := by
    have := mul_neg_geom_sum Wm n
    rwa [h1W, hn, sub_zero] at this
  have hRT : R * T = 1 := by
    have := geom_sum_mul_neg Wm n
    rwa [h1W, hn, sub_zero] at this
  constructor
  · intro z hz
    obtain ⟨c, z', rfl⟩ := exists_eq_add_shift e z
    have hD0 : D (e 0) = 0 := by simpa using hD 0
    have hTz : T z' = 0 := by
      have : D (c • e 0 + shift e z') = T z' := by
        simp [hTdef, Module.End.mul_apply, hD0]
      rwa [this] at hz
    have hz' : z' = 0 := by
      have : (R * T) z' = z' := by rw [hRT]; rfl
      rw [← this, Module.End.mul_apply, hTz, map_zero]
    exact ⟨c, by simp [hz']⟩
  · intro r z hz
    have hTG : ∀ y ∈ grade e I r, T y ∈ grade e I r :=
      mul_shift_mem_grade e I q ν D hmul hanti hνI hD r
    have hWG : ∀ y ∈ grade e I r, Wm y ∈ grade e I r := by
      intro y hy
      simpa [hWm] using Submodule.sub_mem _ hy (hTG y hy)
    have hpow : ∀ i, ∀ y ∈ grade e I r, (Wm ^ i) y ∈ grade e I r := by
      intro i
      induction i with
      | zero => intro y hy; simpa using hy
      | succ i ih =>
        intro y hy
        rw [pow_succ', Module.End.mul_apply]
        exact hWG _ (ih y hy)
    have hRG : R z ∈ grade e I r := by
      rw [hR, LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun i _ => hpow i z hz
    refine ⟨shift e (R z), shift_mem_grade e I r _ hRG, ?_⟩
    have : (T * R) z = z := by rw [hTR]; rfl
    simpa [hTdef, Module.End.mul_apply] using this

end GlobalTheory.CompanionTheory.QDerivative
