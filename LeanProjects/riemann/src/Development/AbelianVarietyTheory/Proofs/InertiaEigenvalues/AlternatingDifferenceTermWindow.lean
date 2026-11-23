import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegral

noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical

namespace GlobalTheory.UnitLemma.Desc.Window

variable {K : UQ} (B : InvAlg K) {ι : Type}

theorem al_ne_zero {a : K.O} (ha : K.Small a) : al K a ≠ 0 := by
  intro h
  exact ha.1 ((injective_iff_map_eq_zero (algebraMap K.O K.E)).1 (IsFractionRing.injective K.O K.E) a h)

theorem zpow_smul_eq (a : K.O) (n : ℤ) (hn : 0 ≤ n) (y : B.A) :
    al K a ^ n • y = algebraMap K.O B.A (a ^ n.toNat) * y := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [zpow_natCast, Int.toNat_natCast, Algebra.smul_def, IsScalarTower.algebraMap_apply K.O K.E B.A]
  simp only [map_pow]

theorem isIntegral_zpow_smul (a : K.O) {n : ℤ} (hn : 0 ≤ n) {y : B.A} (hy : IsIntegral K.O y) :
    IsIntegral K.O (al K a ^ n • y) := by
  rw [zpow_smul_eq B a n hn]
  exact isIntegral_algebraMap.mul hy

theorem isIntegral_zpow_smul_of_le {a : K.O} (ha : K.Small a) {c n : ℤ} (hcn : c ≤ n) {y : B.A}
    (hy : IsIntegral K.O (al K a ^ c • y)) : IsIntegral K.O (al K a ^ n • y) := by
  have : al K a ^ n • y = al K a ^ (n - c) • (al K a ^ c • y) := by
    rw [smul_smul, ← zpow_add₀ (al_ne_zero ha)]; congr 2; ring
  rw [this]
  exact isIntegral_zpow_smul B a (by omega) hy

theorem exists_scale {a : K.O} (ha : K.Small a) (y : B.A) :
    ∃ c : ℕ, ∀ n : ℤ, (c : ℤ) ≤ n → IsIntegral K.O (al K a ^ n • y) := by
  have halg : IsAlgebraic K.O y :=
    (IsFractionRing.isAlgebraic_iff K.O K.E (C := B.A)).2 (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨y0, hy0, hint⟩ := halg.exists_integral_multiple
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hy0 hϖ
  have hdvd : ϖ ∣ a := by
    have := ha.2.1
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    exact this
  obtain ⟨w, hw⟩ : y0 ∣ a ^ m := hm.dvd.trans (pow_dvd_pow_of_dvd hdvd m)
  refine ⟨m, fun n hn => isIntegral_zpow_smul_of_le B ha hn ?_⟩
  rw [zpow_natCast]
  have : al K a ^ m • y = algebraMap K.O B.A w * (y0 • y) := by
    rw [← map_pow, algebraMap_smul, hw, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
  rw [this]
  exact isIntegral_algebraMap.mul hint

theorem exists_bound {a : K.O} (ha : K.Small a) {t : K.E} (ht : t ≠ 0) :
    ∃ C : ℕ, ∀ m : ℤ, al K a ^ m * t ∈ (algebraMap K.O K.E).range → -(C : ℤ) ≤ m := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := K.O) t
  have hd0 : algebraMap K.O K.E d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hn0 : n ≠ 0 := by rintro rfl; simp at ht
  have hnu : ¬ IsUnit a := fun hu => (IsLocalRing.mem_maximalIdeal a).1 ha.2.1 hu
  obtain ⟨C, hC⟩ := FiniteMultiplicity.of_not_isUnit hnu hn0
  refine ⟨C, fun m hm => ?_⟩
  by_contra hlt
  push_neg at hlt
  obtain ⟨b, hb⟩ := hm
  obtain ⟨j, hj⟩ : ∃ j : ℕ, m = -(j : ℤ) := ⟨(-m).toNat, by omega⟩
  apply hC
  have hjC : C + 1 ≤ j := by omega
  refine (pow_dvd_pow a hjC).trans ⟨d * b, ?_⟩
  apply IsFractionRing.injective K.O K.E
  have hα := al_ne_zero ha
  rw [hj, zpow_neg, zpow_natCast] at hb
  rw [map_mul, map_mul, map_pow, hb]
  field_simp

theorem trace_mem_of_isIntegral {y : B.A} (hy : IsIntegral K.O y) :
    Algebra.trace K.E B.A y ∈ (algebraMap K.O K.E).range := by
  have h := GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral K.O K.E B.A y hy
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨z, hz⟩

theorem trace_ne_zero_of_idem {f : B.A} (hf : IsIdempotentElem f) (h0 : f ≠ 0) :
    Algebra.trace K.E B.A f ≠ 0 := by
  set g := Algebra.lmul K.E B.A f
  have hproj : LinearMap.IsProj (LinearMap.range g) g := by
    refine ⟨fun x => LinearMap.mem_range_self g x, ?_⟩
    rintro _ ⟨z, rfl⟩
    change f * (f * z) = f * z
    rw [← mul_assoc, hf.eq]
  rw [Algebra.trace_apply, hproj.trace]
  have hmem : f ∈ LinearMap.range g := ⟨1, by change f * 1 = f; rw [mul_one]⟩
  have hpos : LinearMap.range g ≠ ⊥ := by
    intro hb; rw [hb, Submodule.mem_bot] at hmem; exact h0 hmem
  rw [Ne, Nat.cast_eq_zero, Submodule.finrank_eq_zero]
  exact hpos

theorem not_isIntegral_inv_smul_idem {a : K.O} (ha : K.Small a) {f : B.A} (hf : IsIdempotentElem f)
    (h0 : f ≠ 0) : ¬ IsIntegral K.O (al K a ^ (-1 : ℤ) • f) := by
  intro hint
  obtain ⟨C, hC⟩ := exists_bound ha (trace_ne_zero_of_idem B hf h0)
  have hpow : (al K a ^ (-1 : ℤ) • f) ^ (C + 1) = al K a ^ (-((C + 1 : ℕ) : ℤ)) • f := by
    rw [_root_.smul_pow, hf.pow_succ_eq, ← zpow_natCast, ← zpow_mul]; congr 2; push_cast; ring
  have ht := trace_mem_of_isIntegral B (hint.pow (C + 1))
  rw [hpow, LinearMap.map_smul, smul_eq_mul] at ht
  have := hC _ ht
  push_cast at this
  omega

theorem ne_zero_of_isPre [Fintype ι] {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (i : ι) : e i ≠ 0 := by
  obtain ⟨f, hf, hf0, -, hS, hnS⟩ := h.2 i
  by_cases hi : i ∈ S
  · rw [(hS hi).1]; exact hf0
  · obtain ⟨h1, h2⟩ := hnS hi
    rw [h2]
    intro hz
    have hs : B.σ f = -f := eq_neg_of_add_eq_zero_right hz
    rw [hs, mul_neg, hf.eq, neg_eq_zero] at h1
    exact hf0 h1

def dualSub (M : Submodule K.O B.A) : AddSubgroup B.A where
  carrier := {s | InDual B s M}
  zero_mem' := by intro z _; simp
  add_mem' := by
    intro s t hs ht z hz
    rw [add_mul, map_add]
    exact add_mem (hs z hz) (ht z hz)
  neg_mem' := by
    intro s hs z hz
    rw [neg_mul, map_neg]
    exact neg_mem (hs z hz)

def ind (Q : AddSubgroup B.A) (y : B.A) : ℚ := if y ∈ Q then 1 else 0

theorem indM_eq (M : Submodule K.O B.A) : indM B M = ind B M.toAddSubgroup := by
  funext y; unfold indM ind; simp

theorem indD_eq (M : Submodule K.O B.A) : indD B M = ind B (dualSub B M) := by
  funext y; unfold indD ind; rfl

theorem ind_add {Q : AddSubgroup B.A} {w d : B.A} (hd : d ∈ Q) : ind B Q (w + d) = ind B Q w := by
  unfold ind
  rw [Q.add_mem_cancel_right hd]

theorem dlt_ind_eq_zero {e π : ι → B.A} (Q : AddSubgroup B.A) {I : Finset ι} {i : ι} (hi : i ∈ I)
    (hπ : π i * (1 - e i) = 1 - e i) (y : B.A)
    (hQ : ∀ J ⊆ I, e i * ((∏ j ∈ J, π j) * y) ∈ Q) : dlt π I (ind B Q) y = 0 := by
  refine dlt_eq_zero π I _ y i hi fun J hJ => ?_
  set w := (∏ j ∈ J, π j) * y
  have hiJ : i ∉ J := fun h => Finset.notMem_erase i I (hJ h)
  have hJI : J ⊆ I := hJ.trans (Finset.erase_subset i I)
  have h1 : e i * (π i * w) ∈ Q := by
    have := hQ (insert i J) (Finset.insert_subset hi hJI)
    rwa [Finset.prod_insert hiJ, mul_assoc] at this
  have h2 : e i * w ∈ Q := hQ J hJI
  have hw : π i * w = w + (e i * (π i * w) - e i * w) := by linear_combination w * hπ
  rw [hw, ind_add B (sub_mem h1 h2)]

theorem dlt_ind_eS [Fintype ι] {e π : ι → B.A} (Q : AddSubgroup B.A) (he : ∑ i, e i = 1)
    (I I₀ : Finset ι) (y : B.A) (hQ : ∀ J ⊆ I, ∀ i ∉ I₀, e i * ((∏ j ∈ J, π j) * y) ∈ Q) :
    dlt π I (ind B Q) y = dlt π I (ind B Q) (eS B e I₀ * y) := by
  unfold dlt
  refine Finset.sum_congr rfl fun J hJ => ?_
  congr 1
  set w := (∏ j ∈ J, π j) * y
  have hsum : ∑ i ∈ I₀ᶜ, e i * w ∈ Q :=
    Q.sum_mem fun i hi => hQ J (Finset.mem_powerset.1 hJ) i (Finset.mem_compl.1 hi)
  have hw : w = (∏ j ∈ J, π j) * (eS B e I₀ * y) + ∑ i ∈ I₀ᶜ, e i * w := by
    have h := Finset.sum_add_sum_compl I₀ fun i => e i * w
    have h2 : ∑ i, e i * w = w := by rw [← Finset.sum_mul, he, one_mul]
    rw [h2, ← Finset.sum_mul] at h
    conv_lhs => rw [← h]
    congr 1
    unfold eS; simp only [w]; ring
  rw [hw, ind_add B hsum]

theorem exists_of_dlt_ne_zero {π : ι → B.A} {I : Finset ι} {f : B.A → ℚ} {y : B.A}
    (h : dlt π I f y ≠ 0) : ∃ J ⊆ I, f ((∏ j ∈ J, π j) * y) ≠ 0 := by
  obtain ⟨J, hJ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨J, Finset.mem_powerset.1 hJ, right_ne_zero_of_mul hne⟩

theorem mem_of_pos {a : K.O} (ha : K.Small a) [Fintype ι] {e : ι → B.A} {N : ℕ} {M : Submodule K.O B.A}
    {p : ι → ℤ} (hP : Pos B a e N M p) (i : ι) {c : ℕ} {y : B.A}
    (hy : ∀ n : ℤ, (c : ℤ) ≤ n → IsIntegral K.O (al K a ^ n • y)) (k : ℕ) (hk : p i + N + c ≤ 2 * k) :
    e i * (al K a ^ ((2 * k : ℕ) : ℤ) • y) ∈ M := by
  have hr := hy (2 * k - p i - N) (by omega)
  have h := (hP i).1 _ hr
  convert h using 1
  rw [mul_smul_comm, mul_smul_comm, smul_smul, ← zpow_add₀ (al_ne_zero ha)]
  congr 2; push_cast; ring

theorem inDual_of_pos {a : K.O} (ha : K.Small a) [Fintype ι] {e : ι → B.A} {N : ℕ} {M : Submodule K.O B.A}
    {p : ι → ℤ} (hP : Pos B a e N M p) (i : ι) {c : ℕ} {y : B.A}
    (hy : ∀ n : ℤ, (c : ℤ) ≤ n → IsIntegral K.O (al K a ^ n • y)) (hp : (c : ℤ) ≤ p i) :
    InDual B (e i * y) M := by
  intro z hz
  have h2 := (hP i).2 z hz
  have h1 := hy c le_rfl
  have hα := al_ne_zero ha
  have heq : e i * y * z = al K a ^ (p i - c) • ((al K a ^ (c : ℤ) • y) * (al K a ^ (-p i) • (e i * z))) := by
    rw [smul_mul_smul_comm, smul_smul, ← zpow_add₀ hα, ← zpow_add₀ hα]
    have : p i - c + (c + -p i) = 0 := by ring
    rw [this, zpow_zero, one_smul]; ring
  rw [heq]
  exact trace_mem_of_isIntegral B (isIntegral_zpow_smul B a (by omega) (h1.mul h2))

theorem prod_mul_eq (a : K.O) (P x : B.A) (k : ℕ) :
    P * (x * algebraMap K.O B.A a ^ (2 * k)) = al K a ^ ((2 * k : ℕ) : ℤ) • (P * x) := by
  rw [zpow_natCast, Algebra.smul_def, IsScalarTower.algebraMap_apply K.O K.E B.A]
  simp only [map_pow]; ring

end GlobalTheory.UnitLemma.Desc.Window

open GlobalTheory.UnitLemma.Desc.Window in

theorem GlobalTheory.UnitLemma.Desc.term_window : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A)
    (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ I I' : Finset ι, I ⊆ S → I' ⊆ S →
    (∀ i ∈ S, i ∈ I ∨ i ∈ I') → ∀ (N : ℕ) (x s : B.A), IsUnit x → IsUnit s → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ k : ℕ, L ≤ k →
    ∀ (M : Submodule K.O B.A) (p : ι → ℤ), Pos B a e N M p →
    (term B π I I' (x * algebraMap K.O B.A a ^ (2 * k)) s M ≠ 0 → Win I I' L k p) ∧
    (Win I I' L k p → Mid S L k p → term B π I I' (x * algebraMap K.O B.A a ^ (2 * k)) s M =
      term B π I I' (eS B e I * (x * algebraMap K.O B.A a ^ (2 * k))) (eS B e I' * s) M) := by
  intro K B ι _ e π S a _ ha hF I I' hIS hI'S hcov N x s hx hs
  have hα := al_ne_zero ha
  have hPu : ∀ J ⊆ S, IsUnit (∏ j ∈ J, π j) := fun J hJ =>
    Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j hj => (hF.2 j (hJ hj)).1.1
  let T : Finset B.A := S.powerset.biUnion fun J =>
    {(∏ j ∈ J, π j) * x, Ring.inverse ((∏ j ∈ J, π j) * x), (∏ j ∈ J, π j) * s,
      Ring.inverse ((∏ j ∈ J, π j) * s)}
  have memT : ∀ J ⊆ S, ∀ y ∈ ({(∏ j ∈ J, π j) * x, Ring.inverse ((∏ j ∈ J, π j) * x), (∏ j ∈ J, π j) * s,
      Ring.inverse ((∏ j ∈ J, π j) * s)} : Finset B.A), y ∈ T := fun J hJ y hy =>
    Finset.mem_biUnion.2 ⟨J, Finset.mem_powerset.2 hJ, hy⟩
  choose cf hcf using fun y : B.A => exists_scale B ha y
  set c := T.sup cf
  have hc : ∀ y ∈ T, ∀ n : ℤ, (c : ℤ) ≤ n → IsIntegral K.O (al K a ^ n • y) := fun y hy n hn =>
    hcf y n (le_trans (by exact_mod_cast Finset.le_sup hy) hn)
  choose Cf hCf using fun i => exists_bound ha (trace_ne_zero_of_idem B (hF.1.1.idem i) (ne_zero_of_isPre B hF.1 i))
  set Ct := Finset.univ.sup Cf
  have hCt : ∀ i (m : ℤ), al K a ^ m * Algebra.trace K.E B.A (e i) ∈ (algebraMap K.O K.E).range →
      -(Ct : ℤ) ≤ m := fun i m h =>
    le_trans (neg_le_neg (by exact_mod_cast Finset.le_sup (Finset.mem_univ i))) (hCf i m h)
  have hπ : ∀ i ∈ S, π i * (1 - e i) = 1 - e i := fun i hi => (hF.2 i hi).2.1
  refine ⟨N + c + Ct, fun L hL k hk M p hP => ?_⟩
  have memU : ∀ J ⊆ S, ∀ i, p i + N + c ≤ 2 * k →
      e i * ((∏ j ∈ J, π j) * (x * algebraMap K.O B.A a ^ (2 * k))) ∈ M := by
    intro J hJ i hi
    rw [prod_mul_eq]
    exact mem_of_pos B ha hP i (hc _ (memT J hJ _ (by simp))) k hi
  have dualS : ∀ J ⊆ S, ∀ i, (c : ℤ) ≤ p i → InDual B (e i * ((∏ j ∈ J, π j) * s)) M := by
    intro J hJ i hi
    exact inDual_of_pos B ha hP i (hc _ (memT J hJ _ (by simp))) hi
  constructor
  · intro hne
    unfold term at hne
    have hne1 := left_ne_zero_of_mul hne
    have hne2 := right_ne_zero_of_mul hne
    obtain ⟨J, hJ, hJm⟩ := exists_of_dlt_ne_zero B hne1
    have hJM : (∏ j ∈ J, π j) * (x * algebraMap K.O B.A a ^ (2 * k)) ∈ M := by
      by_contra h; apply hJm; simp [indM, h]
    obtain ⟨J', hJ', hJd⟩ := exists_of_dlt_ne_zero B hne2
    have hJD : InDual B ((∏ j ∈ J', π j) * s) M := by
      by_contra h; apply hJd; simp [indD, h]
    intro i
    refine ⟨?_, ?_, ?_, ?_⟩
    · set w := (∏ j ∈ J', π j) * s
      have hw : IsUnit w := (hPu J' (hJ'.trans hI'S)).mul hs
      have hr := hc (Ring.inverse w) (memT J' (hJ'.trans hI'S) _ (by simp [w])) c le_rfl
      have ht := hJD _ ((hP i).1 _ hr)
      have heq : w * (al K a ^ (p i + N) • (e i * (al K a ^ (c : ℤ) • Ring.inverse w))) =
          al K a ^ (p i + N + c) • e i := by
        simp only [mul_smul_comm, smul_smul, ← zpow_add₀ hα]
        rw [mul_left_comm, Ring.mul_inverse_cancel w hw, mul_one]
      rw [heq, LinearMap.map_smul, smul_eq_mul] at ht
      have := hCt i _ ht
      omega
    · by_contra hb
      push_neg at hb
      set w := (∏ j ∈ J, π j) * x
      have hw : IsUnit w := (hPu J (hJ.trans hIS)).mul hx
      have h1 := (hP i).2 _ hJM
      rw [prod_mul_eq] at h1
      have h2 := hc (Ring.inverse w) (memT J (hJ.trans hIS) _ (by simp [w])) c le_rfl
      have h3 := h1.mul h2
      have heq : al K a ^ (-p i) • (e i * (al K a ^ ((2 * k : ℕ) : ℤ) • w)) * (al K a ^ (c : ℤ) • Ring.inverse w)
          = al K a ^ (-p i + ((2 * k : ℕ) : ℤ) + c) • e i := by
        simp only [mul_smul_comm, smul_mul_assoc, smul_smul, ← zpow_add₀ hα]
        rw [mul_assoc, Ring.mul_inverse_cancel w hw, mul_one]
        congr 2; ring
      rw [heq] at h3
      apply not_isIntegral_inv_smul_idem B ha (hF.1.1.idem i) (ne_zero_of_isPre B hF.1 i)
      exact isIntegral_zpow_smul_of_le B ha (by push_cast; omega) h3
    · intro hiI
      by_contra hc'
      push_neg at hc'
      apply hne1
      rw [indM_eq]
      refine dlt_ind_eq_zero B _ hiI (hπ i (hIS hiI)) _ fun J hJ => ?_
      exact memU J (hJ.trans hIS) i (by omega)
    · intro hiI'
      by_contra hd
      push_neg at hd
      apply hne2
      rw [indD_eq]
      refine dlt_ind_eq_zero B _ hiI' (hπ i (hI'S hiI')) _ fun J hJ => ?_
      exact dualS J (hJ.trans hI'S) i (by omega)
  · intro hW hMid
    unfold term
    congr 1
    · rw [indM_eq]
      refine dlt_ind_eS B _ hF.1.1.complete I I _ fun J hJ i hi => ?_
      refine memU J (hJ.trans hIS) i ?_
      have : p i ≤ 2 * k - L := by
        by_cases hiS : i ∈ S
        · have hiI' : i ∈ I' := (hcov i hiS).resolve_left hi
          have := (hW i).2.2.2 hiI'
          omega
        · exact (hMid i hiS).2
      omega
    · rw [indD_eq]
      refine dlt_ind_eS B _ hF.1.1.complete I' I' _ fun J hJ i hi => ?_
      refine dualS J (hJ.trans hI'S) i ?_
      have : (L : ℤ) ≤ p i := by
        by_cases hiS : i ∈ S
        · have hiI : i ∈ I := (hcov i hiS).resolve_right hi
          have := (hW i).2.2.1 hiI
          omega
        · exact (hMid i hiS).1
      omega
