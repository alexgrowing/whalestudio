import Mathlib
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtD
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtE

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K}

theorem Kn_le_Kur {n : ℕ} (hn : 0 < n) : Kn p K n ≤ MaximalUnramifiedExtension p K := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact le_iSup (fun n : ℕ => Kn p K (n + 1)) k

theorem le_Kur : K ≤ MaximalUnramifiedExtension p K := (le_Kn p K 1).trans (Kn_le_Kur one_pos)

theorem mem_Kur_iff (hK : FiniteDimensional ℚ_[p] K) (x : PadicAlgCl p) :
    x ∈ MaximalUnramifiedExtension p K ↔ ∃ n, 0 < n ∧ x ∈ Kn p K n := by
  constructor
  · intro hx
    have hdir : Directed (· ≤ ·) (fun n : ℕ => Kn p K (n + 1)) := by
      intro i j
      refine ⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩
      · have : (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1) := Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))
        change Kn p K (i + 1) ≤ Kn p K ((i + 1) * (j + 1) - 1 + 1)
        rw [this]; exact Kn_mono p K hK (Dvd.intro _ rfl)
      · have : (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1) := Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))
        change Kn p K (j + 1) ≤ Kn p K ((i + 1) * (j + 1) - 1 + 1)
        rw [this]; exact Kn_mono p K hK (Dvd.intro_left _ rfl)
    have h := IntermediateField.coe_iSup_of_directed hdir
    have hx' : x ∈ ((⨆ n : ℕ, Kn p K (n + 1) : IntermediateField ℚ_[p] (PadicAlgCl p)) : Set (PadicAlgCl p)) := hx
    rw [h] at hx'
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx'
    exact ⟨k + 1, Nat.succ_pos k, hk⟩
  · rintro ⟨n, hn, hx⟩
    exact Kn_le_Kur hn hx

theorem exists_dvd_qK_pow_sub_one (hK : FiniteDimensional ℚ_[p] K) {m : ℕ} (hm : ¬ p ∣ m) :
    ∃ n, 0 < n ∧ m ∣ qK p K ^ n - 1 := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero p))
  obtain ⟨f, hf, hq⟩ := qK_eq_pow p K hK
  have hcop : Nat.Coprime (qK p K) m := by
    rw [hq]
    exact Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
  refine ⟨Nat.totient m, Nat.totient_pos.2 hm0, ?_⟩
  have h1 : 1 ≤ qK p K ^ Nat.totient m := Nat.one_le_pow _ _ (by have := one_lt_qK p K hK; omega)
  exact (Nat.modEq_iff_dvd' h1).1 (Nat.ModEq.pow_totient hcop).symm

theorem mem_Kur_of_pow (hK : FiniteDimensional ℚ_[p] K) {m : ℕ} (hm : ¬ p ∣ m) {ζ : PadicAlgCl p}
    (hζ : ζ ^ m = 1) : ζ ∈ MaximalUnramifiedExtension p K := by
  obtain ⟨n, hn, d, hd⟩ := exists_dvd_qK_pow_sub_one hK hm
  exact Kn_le_Kur hn (mem_Kn_of_pow p K (by rw [hd, pow_mul, hζ, one_pow]))

theorem Kur_eq (hK : FiniteDimensional ℚ_[p] K) :
    MaximalUnramifiedExtension p K = K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ∃ m : ℕ, ¬ p ∣ m ∧ ζ ^ m = 1} := by
  apply le_antisymm
  · refine iSup_le fun n => UnramifiedExtensions.Kn_le K le_sup_left fun ζ hζ => ?_
    exact (le_sup_right : _ ≤ K ⊔ _) (IntermediateField.subset_adjoin _ _
      ⟨_, UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK (Nat.succ_pos n), hζ⟩)
  · refine sup_le le_Kur (IntermediateField.adjoin_le_iff.2 ?_)
    rintro ζ ⟨m, hm, hζ⟩
    exact mem_Kur_of_pow hK hm hζ

theorem Kur_eq_sup (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    MaximalUnramifiedExtension p L = L ⊔ MaximalUnramifiedExtension p K := by
  rw [Kur_eq hK, Kur_eq hL, ← sup_assoc, sup_eq_left.2 h]

theorem Kur_le_Kur (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    MaximalUnramifiedExtension p K ≤ MaximalUnramifiedExtension p L := by
  rw [Kur_eq_sup L hK hL h]; exact le_sup_right

theorem exists_teichmuller_bar (x : PadicAlgCl p) (hx : ‖x‖ = 1) :
    ∃ (ζ : PadicAlgCl p) (m : ℕ), ¬ p ∣ m ∧ ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  have hfd : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  obtain ⟨ζ, -, hζ, h⟩ := exists_teichmuller p _ hfd (IntermediateField.mem_adjoin_simple_self ℚ_[p] x) hx
  refine ⟨ζ, _, ?_, hζ, h⟩
  simpa using UnramifiedExtensions.not_dvd_qK_pow_sub_one _ hfd (n := 1) one_pos

theorem eqOn_Kur {σ τ : GK p K} (h : ∀ (ζ : PadicAlgCl p) (m : ℕ), ¬ p ∣ m → ζ ^ m = 1 → σ ζ = τ ζ)
    (hK : FiniteDimensional ℚ_[p] K) {x : PadicAlgCl p} (hx : x ∈ MaximalUnramifiedExtension p K) : σ x = τ x := by
  obtain ⟨n, hn, hxn⟩ := (mem_Kur_iff hK x).1 hx
  exact UnramifiedExtensions.eqOn_Kn K (fun ζ hζ => h ζ _ (UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn) hζ) hxn

theorem isFrob_iff (hK : FiniteDimensional ℚ_[p] K) (σ : GK p K) :
    IsFrob p K σ ↔ ∀ (ζ : PadicAlgCl p) (m : ℕ), ¬ p ∣ m → ζ ^ m = 1 → σ ζ = ζ ^ qK p K := by
  constructor
  · intro h ζ m hm hζ
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
    by_contra hne
    have h1 : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
    have h2 : (ζ ^ qK p K) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    have h3 := norm_sub_eq_one_of_pow_eq_one p hm h1 h2 hne
    exact absurd h3 (ne_of_lt (h ζ (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le))
  · intro h x hx
    have hq : qK p K ≠ 0 := by have := one_lt_qK p K hK; omega
    have hσx : ‖σ x‖ ≤ 1 := by rw [norm_GK]; exact hx
    have hxq : ‖x ^ qK p K‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    rw [← UnramifiedExtensions.red_eq_iff hσx hxq, ← UnramifiedExtensions.sigBar_red σ hx, UnramifiedExtensions.red_pow hx]
    rcases lt_or_eq_of_le hx with hlt | heq
    · have h0 : UnramifiedExtensions.red x = 0 := by
        rw [UnramifiedExtensions.red_of_le hx, UnramifiedExtensions.res_eq_zero_iff]; exact hlt
      rw [h0, map_zero, zero_pow hq]
    · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := exists_teichmuller_bar x heq
      have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
      have hζ1 := (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le
      rw [(UnramifiedExtensions.red_eq_iff hx hζ1).2 hxζ, UnramifiedExtensions.sigBar_red σ hζ1, h ζ m hm hζ, UnramifiedExtensions.red_pow hζ1]

theorem exists_isFrob (hK : FiniteDimensional ℚ_[p] K) : ∃ σ : GK p K, IsFrob p K σ := by
  let S : ℕ → Set (GK p K) := fun k => {σ | IsFrobOn p K (k + 1).factorial σ}
  have hS : ∀ k, S k = ⋂ ζ : PadicAlgCl p, ⋂ _ : ζ ^ (qK p K ^ (k + 1).factorial - 1) = 1,
      {σ : GK p K | σ ζ = ζ ^ qK p K} := by
    intro k
    ext σ
    simp only [S, Set.mem_ofPred_eq, Set.mem_iInter]
    exact isFrobOn_iff p K hK (Nat.factorial_pos _) σ
  have hcl : ∀ k, IsClosed (S k) := by
    intro k
    rw [hS]
    exact isClosed_iInter fun ζ => isClosed_iInter fun _ =>
      ReciprocityTheory.Gal.isClosed_setOf_apply ζ (fun y => y = ζ ^ qK p K)
  have hne : ∀ k, (S k).Nonempty := fun k => exists_isFrobOn p K hK (Nat.factorial_pos _)
  have hmono : ∀ k, S (k + 1) ⊆ S k := fun k σ hσ =>
    IsFrobOn.of_dvd p K hK (Nat.factorial_dvd_factorial (Nat.le_succ _)) hσ
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne
    (hcl 0).isCompact hcl
  refine ⟨σ, (isFrob_iff hK σ).2 fun ζ m hm hζ => ?_⟩
  obtain ⟨n, hn, d, hd⟩ := exists_dvd_qK_pow_sub_one hK hm
  have h1 : IsFrobOn p K n σ := by
    have h2 : IsFrobOn p K ((n - 1) + 1).factorial σ := Set.mem_iInter.1 hσ (n - 1)
    refine IsFrobOn.of_dvd p K hK ?_ h2
    rw [Nat.sub_add_cancel hn]
    exact Nat.dvd_factorial hn le_rfl
  exact (isFrobOn_iff p K hK hn σ).1 h1 ζ (by rw [hd, pow_mul, hζ, one_pow])

theorem isFrob_frobK (hK : FiniteDimensional ℚ_[p] K) : IsFrob p K (frobK p K) :=
  Classical.epsilon_spec (exists_isFrob hK)

theorem IsFrob.isFrobOn {σ : GK p K} (h : IsFrob p K σ) (n : ℕ) : IsFrobOn p K n σ :=
  fun x _ hx => h x hx

theorem IsFrob.eqOn (hK : FiniteDimensional ℚ_[p] K) {σ τ : GK p K} (hσ : IsFrob p K σ) (hτ : IsFrob p K τ)
    {x : PadicAlgCl p} (hx : x ∈ MaximalUnramifiedExtension p K) : σ x = τ x :=
  eqOn_Kur (fun ζ m hm hζ => by rw [(isFrob_iff hK σ).1 hσ ζ m hm hζ, (isFrob_iff hK τ).1 hτ ζ m hm hζ]) hK hx

theorem mk_eq_mk_iff {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ τ : GK p K) :
    (QuotientGroup.mk σ : GalLK p K M) = QuotientGroup.mk τ ↔ ∀ x ∈ M, σ x = τ x := by
  rw [QuotientGroup.eq, mem_subG_iff]
  constructor
  · intro h x hx
    have := congrArg σ (h x hx)
    rw [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, mul_inv_cancel] at this
    exact this.symm
  · intro h x hx
    rw [AlgEquiv.mul_apply, ← h x hx, ← AlgEquiv.mul_apply, inv_mul_cancel]
    rfl

theorem IsFrob.mk_eq (hK : FiniteDimensional ℚ_[p] K) {σ : GK p K} (h : IsFrob p K σ) :
    (QuotientGroup.mk σ : GalLK p K (MaximalUnramifiedExtension p K)) = frobLK p K (MaximalUnramifiedExtension p K) :=
  (mk_eq_mk_iff σ (frobK p K)).2 fun _ hx => IsFrob.eqOn hK h (isFrob_frobK hK) hx

theorem mem_subG_Kur_iff (hK : FiniteDimensional ℚ_[p] K) (σ : GK p K) :
    σ ∈ subG p K (MaximalUnramifiedExtension p K) ↔ ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  constructor
  · intro h x hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact lt_of_le_of_lt (UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [norm_GK]; exact hlt) hlt)
    · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := exists_teichmuller_bar x heq
      have h1 : σ ζ = ζ := h ζ (mem_Kur_of_pow hK hm hζ)
      have h2 : σ x - x = σ (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
      rw [h2]
      exact lt_of_le_of_lt (UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [norm_GK]; exact hxζ) hxζ)
  · intro h x hx
    refine eqOn_Kur (σ := σ) (τ := 1) (fun ζ m hm hζ => ?_) hK hx
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
    by_contra hne
    have h1 : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
    have h3 := norm_sub_eq_one_of_pow_eq_one p hm h1 hζ hne
    exact absurd h3 (ne_of_lt (h ζ (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le))

theorem subG_Kur_eq_inertiaK (hK : FiniteDimensional ℚ_[p] K) : subG p K (MaximalUnramifiedExtension p K) = inertiaK p K := by
  have h : inertiaSet p K = (subG p K (MaximalUnramifiedExtension p K) : Set (GK p K)) := by
    ext σ
    exact (mem_subG_Kur_iff hK σ).symm
  rw [inertiaK, h, Subgroup.closure_eq]

theorem degLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : degLK p K (Kn p K n) = n := by
  have h1 := finrank_eq_degLK_mul (le_Kn p K n) (finiteDimensional_Kn p K hK hn)
  rw [finrank_Kn p K hK hn] at h1
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  exact (Nat.eq_of_mul_eq_mul_right hd h1).symm

theorem frobLK_pow (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [(subG p K M).Normal] (i : ℕ) :
    frobLK p K M ^ i = QuotientGroup.mk (frobK p K ^ i) := rfl

theorem mem_zpowers_frobLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n)
    (g : GalLK p K (Kn p K n)) : g ∈ Subgroup.zpowers (frobLK p K (Kn p K n)) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨i, -, hi⟩ := IsFrobOn.exists_pow p K hK hn ((isFrob_frobK hK).isFrobOn n) σ
  refine ⟨i, ?_⟩
  change frobLK p K (Kn p K n) ^ (i : ℤ) = _
  rw [zpow_natCast, frobLK_pow]
  exact ((mk_eq_mk_iff _ _).2 hi).symm

theorem frobLK_Kn_pow_eq_one_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    frobLK p K (Kn p K n) ^ i = 1 ↔ n ∣ i := by
  rw [frobLK_pow, ← IsFrobOn.pow_fixes_iff p K hK hn ((isFrob_frobK hK).isFrobOn n) i,
    ← QuotientGroup.mk_one, mk_eq_mk_iff]
  rfl

theorem orderOf_frobLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    orderOf (frobLK p K (Kn p K n)) = n := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((frobLK_Kn_pow_eq_one_iff hK hn n).2 dvd_rfl)
  · exact (frobLK_Kn_pow_eq_one_iff hK hn _).1 (pow_orderOf_eq_one _)

theorem mem_of_frobK_fixed (hK : FiniteDimensional ℚ_[p] K) {x : PadicAlgCl p} (hx : x ∈ MaximalUnramifiedExtension p K)
    (h : frobK p K x = x) : x ∈ K := by
  obtain ⟨n, hn, hxn⟩ := (mem_Kur_iff hK x).1 hx
  apply UnramifiedExtensions.mem_of_fixed K
  intro σ
  obtain ⟨i, -, hi⟩ := IsFrobOn.exists_pow p K hK hn ((isFrob_frobK hK).isFrobOn n) σ
  rw [hi x hxn]
  clear hi
  induction i with
  | zero => rfl
  | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]

theorem isZHat_GalKur (hK : FiniteDimensional ℚ_[p] K) :
    IsZHat (GalLK p K (MaximalUnramifiedExtension p K)) (frobLK p K (MaximalUnramifiedExtension p K)) := by
  constructor
  · set C : Subgroup (GalLK p K (MaximalUnramifiedExtension p K)) :=
      (Subgroup.zpowers (frobLK p K (MaximalUnramifiedExtension p K))).topologicalClosure with hC
    have hCcl : IsClosed (C : Set (GalLK p K (MaximalUnramifiedExtension p K))) := Subgroup.isClosed_topologicalClosure _
    set H : Subgroup (GK p K) := C.comap (QuotientGroup.mk' (subG p K (MaximalUnramifiedExtension p K))) with hH
    have hHcl : IsClosed (H : Set (GK p K)) := hCcl.preimage continuous_quot_mk
    obtain ⟨M, hKM, hM⟩ := exists_subG_eq H hHcl
    have hNH : subG p K (MaximalUnramifiedExtension p K) ≤ subG p K M := by
      rw [hM]
      intro σ hσ
      change (QuotientGroup.mk σ : GalLK p K (MaximalUnramifiedExtension p K)) ∈ C
      rw [(QuotientGroup.eq_one_iff σ).2 hσ]
      exact C.one_mem
    have hMur : M ≤ MaximalUnramifiedExtension p K := by
      have := (subG_le_iff hKM).1 hNH
      rwa [sup_eq_right.2 le_Kur] at this
    have hfr : frobK p K ∈ subG p K M := by
      rw [hM]
      change frobLK p K (MaximalUnramifiedExtension p K) ∈ C
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)
    have hMK : M ≤ K := fun x hx => mem_of_frobK_fixed hK (hMur hx) (hfr x hx)
    have htop : H = ⊤ := by
      rw [← hM, eq_top_iff]
      intro σ _ x hx
      exact σ.commutes ⟨x, hMK hx⟩
    have hCtop : C = ⊤ := by
      rw [eq_top_iff]
      intro g _
      obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
      have : σ ∈ H := by rw [htop]; trivial
      exact this
    rw [dense_iff_closure_eq]
    have h1 : closure (Subgroup.zpowers (frobLK p K (MaximalUnramifiedExtension p K)) : Set (GalLK p K (MaximalUnramifiedExtension p K))) =
        (C : Set (GalLK p K (MaximalUnramifiedExtension p K))) := rfl
    rw [h1, hCtop]
    rfl
  · intro k hk
    refine ⟨(subG p K (Kn p K k)).map (QuotientGroup.mk' (subG p K (MaximalUnramifiedExtension p K))), ?_, ?_⟩
    · exact QuotientGroup.isOpenMap_coe _ (isOpen_subG (finiteDimensional_Kn p K hK hk))
    · rw [Subgroup.index_map, QuotientGroup.ker_mk', sup_eq_left.2 (subG_anti (Kn_le_Kur hk)),
        MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), Subgroup.index_top, mul_one]
      exact degLK_Kn hK hk

theorem exists_le_Kn_of_le_Kur (hK : FiniteDimensional ℚ_[p] K) {M : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hM : FiniteDimensional ℚ_[p] M) (h : M ≤ MaximalUnramifiedExtension p K) : ∃ n, 0 < n ∧ M ≤ Kn p K n := by
  let b := Module.finBasis ℚ_[p] M
  have h1 : ∀ i, ∃ n, 0 < n ∧ (b i : PadicAlgCl p) ∈ Kn p K n := fun i => (mem_Kur_iff hK _).1 (h (b i).2)
  choose N hN hb using h1
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun x hx => ?_⟩
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : PadicAlgCl p) := by
    have := congrArg M.val (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    exact this.symm
  rw [hx']
  refine sum_mem fun i _ => ?_
  exact (Kn p K (∏ i, N i)).smul_mem (Kn_mono p K hK (Finset.dvd_prod_of_mem N (Finset.mem_univ i)) (hb i))

theorem exists_Kn_of_isOpen (hK : FiniteDimensional ℚ_[p] K) (U : Subgroup (GK p K))
    (hU : IsOpen (U : Set (GK p K))) (h : subG p K (MaximalUnramifiedExtension p K) ≤ U) :
    ∃ n, 0 < n ∧ U = subG p K (Kn p K n) := by
  obtain ⟨M, hKM, hM, rfl⟩ := exists_subG_eq_of_isOpen hK U hU
  have hMur : M ≤ MaximalUnramifiedExtension p K := by
    have := (subG_le_iff hKM).1 h
    rwa [sup_eq_right.2 le_Kur] at this
  obtain ⟨N, hN, hMN⟩ := exists_le_Kn_of_le_Kur hK hM hMur
  refine ⟨degLK p K M, degLK_pos hM, ?_⟩
  rw [← eq_Kn_of_norm p K hK hKM (degLK_pos hM) (finrank_eq_degLK_mul hKM hM)
    (fun x hx => norm_Kn p K hK hN (hMN hx))]

theorem IsFrob.pow_apply (hK : FiniteDimensional ℚ_[p] K) {σ : GK p K} (h : IsFrob p K σ) {m : ℕ}
    (hm : ¬ p ∣ m) (i : ℕ) {ζ : PadicAlgCl p} (hζ : ζ ^ m = 1) : (σ ^ i) ζ = ζ ^ (qK p K ^ i) := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, (isFrob_iff hK σ).1 h ζ m hm hζ, ← pow_mul, ← pow_succ']

theorem resGK_frobK (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) {f : ℕ}
    (hf : qK p L = qK p K ^ f) :
    (QuotientGroup.mk (resGK h (frobK p L)) : GalLK p K (MaximalUnramifiedExtension p K)) = frobLK p K (MaximalUnramifiedExtension p K) ^ f := by
  rw [frobLK_pow, mk_eq_mk_iff]
  intro x hx
  refine eqOn_Kur (fun ζ m hm hζ => ?_) hK hx
  rw [resGK_apply, (isFrob_iff hL _).1 (isFrob_frobK hL) ζ m hm hζ, hf,
    IsFrob.pow_apply hK (isFrob_frobK hK) hm f hζ]

end ReciprocityTheory.DiscreteGroups.LocalClassField
