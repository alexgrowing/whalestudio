import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

def HJb (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ)
    (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ),
    PairPath LL B nu ka → jointType F LL nu ka ≤ Pol F (r + K) B

def HJc (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N))
    (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ),
    jointType F LL nu ka ≠ ⊥ →
    ∃ b' b'' : Fin N → ℕ, (∃ P1 : PPath r N LL b', P1.mu = nu) ∧ ∃ P2 : PPath K N LL b'', P2.mu = ka

lemma domLE_first {n : ℕ} [NeZero n] {la mu : Fin n → ℤ} (h : DomLE la mu) : la 0 ≤ mu 0 := by
  have e : (univ.filter (· ≤ (0 : Fin n))) = {0} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hb
      have h2 : b.val ≤ (0 : Fin n).val := hb
      exact Fin.ext (by simpa using h2)
    · rintro rfl; exact le_refl _
  have := h.1 0
  rw [e] at this
  simpa using this

lemma domLE_last {n : ℕ} [NeZero n] {la mu : Fin n → ℤ} (h : DomLE la mu) : mu (lastIdx n) ≤ la (lastIdx n) := by
  have key : ∀ f : Fin n → ℤ, ∑ b, f b = ∑ b ∈ univ.filter (· ≠ lastIdx n), f b + f (lastIdx n) := by
    intro f
    rw [Finset.filter_ne', Finset.sum_erase_add _ _ (Finset.mem_univ _)]
  have h2 := h.2
  rw [key la, key mu] at h2
  have h3 : ∑ b ∈ univ.filter (· ≠ lastIdx n), la b ≤ ∑ b ∈ univ.filter (· ≠ lastIdx n), mu b := by
    by_cases hn : 2 ≤ n
    · have e : univ.filter (· ≠ lastIdx n) = univ.filter (· ≤ (⟨n - 2, by omega⟩ : Fin n)) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, lastIdx, Fin.le_def, ne_eq, Fin.ext_iff]
        have := b.2
        omega
      rw [e]; exact h.1 _
    · have e : univ.filter (· ≠ lastIdx n) = ∅ := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, lastIdx, ne_eq, Fin.ext_iff, Finset.notMem_empty,
          iff_false, not_not]
        have := b.2
        omega
      rw [e]; simp
  linarith

def prin {n : ℕ} (mu : Fin n → ℤ) : Set (Fin n → ℤ) := {la | Dominant la ∧ DomLE la mu}

lemma prin_lower {n : ℕ} (mu : Fin n → ℤ) : DomLowerSet (prin mu) :=
  ⟨fun _ h => h.1, fun _ h _ hnu hle => ⟨hnu, fun a => (hle.1 a).trans (h.2.1 a), hle.2.trans h.2.2⟩⟩

lemma domLE_refl {n : ℕ} (mu : Fin n → ℤ) : DomLE mu mu := ⟨fun _ => le_refl _, rfl⟩

lemma size_of_path {n N : ℕ} {LL : Letters (Fin N)} {b : Fin N → ℕ} (P : PPath n N LL b) (i : Fin N) :
    (b i : ℤ) = if LL.vec i then ∑ a, P.mu i.succ a - ∑ a, P.mu i.castSucc a
      else ∑ a, P.mu i.castSucc a - ∑ a, P.mu i.succ a := by
  have := P.step i
  split_ifs at this ⊢ with hv
  · rw [← this.2.2, Finset.sum_sub_distrib]
  · rw [← this.2.2, Finset.sum_sub_distrib]

lemma sizes_eq {n N : ℕ} {LL : Letters (Fin N)} {b b' : Fin N → ℕ} (P : PPath n N LL b) (P' : PPath n N LL b')
    (h : ∀ i, ∑ a, P.mu i a = ∑ a, P'.mu i a) : b = b' := by
  funext i
  have h1 := size_of_path P i
  have h2 := size_of_path P' i
  rw [h, h] at h1
  exact Int.natCast_inj.1 (h1.trans h2.symm)

lemma pp_down (D : Formalism.BasicNotions.D7) {N r K : ℕ} [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ)
    (hK : N + r ≤ K) (L : List (PathInequality N))
    (x1 q1 : Fin (N + 1) → Fin r → ℤ) (x2 q2 : Fin (N + 1) → Fin K → ℤ)
    (hx : (∃ P : PPath (r + K) N LL B, P.mu = joinPT x1 x2) ∧ ∀ e ∈ L, e.Sat x1 x2)
    (h1 : ∃ b', ∃ P1 : PPath r N LL b', P1.mu = q1) (h2 : ∃ b'', ∃ P2 : PPath K N LL b'', P2.mu = q2)
    (hle1 : ∀ i, DomLE (q1 i) (x1 i)) (hle2 : ∀ i, DomLE (q2 i) (x2 i)) :
    (∃ P : PPath (r + K) N LL B, P.mu = joinPT q1 q2) ∧ ∀ e ∈ L, e.Sat q1 q2 := by
  obtain ⟨c', c'', hc, ⟨Q1, hQ1⟩, ⟨Q2, hQ2⟩, hC⟩ := (prvB1_of_D7 D N r K LL B hK x1 x2).1 hx.1
  obtain ⟨b', P1, hP1⟩ := h1
  obtain ⟨b'', P2, hP2⟩ := h2
  have e1 : b' = c' := sizes_eq P1 Q1 fun i => by rw [hP1, hQ1]; exact (hle1 i).2
  have e2 : b'' = c'' := sizes_eq P2 Q2 fun i => by rw [hP2, hQ2]; exact (hle2 i).2
  constructor
  · refine (prvB1_of_D7 D N r K LL B hK q1 q2).2 ⟨b', b'', by rw [e1, e2]; exact hc, ⟨P1, hP1⟩, ⟨P2, hP2⟩, ?_⟩
    intro i
    have := hC i
    unfold CondC at this ⊢
    split_ifs at this ⊢ with hv
    · exact (domLE_first (hle2 _)).trans (this.trans (domLE_last (hle1 _)))
    · exact (domLE_first (hle2 _)).trans (this.trans (domLE_last (hle1 _)))
  · intro e he
    have := hx.2 e he
    cases e with
    | nuGe i th =>
      have h3 : th ≤ x1 i (lastIdx r) := this
      exact (h3.trans (domLE_last (hle1 i)) : th ≤ q1 i (lastIdx r))
    | kaLe i M =>
      have h3 : x2 i 0 ≤ M := this
      exact ((domLE_first (hle2 i)).trans h3 : q2 i 0 ≤ M)
    | mix j i m =>
      have h3 : x2 j 0 + m ≤ x1 i (lastIdx r) := this
      have h4 := domLE_first (hle2 j)
      have h5 := domLE_last (hle1 i)
      exact (by linarith : q2 j 0 + m ≤ q1 i (lastIdx r))

section Frac

variable (O : Type*) [CommRing O] [IsDomain O] {σ : Type*}

lemma map_smul' {O : Type*} [CommRing O] [IsDomain O] {σ : Type*} (a : O) (f : MvPolynomial σ O) :
    MvPolynomial.map (algebraMap O (KK O)) (a • f) =
      algebraMap O (KK O) a • MvPolynomial.map (algebraMap O (KK O)) f := by
  rw [MvPolynomial.smul_eq_C_mul, _root_.map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

def fracSub (X : Submodule O (MvPolynomial σ O)) : Submodule (KK O) (MvPolynomial σ (KK O)) where
  carrier := {y | ∃ a : O, a ≠ 0 ∧ ∃ f' ∈ X, MvPolynomial.map (algebraMap O (KK O)) f' = algebraMap O (KK O) a • y}
  zero_mem' := ⟨1, one_ne_zero, 0, X.zero_mem, by simp⟩
  add_mem' := by
    rintro y1 y2 ⟨a1, h1, f1, hf1, e1⟩ ⟨a2, h2, f2, hf2, e2⟩
    refine ⟨a1 * a2, mul_ne_zero h1 h2, a2 • f1 + a1 • f2, X.add_mem (X.smul_mem _ hf1) (X.smul_mem _ hf2), ?_⟩
    rw [_root_.map_add, map_smul', map_smul', e1, e2, smul_add, smul_smul, smul_smul, _root_.map_mul,
      mul_comm (algebraMap O (KK O) a2)]
  smul_mem' := by
    rintro c y ⟨a, h, f', hf, e⟩
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := O) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap O (KK O) d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hd0
    have h3 : algebraMap O (KK O) d * (algebraMap O (KK O) n / algebraMap O (KK O) d) = algebraMap O (KK O) n := by
      field_simp
    refine ⟨a * d, mul_ne_zero h hd0, n • f', X.smul_mem _ hf, ?_⟩
    rw [map_smul', e, smul_smul, smul_smul, _root_.map_mul, mul_assoc, h3, mul_comm]

lemma fracSub_top : fracSub O (⊤ : Submodule O (MvPolynomial σ O)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  refine MvPolynomial.induction_on' (P := fun y => y ∈ fracSub O (⊤ : Submodule O (MvPolynomial σ O))) y ?_ ?_
  · intro u c
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := O) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap O (KK O) d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hd0
    have h3 : algebraMap O (KK O) d * (algebraMap O (KK O) n / algebraMap O (KK O) d) = algebraMap O (KK O) n := by
      field_simp
    refine ⟨d, hd0, monomial u n, Submodule.mem_top, ?_⟩
    rw [MvPolynomial.map_monomial, MvPolynomial.smul_monomial, smul_eq_mul, h3]
  · intro p q hp hq
    exact Submodule.add_mem _ hp hq

lemma pol_of_map {O : Type*} [CommRing O] [IsDomain O] {ι : Type*} {n : ℕ} (d : ι → ℕ)
    (f : MvPolynomial (ι × Fin n) O) (h : MvPolynomial.map (algebraMap O (KK O)) f ∈ Pol (KK O) n d) :
    f ∈ Pol O n d := by
  unfold Pol at h ⊢
  rw [MvPolynomial.mem_restrictSupport_iff] at h ⊢
  rwa [MvPolynomial.support_map_of_injective _ (IsFractionRing.injective O (KK O))] at h

end Frac

theorem integral_joint_type_sum_of_parts (D : Formalism.BasicNotions.D7) (h16 : PairedPathIndependence D) (hb : HJb D) (hc : HJc D) : IntegralJointTypeSum D := by
  intro p hp O _ _ _ S N r K _ _ LL B hK PP L hPPdef
  have hcz : CharZero O := Formalism.MainNotions.G.GLWeightTheory.dvr_charZero_of_prime S hp.out
  have hczK : CharZero (KK O) := Formalism.MainNotions.G.GLWeightTheory.dvr_fraction_field_charZero_prime S hp.out
  have hPP : ∀ q ∈ PP, ∃ P : PPath (r + K) N LL B, P.mu = joinPT q.1 q.2 := by
    intro q hq; rw [hPPdef] at hq; exact hq.1
  have hsat := joint_type_lattice_saturated D h16 p O S N r K LL B hK PP hPP
  obtain ⟨_, h16b⟩ := h16 O N r K LL B
  have hdown : ∀ x ∈ PP, ∀ q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ),
      (∃ b', ∃ P1 : PPath r N LL b', P1.mu = q.1) → (∃ b'', ∃ P2 : PPath K N LL b'', P2.mu = q.2) →
      (∀ i, DomLE (q.1 i) (x.1 i)) → (∀ i, DomLE (q.2 i) (x.2 i)) → q ∈ PP := by
    intro x hx q h1 h2 h3 h4
    rw [hPPdef] at hx ⊢
    exact pp_down D LL B hK L x.1 q.1 x.2 q.2 hx h1 h2 h3 h4
  have hpp : ∀ x ∈ PP, PairPath LL B x.1 x.2 := fun x hx => pairPath_of_path D LL B hK _ _ (hPP x hx)
  have hself : ∀ x ∈ PP, ∀ i, x.1 i ∈ prin (x.1 i) ∧ x.2 i ∈ prin (x.2 i) := by
    intro x hx i
    obtain ⟨b', b'', _, ⟨P1, h1⟩, ⟨P2, h2⟩⟩ := hpp x hx
    exact ⟨⟨h1 ▸ P1.dom i, domLE_refl _⟩, ⟨h2 ▸ P2.dom i, domLE_refl _⟩⟩
  have hprin := fun x : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) =>
    h16b (fun i => prin (x.1 i)) (fun i => prin (x.2 i)) (fun i => prin_lower _) (fun i => prin_lower _)
  have hW : ∀ x ∈ PP, (⨆ q ∈ {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) |
        ∀ i, q.1 i ∈ prin (x.1 i) ∧ q.2 i ∈ prin (x.2 i)}, jointType (KK O) LL q.1 q.2) ≤
      ⨆ q ∈ PP, jointType (KK O) LL q.1 q.2 := by
    intro x hx
    refine iSup₂_le fun q hq => ?_
    by_cases h0 : jointType (KK O) LL q.1 q.2 = ⊥
    · rw [h0]; exact bot_le
    · obtain ⟨b', b'', hP1, hP2⟩ := hc (KK O) N r K LL q.1 q.2 h0
      exact le_iSup₂_of_le q (hdown x hx q ⟨b', hP1⟩ ⟨b'', hP2⟩ (fun i => (hq i).1.2) (fun i => (hq i).2.2)) le_rfl
  apply Set.Subset.antisymm
  · intro f hf
    have hf' : f ∈ XXZ O PP := hf
    show MvPolynomial.map (algebraMap O (KK O)) f ∈ ⨆ q ∈ PP, jointType (KK O) LL q.1 q.2
    unfold XXZ at hf'
    induction hf' using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨q, hq, I', I'', h1, h2, rfl⟩ := hg
      have h3 := (Set.ext_iff.1 (hprin q) (PsiPl O q.1 I' * PsiTan O q.2 I'')).2
        (Submodule.subset_span ⟨q.1, q.2, I', I'', hpp q hq, hself q hq, h1, h2, rfl⟩)
      exact hW q hq h3.2
    | zero => rw [_root_.map_zero]; exact Submodule.zero_mem _
    | add x y _ _ h1 h2 => rw [_root_.map_add]; exact Submodule.add_mem _ (h1 (by assumption)) (h2 (by assumption))
    | smul a x _ h => rw [map_smul']; exact Submodule.smul_mem _ _ (h (by assumption))
  · intro f hf
    have hf' : MvPolynomial.map (algebraMap O (KK O)) f ∈ ⨆ q ∈ PP, jointType (KK O) LL q.1 q.2 := hf
    have hle : (⨆ q ∈ PP, jointType (KK O) LL q.1 q.2) ≤ fracSub O (XXZ O PP) := by
      refine iSup₂_le fun q hq y hy => ?_
      obtain ⟨a, ha, f', -, e⟩ : y ∈ fracSub O (⊤ : Submodule O (MvPolynomial (Fin N × Fin (r + K)) O)) := by
        rw [fracSub_top]; exact Submodule.mem_top
      have hy' : MvPolynomial.map (algebraMap O (KK O)) f' ∈ jointType (KK O) LL q.1 q.2 := by
        rw [e]; exact Submodule.smul_mem _ _ hy
      have hpol : f' ∈ Pol O (r + K) B := pol_of_map B f' (hb (KK O) N r K LL B q.1 q.2 (hpp q hq) hy')
      have hin : MvPolynomial.map (algebraMap O (KK O)) f' ∈
          ⨆ q' ∈ {q' : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) |
            ∀ i, q'.1 i ∈ prin (q.1 i) ∧ q'.2 i ∈ prin (q.2 i)}, jointType (KK O) LL q'.1 q'.2 :=
        (le_iSup₂_of_le q (hself q hq) le_rfl : jointType (KK O) LL q.1 q.2 ≤ _) hy'
      have h3 := (Set.ext_iff.1 (hprin q) f').1 ⟨hpol, hin⟩
      refine ⟨a, ha, f', ?_, e⟩
      refine Submodule.span_le.2 ?_ h3
      rintro g ⟨nu, ka, I', I'', ⟨b', b'', _, hP1, hP2⟩, hmem, h1, h2, rfl⟩
      exact Submodule.subset_span ⟨(nu, ka), hdown q hq (nu, ka) ⟨b', hP1⟩ ⟨b'', hP2⟩
        (fun i => (hmem i).1.2) (fun i => (hmem i).2.2), I', I'', h1, h2, rfl⟩
    obtain ⟨a, ha, f', hf'', e⟩ := hle hf'
    rw [← map_smul'] at e
    have h5 := MvPolynomial.map_injective _ (IsFractionRing.injective O (KK O)) e
    exact hsat f a ha (h5 ▸ hf'')

end Formalism.MainNotions.LemmaBAlt
