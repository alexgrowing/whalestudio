import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSum

set_option autoImplicit false

open DividedPowers CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.LatCpl

def Cpl (l : ℕ) (G : Type*) [AddCommGroup G] : Prop :=
  (∀ x : G, (∀ n : ℕ, ∃ y : G, x = l ^ n • y) → x = 0) ∧
    ∀ s : ℕ → G, (∀ n : ℕ, ∃ y : G, s (n + 1) - s n = l ^ n • y) →
      ∃ L : G, ∀ n : ℕ, ∃ y : G, L - s n = l ^ n • y

theorem Cpl.of_subsingleton (l : ℕ) (G : Type*) [AddCommGroup G] [Subsingleton G] : Cpl l G :=
  ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => ⟨0, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩⟩

theorem Cpl.ext {l : ℕ} {N P Q : Type*} [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    (j : N →+ P) (π : P →+ Q) (hj : Function.Injective j) (hπ : Function.Surjective π)
    (hex : ∀ x, π x = 0 ↔ ∃ y, j y = x) (htf : ∀ (n : ℕ) (q : Q), l ^ n • q = 0 → q = 0)
    (hN : Cpl l N) (hQ : Cpl l Q) : Cpl l P := by
  refine ⟨fun x h => ?_, fun s h => ?_⟩
  · have hπx : π x = 0 := hQ.1 _ fun n => by
      obtain ⟨y, hy⟩ := h n
      exact ⟨π y, by rw [hy, map_nsmul]⟩
    obtain ⟨x', rfl⟩ := (hex x).1 hπx
    have : x' = 0 := hN.1 x' fun n => by
      obtain ⟨y, hy⟩ := h n
      have h0 : π y = 0 := htf n _ (by rw [← map_nsmul, ← hy]; exact hπx)
      obtain ⟨y', rfl⟩ := (hex y).1 h0
      exact ⟨y', hj (by rw [hy, map_nsmul])⟩
    rw [this, map_zero]
  · choose y hy using h
    obtain ⟨q, hq⟩ := hQ.2 (fun n => π (s n)) (fun n => ⟨π (y n), by
      rw [← map_sub, ← map_nsmul, hy]⟩)
    choose z hz using hq
    obtain ⟨p, rfl⟩ := hπ q
    choose w hw using fun n => hπ (z n)
    have ht : ∀ n, π (s n + l ^ n • w n - p) = 0 := fun n => by
      rw [map_sub, map_add, map_nsmul, hw, ← hz n]; abel
    choose t ht' using fun n => (hex _).1 (ht n)
    have step : ∀ n, ∃ v : N, t (n + 1) - t n = l ^ n • v := fun n => by
      have e : j (t (n + 1) - t n) = l ^ n • (y n + l • w (n + 1) - w n) := by
        rw [map_sub, ht', ht', smul_sub, smul_add, ← hy, pow_succ, mul_smul]; abel
      have h0 : π (y n + l • w (n + 1) - w n) = 0 := htf n _ (by
        rw [← map_nsmul, ← e]; exact (hex _).2 ⟨_, rfl⟩)
      obtain ⟨v, hv⟩ := (hex _).1 h0
      exact ⟨v, hj (by rw [e, map_nsmul, hv])⟩
    obtain ⟨T, hT⟩ := hN.2 t step
    choose u hu using hT
    refine ⟨j T + p, fun n => ⟨j (u n) + w n, ?_⟩⟩
    have := congrArg j (hu n)
    rw [map_sub, ht', map_nsmul] at this
    rw [smul_add, ← this]; abel

theorem exists_pi {P V Q : Type*} [AddCommGroup P] [AddCommGroup V] [AddCommGroup Q] (K : AddSubgroup P)
    (g : V →+ P) (mk : V →+ Q) (hmk : Function.Surjective mk) (h1 : ∀ x, ∃ w, x - g w ∈ K)
    (h2 : ∀ w, g w ∈ K ↔ mk w = 0) :
    ∃ π : P →+ Q, Function.Surjective π ∧ ∀ x, π x = 0 ↔ x ∈ K := by
  choose c hc using h1
  have hadd : ∀ x y, mk (c (x + y)) = mk (c x) + mk (c y) := fun x y => by
    rw [← sub_eq_zero, ← map_add, ← map_sub, ← h2, map_sub, map_add]
    have := K.sub_mem (K.add_mem (hc x) (hc y)) (hc (x + y))
    have e : g (c (x + y)) - (g (c x) + g (c y)) = x - g (c x) + (y - g (c y)) - (x + y - g (c (x + y))) := by abel
    rwa [e]
  refine ⟨AddMonoidHom.mk' (fun x => mk (c x)) hadd, fun q => ?_, fun x => ?_⟩
  · obtain ⟨w, rfl⟩ := hmk q
    refine ⟨g w, ?_⟩
    show mk (c (g w)) = mk w
    rw [← sub_eq_zero, ← map_sub, ← h2, map_sub]
    have := K.neg_mem (hc (g w))
    rwa [neg_sub] at this
  · show mk (c x) = 0 ↔ x ∈ K
    rw [← h2]
    constructor
    · intro h
      have := K.add_mem (hc x) h
      rwa [sub_add_cancel] at this
    · intro h
      have := K.sub_mem h (hc x)
      rwa [sub_sub_cancel] at this

theorem smodEq_iff {R : Type*} [CommRing R] (l n : ℕ) (x y : R) :
    x ≡ y [SMOD (Ideal.span {(l : R)} ^ n • (⊤ : Submodule R R))] ↔ ∃ z : R, x - y = l ^ n • z := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← ha, nsmul_eq_mul, Nat.cast_pow, mul_comm]⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [ha, nsmul_eq_mul, Nat.cast_pow, mul_comm]⟩

theorem cpl_of_adic {R : Type*} [CommRing R] (l : ℕ) (h : IsAdicComplete (Ideal.span {(l : R)}) R) : Cpl l R := by
  refine ⟨fun x hx => ?_, fun s hs => ?_⟩
  · refine h.toIsHausdorff.haus' x fun n => ?_
    obtain ⟨y, hy⟩ := hx n
    exact (smodEq_iff l n x 0).2 ⟨y, by rw [sub_zero, hy]⟩
  · have hc : ∀ {a b : ℕ}, a ≤ b → s a ≡ s b [SMOD (Ideal.span {(l : R)} ^ a • (⊤ : Submodule R R))] := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => exact SModEq.refl _
      | succ b hab ih =>
        refine ih.trans ?_
        obtain ⟨y, hy⟩ := hs b
        have h1 : s (b + 1) ≡ s b [SMOD (Ideal.span {(l : R)} ^ b • (⊤ : Submodule R R))] :=
          (smodEq_iff l b _ _).2 ⟨y, hy⟩
        exact (h1.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hab))).symm
    obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' s hc
    exact ⟨L, fun n => (smodEq_iff l n _ _).1 (hL n).symm⟩

theorem adic_of_cpl {R : Type*} [CommRing R] (l : ℕ) (h : Cpl l R) : IsAdicComplete (Ideal.span {(l : R)}) R := by
  refine { haus' := fun x hx => ?_, prec' := fun s hs => ?_ }
  · exact h.1 x fun n => by
      obtain ⟨y, hy⟩ := (smodEq_iff l n x 0).1 (hx n)
      exact ⟨y, by rwa [sub_zero] at hy⟩
  · obtain ⟨L, hL⟩ := h.2 s fun n => (smodEq_iff l n _ _).1 (hs n.le_succ).symm
    exact ⟨L, fun n => ((smodEq_iff l n _ _).2 (hL n)).symm⟩

section Lat

open CrystallineSemistableComparison.Pb.Lat

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

def F (i : ℕ) : AddSubgroup (A f ξ l M) :=
  (Ideal.span {f ξ ^ i}).toAddSubgroup.comap (ι f ξ l M).toAddMonoidHom

theorem mem_F {i : ℕ} {x : A f ξ l M} : x ∈ F f ξ l M i ↔ ι f ξ l M x ∈ Ideal.span {f ξ ^ i} := Iff.rfl

def S (i : ℕ) : AddSubgroup B :=
  AddSubgroup.closure {b | ∃ (w : W) (j : ℕ), i ≤ j ∧ b = f w * dpE f ξ l M j}

def co (l M i : ℕ) : ℚ := ((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i

theorem dpE_eq (i : ℕ) : dpE f ξ l M i = co l M i • f ξ ^ i := by
  simp only [dpE, η, co, smul_pow, smul_smul]

theorem co_ne {l : ℕ} (hl : l ≠ 0) (M i : ℕ) : co l M i ≠ 0 := by
  have : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  have h2 : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  unfold co
  positivity

theorem co_succ {l : ℕ} (hl : l ≠ 0) (M i : ℕ) :
    (((l ^ M * (i + 1) : ℕ) : ℚ)) * co l M (i + 1) = co l M i := by
  have h1 : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  have h2 : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h3 : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hL : (l : ℚ) ^ M ≠ 0 := pow_ne_zero _ h1
  simp only [co, Nat.factorial_succ]
  push_cast
  generalize (l : ℚ) ^ M = L at hL
  field_simp
  rw [pow_succ, mul_comm, mul_assoc, one_div, inv_mul_cancel₀ hL, mul_one]

theorem dpE_mem (j : ℕ) : dpE f ξ l M j ∈ Ideal.span {f ξ ^ j} := by
  rw [dpE_eq, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem span_mono {i j : ℕ} (h : i ≤ j) : (Ideal.span {f ξ ^ j} : Ideal B) ≤ Ideal.span {f ξ ^ i} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)

theorem S_le_span (i : ℕ) {x : B} (hx : x ∈ S f ξ l M i) : x ∈ Ideal.span {f ξ ^ i} := by
  have : S f ξ l M i ≤ (Ideal.span {f ξ ^ i}).toAddSubgroup := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, j, hj, rfl⟩
    exact Ideal.mul_mem_left _ _ (span_mono f ξ hj (dpE_mem f ξ l M j))
  exact this hx

theorem sub_le_S {x : B} (hx : x ∈ sub f ξ l M) : x ∈ S f ξ l M 0 := by
  obtain ⟨n, c, rfl⟩ := (GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff f ξ l M x).1 hx
  exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ⟨c i, i, Nat.zero_le _, rfl⟩

theorem head (i : ℕ) {y : B} (hy : y ∈ S f ξ l M i) :
    ∃ w : W, y - f w * dpE f ξ l M i ∈ S f ξ l M (i + 1) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, j, hj, rfl⟩ := hx
    rcases hj.eq_or_lt with rfl | hj
    · exact ⟨w, by rw [sub_self]; exact AddSubgroup.zero_mem _⟩
    · exact ⟨0, by
        rw [map_zero, zero_mul, sub_zero]
        exact AddSubgroup.subset_closure ⟨w, j, hj, rfl⟩⟩
  | zero => exact ⟨0, by rw [map_zero, zero_mul, sub_zero]; exact AddSubgroup.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    have := AddSubgroup.add_mem _ ha hb
    convert this using 1
    rw [map_add]; ring
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨-a, ?_⟩
    have := AddSubgroup.neg_mem _ ha
    convert this using 1
    rw [map_neg]; ring

variable {f ξ l}

theorem l_ne {m : ℕ} (h : Hyp f ξ l m) : l ≠ 0 := by
  rintro rfl
  exact h.l0 Nat.cast_zero

theorem dvd_of_mem {m : ℕ} (h : Hyp f ξ l m) {i : ℕ} (hi : i < m) {w : W}
    (hw : f w * dpE f ξ l M i ∈ Ideal.span {f ξ ^ (i + 1)}) : ξ ∣ w := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hw
  have hc := co_ne (l_ne h) M i
  refine h.gr i hi w ((co l M i)⁻¹ • b) ?_
  rw [dpE_eq, mul_smul_comm, mul_comm b] at hb
  rw [mul_smul_comm, hb, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem xi_mul {m : ℕ} (h : Hyp f ξ l m) (i : ℕ) :
    f ξ * dpE f ξ l M i = ((l ^ M * (i + 1) : ℕ) : B) * dpE f ξ l M (i + 1) := by
  rw [dpE_eq, dpE_eq, mul_smul_comm, ← pow_succ', ← co_succ (l_ne h) M i, mul_smul,
    Nat.cast_smul_eq_nsmul ℚ, nsmul_eq_mul]

theorem S_push {m : ℕ} (h : Hyp f ξ l m) {i : ℕ} (hi : i < m) {x : B} (hx : x ∈ S f ξ l M i)
    (hx' : x ∈ Ideal.span {f ξ ^ (i + 1)}) : x ∈ S f ξ l M (i + 1) := by
  obtain ⟨w, hw⟩ := head f ξ l M i hx
  have h1 : f w * dpE f ξ l M i ∈ Ideal.span {f ξ ^ (i + 1)} := by
    have := Ideal.sub_mem _ hx' (S_le_span f ξ l M (i + 1) hw)
    rwa [sub_sub_cancel] at this
  obtain ⟨d, rfl⟩ := dvd_of_mem M h hi h1
  have h2 : f (ξ * d) * dpE f ξ l M i ∈ S f ξ l M (i + 1) := by
    refine AddSubgroup.subset_closure ⟨d * ((l ^ M * (i + 1) : ℕ) : W), i + 1, le_rfl, ?_⟩
    rw [map_mul, map_mul, map_natCast, mul_comm (f ξ), mul_assoc, xi_mul M h, mul_assoc]
  have := AddSubgroup.add_mem _ hw h2
  rwa [sub_add_cancel] at this

theorem mem_S {m : ℕ} (h : Hyp f ξ l m) {i : ℕ} (hi : i ≤ m) {x : B} (hx : x ∈ sub f ξ l M)
    (hx' : x ∈ Ideal.span {f ξ ^ i}) : x ∈ S f ξ l M i := by
  induction i with
  | zero => exact sub_le_S f ξ l M hx
  | succ i ih =>
    exact S_push M h hi (ih (by omega) (span_mono f ξ i.le_succ hx')) hx'

variable (f ξ l)

def gA (i : ℕ) (w : W) : A f ξ l M := ofW f ξ l M w * dpA f ξ l M i

theorem ι_gA (i : ℕ) (w : W) : ι f ξ l M (gA f ξ l M i w) = f w * dpE f ξ l M i := by
  rw [gA, map_mul, ι_ofW, ι_dpA]

theorem gA_mem (i : ℕ) (w : W) : gA f ξ l M i w ∈ F f ξ l M i := by
  rw [mem_F, ι_gA]
  exact Ideal.mul_mem_left _ _ (dpE_mem f ξ l M i)

def gF (i : ℕ) : W →+ F f ξ l M i :=
  AddMonoidHom.mk' (fun w => ⟨gA f ξ l M i w, gA_mem f ξ l M i w⟩) fun a b => by
    apply Subtype.ext
    show gA f ξ l M i (a + b) = gA f ξ l M i a + gA f ξ l M i b
    simp only [gA, map_add, add_mul]

variable {f ξ l}

theorem gA_succ {m : ℕ} (h : Hyp f ξ l m) {i : ℕ} (hi : i < m) (w : W) :
    gA f ξ l M i w ∈ F f ξ l M (i + 1) ↔ ξ ∣ w := by
  rw [mem_F, ι_gA]
  constructor
  · exact dvd_of_mem M h hi
  · rintro ⟨d, rfl⟩
    rw [map_mul, mul_comm (f ξ), mul_assoc, xi_mul M h]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (dpE_mem f ξ l M (i + 1)))

theorem exists_sub_mem {m : ℕ} (h : Hyp f ξ l m) {i : ℕ} (hi : i < m) {x : A f ξ l M}
    (hx : x ∈ F f ξ l M i) : ∃ w, x - gA f ξ l M i w ∈ F f ξ l M (i + 1) := by
  have h1 := mem_S M h hi.le x.2 hx
  obtain ⟨w, hw⟩ := head f ξ l M i h1
  refine ⟨w, ?_⟩
  rw [mem_F, map_sub, ι_gA]
  exact S_le_span f ξ l M (i + 1) hw

theorem F_le {i : ℕ} : F f ξ l M (i + 1) ≤ F f ξ l M i :=
  fun _ hx => span_mono f ξ i.le_succ hx

theorem cpl_step {m : ℕ} (h : Hyp f ξ l m) {i : ℕ} (hi : i < m) (hN : Cpl l (F f ξ l M (i + 1))) :
    Cpl l (F f ξ l M i) := by
  haveI := h.dom
  obtain ⟨π, hs, hk⟩ := exists_pi ((F f ξ l M (i + 1)).addSubgroupOf (F f ξ l M i))
    (gF f ξ l M i) (Ideal.Quotient.mk (Ideal.span {ξ})).toAddMonoidHom Ideal.Quotient.mk_surjective
    (fun x => by
      obtain ⟨w, hw⟩ := exists_sub_mem M h hi x.2
      exact ⟨w, AddSubgroup.mem_addSubgroupOf.2 hw⟩)
    (fun w => by
      rw [AddSubgroup.mem_addSubgroupOf]
      refine (gA_succ M h hi w).trans ?_
      show _ ↔ Ideal.Quotient.mk _ w = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton])
  refine Cpl.ext (AddSubgroup.inclusion (F_le M)) π (AddSubgroup.inclusion_injective _) hs
    (fun x => ?_) (fun n q hq => ?_) hN (cpl_of_adic l h.cpl)
  · rw [hk, AddSubgroup.mem_addSubgroupOf]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
  · rw [nsmul_eq_mul] at hq
    exact (mul_eq_zero.1 hq).resolve_left (by
      rw [Nat.cast_pow]
      exact pow_ne_zero _ h.l0)

theorem cpl_F {m : ℕ} (h : Hyp f ξ l m) (d i : ℕ) (hd : i + d = m) : Cpl l (F f ξ l M i) := by
  induction d generalizing i with
  | zero =>
    have hm : i = m := by omega
    subst hm
    haveI : Subsingleton (F f ξ l M i) := ⟨fun a b => by
      have key : ∀ c : F f ξ l M i, c = 0 := fun c => by
        apply Subtype.ext
        apply ι_injective f ξ l M
        have := c.2
        rw [mem_F, h.nil, Ideal.span_singleton_eq_bot.2 rfl] at this
        simpa using this
      rw [key a, key b]⟩
    exact Cpl.of_subsingleton l _
  | succ d ih =>
    exact cpl_step M h (by omega) (ih (i + 1) (by omega))

theorem F_zero (x : A f ξ l M) : x ∈ F f ξ l M 0 := by
  rw [mem_F, pow_zero, Ideal.span_singleton_one]
  trivial

theorem isAdicComplete_A {m : ℕ} (h : Hyp f ξ l m) :
    IsAdicComplete (Ideal.span {(l : A f ξ l M)}) (A f ξ l M) := by
  refine adic_of_cpl l ?_
  refine Cpl.ext (Q := PUnit.{1}) (F f ξ l M 0).subtype 0 Subtype.val_injective
    (fun _ => ⟨0, rfl⟩) (fun x => ⟨fun _ => ⟨⟨x, F_zero M x⟩, rfl⟩, fun _ => rfl⟩)
    (fun _ _ _ => rfl) (cpl_F M h m 0 (by omega)) (Cpl.of_subsingleton l _)

end Lat

end GlobalTheory.CompanionTheory.LatCpl
