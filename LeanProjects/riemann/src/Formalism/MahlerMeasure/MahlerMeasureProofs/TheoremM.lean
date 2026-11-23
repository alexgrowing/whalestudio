import Formalism.MahlerMeasure.StatementTM

namespace Formalism.GM.TM

section S0
open M MvPolynomial Finset

variable {N : ℕ}

theorem letters_ext {K : ℕ} {L1 L2 : Letters K} (hv : L1.vec = L2.vec) (hd : L1.deg = L2.deg) : L1 = L2 := by
  cases L1; cases L2; simp_all

theorem takeD_setTies_update (LL : Letters N) (T : TieData) (n : Fin T.t → ℕ) (i : Fin T.t) (x : ℕ) :
    (LL.setTies T (Function.update n i x)).takeD (T.pos i + 1) = (LL.setTies T n).takeD (T.pos i + 1) := by
  refine letters_ext rfl ?_
  funext a
  simp only [Letters.takeD, Letters.setTies]
  split_ifs with h1 h2
  · apply Function.update_of_ne
    intro heq
    have := Classical.choose_spec h2
    rw [heq] at this
    have := a.isLt
    simp at this; omega
  · rfl
  · rfl

theorem setTies_deg_eta (LL : Letters N) (T : TieData) (hT : StrictMono T.pos) (n : Fin T.t → ℕ) (i : Fin T.t)
    (h : T.pos i + 1 < N) : (LL.setTies T n).deg ⟨T.pos i + 1, h⟩ = n i := by
  unfold Letters.setTies
  have hex : ∃ j, T.pos j + 1 = ((⟨T.pos i + 1, h⟩ : Fin N) : ℕ) := ⟨i, rfl⟩
  simp only [dif_pos hex]
  congr 1
  have := Classical.choose_spec hex
  exact hT.injective (by simpa using this)

theorem setTies_deg_mono (LL : Letters N) (T : TieData) (n n' : Fin T.t → ℕ) (hn : ∀ i, n i ≤ n' i) (a : Fin N) :
    (LL.setTies T n).deg a ≤ (LL.setTies T n').deg a := by
  unfold Letters.setTies
  dsimp only
  split_ifs with h
  · exact hn _
  · exact le_rfl

theorem takeD_total_eq (LL : Letters N) (T : TieData) (i : Fin T.t) (h : T.pos i + 1 < N) :
    (LL.takeD (T.pos i + 1)).total = T.S LL i := by
  unfold Letters.total TieData.S Letters.takeD
  dsimp only
  let g : ℕ → ℕ := fun a => if h : a < N then (if a ≤ T.pos i then LL.deg ⟨a, h⟩ else 0) else 0
  have e1 : (∑ a : Fin (T.pos i + 1), if h : (a : ℕ) < N then LL.deg ⟨a, h⟩ else 0) = ∑ a ∈ range (T.pos i + 1), g a := by
    rw [Fin.sum_univ_eq_sum_range (fun a => if h : a < N then LL.deg ⟨a, h⟩ else 0)]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [mem_range] at ha
    simp only [g]
    split_ifs <;> first | rfl | omega
  have e2 : (∑ a : Fin N, if (a : ℕ) ≤ T.pos i then LL.deg a else 0) = ∑ a ∈ range N, g a := by
    rw [← Fin.sum_univ_eq_sum_range g N]
    apply Finset.sum_congr rfl
    intro a _
    simp only [g, dif_pos a.isLt]
  rw [e1, e2, ← Finset.sum_range_add_sum_Ico g (by omega : T.pos i + 1 ≤ N)]
  have : ∑ a ∈ Ico (T.pos i + 1) N, g a = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    simp only [mem_Ico] at ha
    simp only [g]
    split_ifs <;> first | rfl | omega
  omega

theorem S_mono (LL : Letters N) (T : TieData) (n n' : Fin T.t → ℕ) (hn : ∀ i, n i ≤ n' i) (i : Fin T.t) :
    T.S (LL.setTies T n) i ≤ T.S (LL.setTies T n') i := by
  unfold TieData.S
  apply Finset.sum_le_sum
  intro a _
  split_ifs
  · exact setTies_deg_mono LL T n n' hn a
  · exact le_rfl
end S0

section S1
open M MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime]

theorem mem_intPol_of_norm {σ : Type} (x : MvPolynomial σ ℚ_[p]) (h : ∀ m, ‖x.coeff m‖ ≤ 1) :
    x ∈ IntPol p σ := by
  have : (x.coeffs : Set ℚ_[p]) ⊆ Set.range (algebraMap ℤ_[p] ℚ_[p]) := by
    intro a ha
    rw [Finset.mem_coe, mem_coeffs_iff] at ha
    obtain ⟨m, _, rfl⟩ := ha
    exact ⟨⟨x.coeff m, h m⟩, rfl⟩
  rw [← mem_range_map_iff_coeffs_subset] at this
  simpa [IntPol, LinearMap.mem_range, AlgHom.toLinearMap_apply, mapAlgHom_apply, Set.mem_range] using this

theorem exists_pow_smul_intPol {σ : Type} (x : MvPolynomial σ ℚ_[p]) :
    ∃ k : ℕ, ((p : ℚ_[p]) ^ k) • x ∈ IntPol p σ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (∑ m ∈ x.support, ‖x.coeff m‖) hp
  refine ⟨k, mem_intPol_of_norm _ fun m => ?_⟩
  rw [coeff_smul, smul_eq_mul, norm_mul, norm_pow, Padic.norm_p]
  by_cases hm : m ∈ x.support
  · have h1 : ‖x.coeff m‖ ≤ ∑ m ∈ x.support, ‖x.coeff m‖ :=
      Finset.single_le_sum (f := fun m => ‖x.coeff m‖) (fun _ _ => norm_nonneg _) hm
    have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
    rw [inv_pow, inv_mul_le_iff₀ hpk, mul_one]
    linarith
  · rw [notMem_support_iff.mp hm, norm_zero, mul_zero]; exact zero_le_one

theorem finrank_of_lattice_basis {σ : Type} (S : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) {n₀ : ℕ}
    (f : Fin n₀ → MvPolynomial σ ℚ_[p]) (hli : LinearIndependent ℤ_[p] f)
    (hsp : Submodule.span ℤ_[p] (Set.range f) = S.restrictScalars ℤ_[p] ⊓ IntPol p σ) :
    Module.finrank ℚ_[p] S = n₀ := by
  have hli' : LinearIndependent ℚ_[p] f := (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp hli
  have hS : Submodule.span ℚ_[p] (Set.range f) = S := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      have : f b ∈ Submodule.span ℤ_[p] (Set.range f) := Submodule.subset_span ⟨b, rfl⟩
      rw [hsp] at this
      exact (Submodule.mem_inf.mp this).1
    · intro x hx
      obtain ⟨k, hk⟩ := exists_pow_smul_intPol x
      have h1 : ((p : ℚ_[p]) ^ k) • x ∈ Submodule.span ℤ_[p] (Set.range f) := by
        rw [hsp]; exact Submodule.mem_inf.mpr ⟨S.smul_mem _ hx, hk⟩
      have h2 := Submodule.span_le_restrictScalars ℤ_[p] ℚ_[p] (Set.range f) h1
      have hp0 : ((p : ℚ_[p]) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
      have : x = ((p : ℚ_[p]) ^ k)⁻¹ • (((p : ℚ_[p]) ^ k) • x) := by
        rw [smul_smul, inv_mul_cancel₀ hp0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ h2
  rw [← hS, finrank_span_eq_card hli', Fintype.card_fin]

theorem wt_abs_le {N r : ℕ} (LL : Letters N) (j : ℕ) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) (hm : MultiDeg LL m) :
    |wt LL j c m| ≤ (LL.total : ℤ) := by
  unfold wt Letters.total
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h1 : (m (i, c) : ℤ) ≤ LL.deg i := by
    rw [← hm i]; push_cast
    exact_mod_cast Finset.single_le_sum (f := fun c => m (i, c)) (fun _ _ => Nat.zero_le _) (mem_univ c)
  split_ifs <;> simp <;> omega

theorem mmw_ne_bot_box {K r : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (w : Fin r → ℤ) (h : MMw p LLw J M ρ w ≠ ⊥) :
    w ∈ Fintype.piFinset (fun _ : Fin r => Icc (-(LLw.total : ℤ)) LLw.total) := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨m, hm⟩ : ∃ m, m ∈ x.support := by
    by_contra hc; push Not at hc
    exact hx0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  unfold MMw at hx
  have hY := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).1
  have hW := (Submodule.mem_inf.mp hx).2
  have hP : x ∈ Pol p r LLw := (Submodule.mem_inf.mp hY).1
  rw [Pol, mem_restrictSupport_iff] at hP
  rw [WtSpC, mem_restrictSupport_iff] at hW
  have hmd : MultiDeg LLw m := hP (Finset.mem_coe.mpr hm)
  have hwt : ∀ c ∈ (univ : Finset (Fin r)), wt LLw K c m = w c := hW (Finset.mem_coe.mpr hm)
  rw [Fintype.mem_piFinset]
  intro c
  have := wt_abs_le LLw K c m hmd
  rw [hwt c (mem_univ _)] at this
  rw [mem_Icc]; constructor <;> linarith [abs_le.mp this]
end S1

section S2
open M Finset Matrix

variable {p : ℕ} [Fact p.Prime]

theorem smith_qp (hS : SmithZp) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ_[p]) :
    ∃ (U V : Matrix (Fin n) (Fin n) ℚ_[p]) (dg : Fin n → ℚ_[p]),
      (∀ x y, ‖U x y‖ ≤ 1) ∧ (∀ x y, ‖V x y‖ ≤ 1) ∧ ‖U.det‖ = 1 ∧ ‖V.det‖ = 1 ∧
        A = U * Matrix.diagonal dg * V := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (∑ x, ∑ y, ‖A x y‖) hp
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  have hnorm : ∀ x y, ‖(p : ℚ_[p]) ^ k * A x y‖ ≤ 1 := by
    intro x y
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hpk, mul_one]
    have h1 : ‖A x y‖ ≤ ∑ y, ‖A x y‖ :=
      Finset.single_le_sum (f := fun y => ‖A x y‖) (fun _ _ => norm_nonneg _) (mem_univ y)
    have h2 : ∑ y, ‖A x y‖ ≤ ∑ x, ∑ y, ‖A x y‖ :=
      Finset.single_le_sum (f := fun x => ∑ y, ‖A x y‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (mem_univ x)
    linarith
  let A' : Matrix (Fin n) (Fin n) ℤ_[p] := fun x y => ⟨(p : ℚ_[p]) ^ k * A x y, hnorm x y⟩
  obtain ⟨U, V, d, hU, hV, hA⟩ := hS p n A'
  let φ : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  have hmap : A'.map φ = ((p : ℚ_[p]) ^ k) • A := by
    ext x y; rfl
  have hmap2 : A'.map φ = U.map φ * Matrix.diagonal (fun i => φ (d i)) * V.map φ := by
    rw [hA, Matrix.map_mul, Matrix.map_mul]
    congr 2
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.diagonal_apply_ne _ h]
  have hp0 : ((p : ℚ_[p]) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  refine ⟨U.map φ, V.map φ, fun i => ((p : ℚ_[p]) ^ k)⁻¹ * φ (d i), fun x y => ?_, fun x y => ?_, ?_, ?_, ?_⟩
  · exact PadicInt.norm_le_one (U x y)
  · exact PadicInt.norm_le_one (V x y)
  · rw [show U.map φ = φ.mapMatrix U from rfl, ← RingHom.map_det]
    exact (PadicInt.isUnit_iff.mp hU)
  · rw [show V.map φ = φ.mapMatrix V from rfl, ← RingHom.map_det]
    exact (PadicInt.isUnit_iff.mp hV)
  · have : A = ((p : ℚ_[p]) ^ k)⁻¹ • (A'.map φ) := by
      rw [hmap, smul_smul, inv_mul_cancel₀ hp0, one_smul]
    rw [this, hmap2]
    have hd : Matrix.diagonal (fun i => ((p : ℚ_[p]) ^ k)⁻¹ * φ (d i)) =
        ((p : ℚ_[p]) ^ k)⁻¹ • Matrix.diagonal (fun i => φ (d i)) := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.diagonal_apply_ne _ h]
    rw [hd, Matrix.mul_smul, Matrix.smul_mul]
end S2

section S3
open Finset

theorem sum_fiber {t : ℕ} (s : Fin t → Finset ℕ) (g : (Fin t → ℕ) → ℝ) (i : Fin t) :
    ∑ n ∈ Fintype.piFinset s, ∑ y ∈ s i, g (Function.update n i y) =
      (s i).card * ∑ n ∈ Fintype.piFinset s, g n := by
  classical
  rw [← Finset.sum_product' (f := fun n y => g (Function.update n i y))]
  have : ∑ x ∈ Fintype.piFinset s ×ˢ s i, g (Function.update x.1 i x.2) =
      ∑ x ∈ Fintype.piFinset s ×ˢ s i, g x.1 := by
    apply Finset.sum_nbij' (fun x => (Function.update x.1 i x.2, x.1 i)) (fun x => (Function.update x.1 i x.2, x.1 i))
    · rintro ⟨n, y⟩ h
      rw [Finset.mem_product, Fintype.mem_piFinset] at h ⊢
      dsimp only at h ⊢
      refine ⟨fun j => ?_, h.1 i⟩
      by_cases hj : j = i
      · subst hj; simpa using h.2
      · rw [Function.update_of_ne hj]; exact h.1 j
    · rintro ⟨n, y⟩ h
      rw [Finset.mem_product, Fintype.mem_piFinset] at h ⊢
      dsimp only at h ⊢
      refine ⟨fun j => ?_, h.1 i⟩
      by_cases hj : j = i
      · subst hj; simpa using h.2
      · rw [Function.update_of_ne hj]; exact h.1 j
    · rintro ⟨n, y⟩ _
      simp
    · rintro ⟨n, y⟩ _
      simp
    · rintro ⟨n, y⟩ _
      simp
  rw [this, Finset.sum_product]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Finset.sum_const, nsmul_eq_mul]

theorem grid_average {t : ℕ} (s : Fin t → Finset ℕ) (bad : (Fin t → ℕ) → ℝ) (B Dm : Fin t → (Fin t → ℕ) → ℝ)
    (eps : Fin t → ℝ) (hcard : ∀ i, 0 < (s i).card)
    (h1 : ∀ n ∈ Fintype.piFinset s, bad n ≤ ∑ i, B i n)
    (h2 : ∀ i, ∀ n ∈ Fintype.piFinset s, ∑ y ∈ s i, B i (Function.update n i y) ≤ (s i).card * (eps i * Dm i n)) :
    (∑ n ∈ Fintype.piFinset s, bad n) / (Fintype.piFinset s).card ≤
      ∑ i, eps i * ((∑ n ∈ Fintype.piFinset s, Dm i n) / (Fintype.piFinset s).card) := by
  have hB : ∀ i, ∑ n ∈ Fintype.piFinset s, B i n ≤ eps i * ∑ n ∈ Fintype.piFinset s, Dm i n := by
    intro i
    have hc : (0 : ℝ) < (s i).card := by exact_mod_cast hcard i
    have := sum_fiber s (B i) i
    have h3 : ∑ n ∈ Fintype.piFinset s, ∑ y ∈ s i, B i (Function.update n i y) ≤
        ∑ n ∈ Fintype.piFinset s, (s i).card * (eps i * Dm i n) := Finset.sum_le_sum (h2 i)
    rw [this, ← Finset.mul_sum, ← Finset.mul_sum] at h3
    exact le_of_mul_le_mul_left h3 hc
  have hsum : ∑ n ∈ Fintype.piFinset s, bad n ≤ ∑ i, eps i * ∑ n ∈ Fintype.piFinset s, Dm i n := by
    calc ∑ n ∈ Fintype.piFinset s, bad n ≤ ∑ n ∈ Fintype.piFinset s, ∑ i, B i n := Finset.sum_le_sum h1
      _ = ∑ i, ∑ n ∈ Fintype.piFinset s, B i n := Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun i _ => hB i
  have hG : (0 : ℝ) ≤ (Fintype.piFinset s).card := by positivity
  calc (∑ n ∈ Fintype.piFinset s, bad n) / (Fintype.piFinset s).card
      ≤ (∑ i, eps i * ∑ n ∈ Fintype.piFinset s, Dm i n) / (Fintype.piFinset s).card :=
        div_le_div_of_nonneg_right hsum hG
    _ = _ := by rw [Finset.sum_div]; simp only [mul_div_assoc]
end S3

section S4
open M MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {σ : Type}

def AdaptedBasisExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ),
    ∃ (n₀ : ℕ) (f : Fin n₀ → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (ord : Fin n₀ → ℕ),
      LinearIndependent ℤ_[p] f ∧ Submodule.span ℤ_[p] (Set.range f) = MMwZ p LLw J M ρ w ∧
      (∀ b, HasOrder (Fin.last K, ρ) (ord b) (f b)) ∧
      ∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = FilE p LLw J M ρ w (Fin.last K, ρ) e

noncomputable def filL (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (e : ℕ) :
    Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]) :=
  L ⊓ (MvPolynomial.restrictSupport ℚ_[p] {m | e ≤ m v}).restrictScalars ℤ_[p]

theorem support_zpsmul (a : ℤ_[p]) (ha : a ≠ 0) (x : MvPolynomial σ ℚ_[p]) : (a • x).support = x.support := by
  have hne : (algebraMap ℤ_[p] ℚ_[p]) a ≠ 0 := by
    intro h; apply ha; exact PadicInt.coe_eq_zero.mp h
  ext m
  rw [mem_support_iff, mem_support_iff, MvPolynomial.coeff_smul, Algebra.smul_def]
  constructor
  · intro h h0; apply h; rw [h0, mul_zero]
  · intro h; exact mul_ne_zero hne h

theorem filL_sat (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (e : ℕ) (a : ℤ_[p]) (ha : a ≠ 0)
    (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ L) (h : a • x ∈ filL L v e) : x ∈ filL L v e := by
  refine Submodule.mem_inf.mpr ⟨hx, ?_⟩
  have h2 := (Submodule.mem_inf.mp h).2
  change a • x ∈ MvPolynomial.restrictSupport ℚ_[p] _ at h2
  change x ∈ MvPolynomial.restrictSupport ℚ_[p] _
  rw [mem_restrictSupport_iff] at h2 ⊢
  rwa [support_zpsmul a ha] at h2

theorem filL_anti (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) {e e' : ℕ} (h : e ≤ e') :
    filL L v e' ≤ filL L v e := by
  intro x hx
  refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).1, ?_⟩
  have h2 := (Submodule.mem_inf.mp hx).2
  change x ∈ MvPolynomial.restrictSupport ℚ_[p] _ at h2
  change x ∈ MvPolynomial.restrictSupport ℚ_[p] _
  rw [mem_restrictSupport_iff] at h2 ⊢
  intro m hm
  exact le_trans h (h2 hm)

theorem filL_zero (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) : filL L v 0 = L := by
  apply le_antisymm inf_le_left
  intro x hx
  refine Submodule.mem_inf.mpr ⟨hx, ?_⟩
  change x ∈ MvPolynomial.restrictSupport ℚ_[p] _
  rw [mem_restrictSupport_iff]
  intro m _
  exact Nat.zero_le _

theorem filL_top (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (D : ℕ)
    (hD : ∀ x ∈ L, ∀ m ∈ x.support, m v ≤ D) (e : ℕ) (he : D < e) : filL L v e = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have h1 := (Submodule.mem_inf.mp hx).1
  have h2 := (Submodule.mem_inf.mp hx).2
  change x ∈ MvPolynomial.restrictSupport ℚ_[p] _ at h2
  rw [mem_restrictSupport_iff] at h2
  by_contra hne
  obtain ⟨m, hm⟩ : ∃ m, m ∈ x.support := by
    by_contra hc; push Not at hc
    exact hne (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  have := hD x h1 m hm
  have := h2 (Finset.mem_coe.mpr hm)
  simp only [Set.mem_setOf_eq] at this
  omega

def AdStep (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (e : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f : ι → MvPolynomial σ ℚ_[p]) (ord : ι → ℕ),
    LinearIndependent ℤ_[p] f ∧ Submodule.span ℤ_[p] (Set.range f) = filL L v e ∧
    (∀ b, HasOrder v (ord b) (f b) ∧ e ≤ ord b) ∧
    ∀ e', e ≤ e' → Submodule.span ℤ_[p] (f '' {b | e' ≤ ord b}) = filL L v e'

theorem adStep_top (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (D : ℕ)
    (hD : ∀ x ∈ L, ∀ m ∈ x.support, m v ≤ D) : AdStep L v (D + 1) := by
  refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, linearIndependent_empty_type, ?_, fun b => b.elim, ?_⟩
  · rw [filL_top L v D hD _ (by omega), Set.range_eq_empty, Submodule.span_empty]
  · intro e' he'
    rw [filL_top L v D hD _ (by omega)]
    have : (Empty.elim : Empty → MvPolynomial σ ℚ_[p]) '' {b | e' ≤ (Empty.elim : Empty → ℕ) b} = ∅ := by
      ext x; simp
    rw [this, Submodule.span_empty]

theorem adStep_succ (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (hFG : L.FG) (e : ℕ)
    (h : AdStep L v (e + 1)) : AdStep L v e := by
  obtain ⟨ι, _, f, ord, hli, hsp, hord, hfil⟩ := h
  have hle : filL L v (e + 1) ≤ filL L v e := filL_anti L v (Nat.le_succ e)
  have hfmem : ∀ i, f i ∈ filL L v (e + 1) := fun i => by
    rw [← hsp]; exact Submodule.subset_span ⟨i, rfl⟩
  let Fe := filL L v e
  let Fe1 := filL L v (e + 1)
  let Im : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p] ⧸ Fe1) := Fe.map Fe1.mkQ
  have hFeFG : Fe.FG := Submodule.FG.of_le hFG inf_le_left
  haveI : Module.Finite ℤ_[p] Im := Module.Finite.iff_fg.mpr (hFeFG.map _)
  haveI : Module.IsTorsionFree ℤ_[p] Im := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    rintro a ⟨y, hy⟩ h
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    by_cases ha : a = 0
    · left; exact ha
    · right
      have h' : a • Fe1.mkQ x = 0 := by
        have := congrArg Subtype.val h
        simpa using this
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
      have := filL_sat L v (e+1) a ha x (Submodule.mem_inf.mp hx).1 h'
      apply Subtype.ext
      change Fe1.mkQ x = 0
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr this
  obtain ⟨k, bQ⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ_[p]) (M := Im)
  have hlift : ∀ j, ∃ x, x ∈ Fe ∧ Fe1.mkQ x = (bQ j : MvPolynomial σ ℚ_[p] ⧸ Fe1) := fun j =>
    Submodule.mem_map.mp (bQ j).2
  choose g hgFe hgmk using hlift
  have hgnot : ∀ j, g j ∉ Fe1 := by
    intro j hj
    apply bQ.ne_zero j
    apply Subtype.ext
    rw [← hgmk j, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hj]
    rfl
  have hspanEq : Submodule.span ℤ_[p] (Set.range (Sum.elim f g)) = Fe := by
    rw [Set.Sum.elim_range, Submodule.span_union, hsp]
    apply le_antisymm
    · exact sup_le hle (Submodule.span_le.mpr (Set.range_subset_iff.mpr hgFe))
    · intro x hx
      have hxI : Fe1.mkQ x ∈ Im := Submodule.mem_map_of_mem hx
      have htop : (⟨Fe1.mkQ x, hxI⟩ : Im) ∈ Submodule.span ℤ_[p] (Set.range bQ) := by
        rw [bQ.span_eq]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp htop
      have hc' : ∑ j, c j • Fe1.mkQ (g j) = Fe1.mkQ x := by
        have := congrArg Subtype.val hc
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        rw [← this]
        apply Finset.sum_congr rfl
        intro j _
        rw [hgmk j]
      have hc2 : Fe1.mkQ (∑ j, c j • g j) = Fe1.mkQ x := by
        rw [map_sum]; simp only [map_smul]; exact hc'
      simp only [Submodule.mkQ_apply] at hc2
      have hdiff : x - ∑ j, c j • g j ∈ Fe1 := (Submodule.Quotient.eq Fe1).mp hc2.symm
      have : x = (x - ∑ j, c j • g j) + ∑ j, c j • g j := by abel
      rw [this]
      refine Submodule.add_mem _ (Submodule.mem_sup_left hdiff) (Submodule.mem_sup_right ?_)
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine ⟨ι ⊕ Fin k, inferInstance, Sum.elim f g, Sum.elim ord (fun _ => e), ?_, ?_, ?_, ?_⟩
  ·
    let f' : ι → Fe1 := fun i => ⟨f i, hfmem i⟩
    have hf' : LinearIndependent ℤ_[p] f' := LinearIndependent.of_comp Fe1.subtype hli
    have hg : LinearIndependent ℤ_[p] (Submodule.Quotient.mk (p := Fe1) ∘ g) := by
      have hb := bQ.linearIndependent.map' Im.subtype (Submodule.ker_subtype Im)
      have : Submodule.Quotient.mk (p := Fe1) ∘ g = Im.subtype ∘ bQ := by
        funext j; simp only [Function.comp_apply, Submodule.subtype_apply]; rw [← hgmk j]; rfl
      rw [this]; exact hb
    exact LinearIndependent.sumElim_of_quotient hf' g hg
  · exact hspanEq
  ·
    rintro (i | j)
    · exact ⟨(hord i).1, le_trans (Nat.le_succ e) (hord i).2⟩
    · refine ⟨⟨fun m hm => ?_, ?_⟩, le_rfl⟩
      · have h2 := (Submodule.mem_inf.mp (hgFe j)).2
        change g j ∈ MvPolynomial.restrictSupport ℚ_[p] _ at h2
        rw [mem_restrictSupport_iff] at h2
        exact h2 (Finset.mem_coe.mpr hm)
      · by_contra hc
        push Not at hc
        apply hgnot j
        refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp (hgFe j)).1, ?_⟩
        have h2 := (Submodule.mem_inf.mp (hgFe j)).2
        change g j ∈ MvPolynomial.restrictSupport ℚ_[p] _ at h2
        change g j ∈ MvPolynomial.restrictSupport ℚ_[p] _
        rw [mem_restrictSupport_iff] at h2 ⊢
        intro m hm
        have h3 : e ≤ m v := h2 hm
        have h4 : m v ≠ e := hc m hm
        simp only [Set.mem_setOf_eq]
        omega
  ·
    intro e' he'
    rcases Nat.eq_or_lt_of_le he' with rfl | hlt
    · have : {b : ι ⊕ Fin k | e ≤ Sum.elim ord (fun _ => e) b} = Set.univ := by
        ext b; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rcases b with i | j
        · exact le_trans (Nat.le_succ e) (hord i).2
        · exact le_rfl
      rw [this, Set.image_univ]
      exact hspanEq
    · have : Sum.elim f g '' {b | e' ≤ Sum.elim ord (fun _ => e) b} = f '' {i | e' ≤ ord i} := by
        ext x
        constructor
        · rintro ⟨b, hb, rfl⟩
          rcases b with i | j
          · exact ⟨i, hb, rfl⟩
          · simp only [Set.mem_setOf_eq, Sum.elim_inr] at hb; omega
        · rintro ⟨i, hi, rfl⟩
          exact ⟨Sum.inl i, hi, rfl⟩
      rw [this]
      exact hfil e' hlt

theorem adapted_of_fg (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (hFG : L.FG) (D : ℕ)
    (hD : ∀ x ∈ L, ∀ m ∈ x.support, m v ≤ D) :
    ∃ (n₀ : ℕ) (f : Fin n₀ → MvPolynomial σ ℚ_[p]) (ord : Fin n₀ → ℕ),
      LinearIndependent ℤ_[p] f ∧ Submodule.span ℤ_[p] (Set.range f) = L ∧
      (∀ b, HasOrder v (ord b) (f b)) ∧ ∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = filL L v e := by
  have hind : ∀ k e, e + k = D + 1 → AdStep L v e := by
    intro k
    induction k with
    | zero => intro e he; rw [show e = D + 1 by omega]; exact adStep_top L v D hD
    | succ k ih => intro e he; exact adStep_succ L v hFG e (ih (e + 1) (by omega))
  obtain ⟨ι, _, f, ord, hli, hsp, hord, hfil⟩ := hind (D + 1) 0 (by omega)
  let eq := Fintype.equivFin ι
  refine ⟨Fintype.card ι, f ∘ eq.symm, ord ∘ eq.symm, hli.comp _ eq.symm.injective, ?_, fun b => (hord _).1, ?_⟩
  · rw [eq.symm.surjective.range_comp, hsp, filL_zero]
  · intro e
    have : (f ∘ eq.symm) '' {b | e ≤ (ord ∘ eq.symm) b} = f '' {i | e ≤ ord i} := by
      ext x
      constructor
      · rintro ⟨b, hb, rfl⟩; exact ⟨eq.symm b, hb, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        refine ⟨eq i, ?_, ?_⟩
        · simp only [Set.mem_setOf_eq, Function.comp_apply, Equiv.symm_apply_apply]; exact hi
        · simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [this]
    exact hfil e (Nat.zero_le e)

theorem polZ_fg {K r : ℕ} (LLw : Letters K) : (PolZ p r LLw).FG := by
  classical
  let bnd : Fin K × Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => LLw.total)
  let T : Finset (Fin K × Fin r →₀ ℕ) := Finset.Iic bnd
  have hfg : (Submodule.span ℤ_[p] ((fun m => (monomial m (1 : ℚ_[p]) : MvPolynomial (Fin K × Fin r) ℚ_[p])) ''
      (T : Set (Fin K × Fin r →₀ ℕ)))).FG := Submodule.fg_span ((T.finite_toSet).image _)
  refine Submodule.FG.of_le hfg ?_
  intro x hx
  have hxP : x ∈ Pol p r LLw := (Submodule.mem_inf.mp hx).1
  have hxI := (Submodule.mem_inf.mp hx).2
  rw [Pol, mem_restrictSupport_iff] at hxP
  obtain ⟨y, hy⟩ := hxI
  rw [x.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmT : m ∈ T := by
    rw [Finset.mem_Iic, Finsupp.le_def]
    intro a
    have hmd : MultiDeg LLw m := hxP (Finset.mem_coe.mpr hm)
    have h1 : m a ≤ ∑ c, m (a.1, c) :=
      Finset.single_le_sum (f := fun c => m (a.1, c)) (fun _ _ => Nat.zero_le _) (mem_univ a.2)
    have h2 : LLw.deg a.1 ≤ LLw.total :=
      Finset.single_le_sum (f := fun i => LLw.deg i) (fun _ _ => Nat.zero_le _) (mem_univ a.1)
    have h3 : bnd a = LLw.total := by simp [bnd]
    rw [h3]
    rw [hmd a.1] at h1
    omega
  have hco : x.coeff m = algebraMap ℤ_[p] ℚ_[p] (y.coeff m) := by
    rw [← hy]
    simp [MvPolynomial.coeff_map]
  have : monomial m (x.coeff m) = y.coeff m • (monomial m (1 : ℚ_[p])) := by
    rw [hco, MvPolynomial.smul_monomial, Algebra.smul_def, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, Finset.mem_coe.mpr hmT, rfl⟩)

theorem mmwZ_fg {K r : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (w : Fin r → ℤ) : (MMwZ p LLw J M ρ w).FG := by
  refine Submodule.FG.of_le (polZ_fg LLw) ?_
  intro x hx
  have hxY := (Submodule.mem_inf.mp hx).1
  exact Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hxY).1).1).1,
    (Submodule.mem_inf.mp hx).2⟩

theorem yZ_fg {K r : ℕ} [NeZero r] (LL : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    (YZ p (r := r) LL J M).FG :=
  Submodule.FG.of_le (polZ_fg LL) inf_le_right

theorem existsAdaptedBasis : AdaptedBasisExists := by
  intro p _ K r _ LLw q J M ρ w
  refine adapted_of_fg (MMwZ p LLw J M ρ w) (Fin.last K, ρ) (mmwZ_fg LLw J M ρ w) (LLw.deg (Fin.last K)) ?_
  intro x hx m hm
  have hxY := (Submodule.mem_inf.mp hx).1
  have hxP : x ∈ Pol p r LLw := (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hxY).1).1).1
  rw [Pol, mem_restrictSupport_iff] at hxP
  have hmd : MultiDeg LLw m := hxP (Finset.mem_coe.mpr hm)
  rw [← hmd (Fin.last K)]
  exact Finset.single_le_sum (f := fun c => m (Fin.last K, c)) (fun _ _ => Nat.zero_le _) (mem_univ ρ)
end S4

section S5
open M MvPolynomial Finset

def PointM : Prop :=
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r]
    (LL : Letters N) (T : TieData) (a : ℕ) (E κ : ℝ) (n : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → 1 ≤ E →
    (∀ i, T.S (LL.setTies T n) i ≤ n i) → (∀ x, (LL.setTies T n).deg x ≤ 2 * a) → (∀ i, T.z i ≤ 2 * a) →
    ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ →
    HypP p (LL.setTies T n) ρ ⌈κ / (N + 2)⌉₊ → HypW p (r := r) (LL.setTies T n) ⌈κ / (N + 2)⌉₊ →
    (∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ κ) →
    ∀ (nb : Fin T.t → (Fin r → ℤ) → ℕ)
      (f : ∀ i w, Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
      (U V : ∀ i w, Matrix (Fin (nb i w)) (Fin (nb i w)) ℚ_[p]) (dg : ∀ i w, Fin (nb i w) → ℚ_[p])
      (fw : ∀ i : Fin T.t, (Fin r → ℤ) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]),
      (∀ i w, LinearIndependent ℤ_[p] (f i w) ∧
        Submodule.span ℤ_[p] (Set.range (f i w)) =
          MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) →
      (∀ i w, (∀ x y, ‖U i w x y‖ ≤ 1) ∧ (∀ x y, ‖V i w x y‖ ≤ 1) ∧ ‖(U i w).det‖ = 1 ∧ ‖(V i w).det‖ = 1 ∧
        (Matrix.of fun x y => (p : ℚ_[p]) ^ (⌈κ⌉₊) *
          tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) (f i w x) (f i w y)) =
          U i w * Matrix.diagonal (dg i w) * V i w) →
      (∀ i w, fw i w ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ∧
        (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ → fw i w ≠ 0)) →
      (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + C * κ) + C * κ⌋ : ℝ) ≤
        ∑ i, ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
          (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ)

theorem lg_nonneg (p a r : ℕ) [Fact p.Prime] (hr : 2 ≤ r) : 0 ≤ lgV2 p a r := by
  unfold lgV2
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have : (1 : ℝ) ≤ 8 * a + r := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  have := Real.logb_nonneg hp this
  linarith

theorem theoremM_of_point (hMean : MeanGam) (hMono : WeightSpaceDimMonotone) (hCount : MonoCount) (hSmith : SmithZp)
    (hAd : AdaptedBasisExists) (hPt : PointM) : TheoremM := by
  obtain ⟨C₀', hC₀', hMG⟩ := hMean
  obtain ⟨C₁, hC₁, hPW⟩ := hPt
  refine ⟨max C₀' C₁, le_trans hC₁ (le_max_right _ _), ?_⟩
  intro p _ N r _ _ LL T a E κ Yl n₀ dd ρ hp2 hr hρ hadm hE hYd hS hdeg hz hκ hHyp
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlg : 0 ≤ lgV2 p a r := lg_nonneg p a r hr
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ

  choose nb fb ord hli hsp hord hfil using fun (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) =>
    hAd p (T.pos i) r L0 T.J (T.thrUpTo i) ρ w
  choose Uc Vc dgc hUc using fun (k : ℕ) (A : Matrix (Fin k) (Fin k) ℚ_[p]) => smith_qp hSmith A
  have hfwex : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ), ∃ g,
      g ∈ MMw p L0 T.J (T.thrUpTo i) ρ w ∧ (MMw p L0 T.J (T.thrUpTo i) ρ w ≠ ⊥ → g ≠ 0) := by
    intro i L0 w
    by_cases h : MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥
    · exact ⟨0, Submodule.zero_mem _, fun h' => absurd h h'⟩
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      exact ⟨g, hg, fun _ => hg0⟩
  choose fw hfw using hfwex
  have hnb : ∀ i L0 w, nb i L0 w = Module.finrank ℚ_[p] (MMw p L0 T.J (T.thrUpTo i) ρ w) := fun i L0 w =>
    (finrank_of_lattice_basis _ (fb i L0 w) (hli i L0 w) (hsp i L0 w)).symm
  let MatF : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) (y : ℕ),
      Matrix (Fin (nb i L0 w)) (Fin (nb i L0 w)) ℚ_[p] := fun i L0 w y =>
    Matrix.of fun x x' => (p : ℚ_[p]) ^ (⌈κ⌉₊) * tieGam p L0 ρ (T.z i) y (fb i L0 w x) (fb i L0 w x')
  let cntF : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) (y : ℕ), ℕ := fun i L0 w y =>
    (univ.filter (fun b => ‖dgc _ (MatF i L0 w y) b‖ < (p : ℝ) ^ (-E))).card
  let Bx : ∀ i : Fin T.t, Letters (T.pos i + 1) → Finset (Fin r → ℤ) := fun i L0 =>
    Fintype.piFinset fun _ => Icc (-(L0.total : ℤ)) L0.total
  have hcntle : ∀ i L0 w y, cntF i L0 w y ≤ nb i L0 w := fun i L0 w y =>
    (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  have hbot : ∀ i L0 w, w ∉ Bx i L0 → MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥ := fun i L0 w hw => by
    by_contra h; exact hw (mmw_ne_bot_box L0 T.J (T.thrUpTo i) ρ w h)
  have hnb0 : ∀ i L0 w, w ∉ Bx i L0 → nb i L0 w = 0 := fun i L0 w hw => by
    rw [hnb, hbot i L0 w hw, finrank_bot]
  have hcnt0 : ∀ i L0 w y, w ∉ Bx i L0 → cntF i L0 w y = 0 := fun i L0 w y hw =>
    Nat.eq_zero_of_le_zero ((hcntle i L0 w y).trans (hnb0 i L0 w hw).le)
  let sI : Fin T.t → Finset ℕ := fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)
  let top : Fin T.t → ℕ := fun i => n₀ i + dd i * (Yl i - 1)
  have hsI : ∀ i y, y ∈ sI i → n₀ i ≤ y ∧ y ≤ top i := by
    intro i y hy
    simp only [sI, mem_image, mem_range] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    refine ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _⟩
  have hgrid : ∀ n ∈ Fintype.piFinset sI, ∀ i, n₀ i ≤ n i ∧ n i ≤ top i := fun n hn i =>
    hsI i (n i) (Fintype.mem_piFinset.mp hn i)
  have hinj : ∀ i, Set.InjOn (fun j => n₀ i + dd i * j) (range (Yl i) : Set ℕ) := by
    intro i x _ y _ hxy
    have := (hYd i).2.1
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_left this (by omega)
  have hcard : ∀ i, (sI i).card = Yl i := fun i => by
    simp only [sI]; rw [Finset.card_image_of_injOn (hinj i), Finset.card_range]
  let BB : Fin T.t → (Fin T.t → ℕ) → ℝ := fun i n =>
    ∑ w ∈ Bx i ((LL.setTies T n).takeD (T.pos i + 1)),
      (cntF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i) : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i ((LL.setTies T n).takeD (T.pos i + 1)) w)) : ℝ)
  refine grid_average sI (fun n => (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
      (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + max C₀' C₁ * κ) + max C₀' C₁ * κ⌋ : ℝ)) BB
    (fun i n => (Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T (Function.update n i (top i))) T.J T.thr) : ℝ))
    (fun i => 2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
      (max C₀' C₁ * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgV2 p a r / Yl i) / E)
    (fun i => by rw [hcard]; exact (hYd i).1) ?_ ?_
  · intro n hn
    have hnt : ∀ i, n i ≤ top i := fun i => (hgrid n hn i).2
    have hSn : ∀ i, T.S (LL.setTies T n) i ≤ n i := fun i =>
      (S_mono LL T n top hnt i).trans ((hS i).trans (hgrid n hn i).1)
    have hdegn : ∀ x, (LL.setTies T n).deg x ≤ 2 * a := fun x =>
      (setTies_deg_mono LL T n top hnt x).trans (hdeg x)
    obtain ⟨hP, hW, hL4⟩ := hHyp n hn
    have key := hPW (max C₀' C₁) (le_max_right _ _) p N r LL T a E κ n ρ hp2 hr hρ hadm hE hSn hdegn hz hκ hP hW hL4
      (fun i w => nb i ((LL.setTies T n).takeD (T.pos i + 1)) w)
      (fun i w => fb i ((LL.setTies T n).takeD (T.pos i + 1)) w)
      (fun i w => Uc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i)))
      (fun i w => Vc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i)))
      (fun i w => dgc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i)))
      (fun i w => fw i ((LL.setTies T n).takeD (T.pos i + 1)) w)
      (fun i w => ⟨hli _ _ _, hsp _ _ _⟩) (fun i w => hUc _ _) (fun i w => hfw _ _ _)
    refine key.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    apply finsum_eq_sum_of_support_subset
    intro w hw
    by_contra hwn
    apply hw
    have h0 := hcnt0 i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i) hwn
    simp only [cntF] at h0
    simp only [h0, Nat.cast_zero, zero_mul]
  · intro i n hn
    have hnt : ∀ i, n i ≤ top i := fun i => (hgrid n hn i).2
    obtain ⟨hlt, hvW, _⟩ := hadm.2.1 i
    obtain ⟨_, _, hL4⟩ := hHyp n hn
    have hLW : ∀ y, (LL.setTies T (Function.update n i y)).takeD (T.pos i + 1) =
        (LL.setTies T n).takeD (T.pos i + 1) := fun y => takeD_setTies_update LL T n i y
    have hL0S : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ T.S (LL.setTies T top) i := by
      rw [takeD_total_eq (LL.setTies T n) T i hlt]; exact S_mono LL T n top hnt i
    have hL0tot : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n₀ i := hL0S.trans (hS i)
    have hvec : ((LL.setTies T n).takeD (T.pos i + 1)).vec (Fin.last (T.pos i)) = true := by
      simp only [Letters.takeD, Fin.val_last]
      rw [dif_pos (by omega)]
      exact hvW
    have hL0deg : ∀ x, ((LL.setTies T n).takeD (T.pos i + 1)).deg x ≤ 2 * a := by
      intro x
      simp only [Letters.takeD]
      split_ifs
      · exact (setTies_deg_mono LL T n top hnt _).trans (hdeg _)
      · exact Nat.zero_le _
    have hsd : n₀ i + dd i * (Yl i - 1) ≤ 2 * a := by
      have := hdeg ⟨T.pos i + 1, hlt⟩
      rwa [setTies_deg_eta LL T hadm.1 top i hlt] at this
    have hκi : (((T.pos i : ℕ) + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ := by
      refine le_trans ?_ hκ
      have : ((T.pos i : ℕ) + 3 : ℝ) ≤ (N : ℝ) + 2 := by
        have : T.pos i + 3 ≤ N + 2 := by omega
        exact_mod_cast this
      gcongr
    set L0 := (LL.setTies T n).takeD (T.pos i + 1) with hL0
    have e1 : ∀ y, BB i (Function.update n i y) = ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ) := by
      intro y
      simp only [BB]
      rw [hLW y, Function.update_self]
    simp only [e1]

    have hmono : ∀ y ∈ sI i, ∀ w, (cntF i L0 w y : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ) ≤
        (cntF i L0 w y : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) := by
      intro y hy w
      by_cases hM : MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥
      · have : cntF i L0 w y = 0 := Nat.eq_zero_of_le_zero
          ((hcntle i L0 w y).trans (by rw [hnb, hM, finrank_bot]))
        simp [this]
      · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have hm := hMono p N r LL T hadm ρ hρ hr i (Function.update n i y) w (fw i L0 w)
          (by rw [hLW y]; exact (hfw i L0 w).1) ((hfw i L0 w).2 hM)
          (by rw [hLW y, Function.update_self]; exact hL0tot.trans (hsI i y hy).1) (top i)
          (by rw [Function.update_self]; exact (hsI i y hy).2)
        rw [Function.update_idem] at hm
        exact_mod_cast hm

    have hmean : ∀ w ∈ Bx i L0, (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) ≤
        (Yl i : ℝ) * ((nb i L0 w : ℝ) * (2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
          (max C₀' C₁ * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgV2 p a r / Yl i) / E)) := by
      intro w _
      have hm := hMG p (T.pos i) r L0 T.J (T.thrUpTo i) ρ (T.z i) w (nb i L0 w) (fb i L0 w) (ord i L0 w)
        (n₀ i) (dd i) (Yl i) a E κ (fun j => Uc _ (MatF i L0 w (n₀ i + dd i * j)))
        (fun j => Vc _ (MatF i L0 w (n₀ i + dd i * j))) (fun j => dgc _ (MatF i L0 w (n₀ i + dd i * j)))
        hρ hr hvec (hli _ _ _) (hsp _ _ _) (hord _ _ _) (hfil _ _ _) hE (hYd i).1 (hYd i).2.1 (hYd i).2.2
        hL0tot hL0deg hsd (hz i) hκi (hL4 i) (fun j _ => hUc _ _)
      have hY0 : (0 : ℝ) < Yl i := by exact_mod_cast (hYd i).1
      rw [div_le_iff₀ hY0] at hm
      have hsum : (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) =
          ∑ j ∈ range (Yl i), ((univ.filter (fun b =>
            ‖dgc _ (MatF i L0 w (n₀ i + dd i * j)) b‖ < (p : ℝ) ^ (-E))).card : ℝ) := by
        simp only [sI]
        rw [Finset.sum_image (hinj i)]
      rw [hsum]
      refine hm.trans ?_
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ hY0.le
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hE0 : (0 : ℝ) < E := by linarith
      have hL : ((L0.total : ℕ) : ℝ) ≤ (T.S (LL.setTies T top) i : ℝ) := by exact_mod_cast hL0S
      have hC : C₀' * κ ≤ max C₀' C₁ * κ := mul_le_mul_of_nonneg_right (le_max_left _ _) hκ0
      gcongr

    have hcount : (∑ w ∈ Bx i L0, (nb i L0 w : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ)) =
        (Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T (Function.update n i (top i))) T.J T.thr) : ℝ) := by
      have hc := hCount p N r LL T hadm ρ hρ hr i (Function.update n i (top i))
        (by rw [hLW, Function.update_self]; exact hL0tot.trans (Nat.le_add_right _ _)) (fun w => fw i L0 w)
        (fun w => by rw [hLW]; exact hfw i L0 w)
      rw [hLW] at hc
      rw [finsum_eq_sum_of_support_subset _ (s := Bx i L0) (fun w hw => by
        by_contra hwn
        apply hw
        beta_reduce
        rw [← hnb, hnb0 i L0 w hwn, zero_mul])] at hc
      rw [← hc]
      push_cast
      apply Finset.sum_congr rfl
      intro w _
      rw [hnb]
    calc ∑ y ∈ sI i, ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ)
        ≤ ∑ y ∈ sI i, ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) :=
          Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun w _ => hmono y hy w
      _ = ∑ w ∈ Bx i L0, (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ ≤ ∑ w ∈ Bx i L0, ((Yl i : ℝ) * ((nb i L0 w : ℝ) * (2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
          (max C₀' C₁ * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgV2 p a r / Yl i) / E))) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) :=
          Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_right (hmean w hw) (Nat.cast_nonneg _)
      _ = (sI i).card * ((2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
          (max C₀' C₁ * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgV2 p a r / Yl i) / E) *
            ∑ w ∈ Bx i L0, (nb i L0 w : ℝ) *
              (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ)) := by
          rw [hcard, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          ring
      _ = _ := by rw [hcount]
end S5

section S6
open M MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem fock_eq_sum (F G : MvPolynomial σ ℚ_[p]) (s : Finset (σ →₀ ℕ)) (hs : F.support ⊆ s) :
    fock p F G = ∑ m ∈ s, F.coeff m * G.coeff m * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by
  classical
  unfold fock
  apply Finset.sum_subset hs
  intro m _ hm
  rw [notMem_support_iff.mp hm, zero_mul, zero_mul]

theorem fock_add_left (F F' G : MvPolynomial σ ℚ_[p]) : fock p (F + F') G = fock p F G + fock p F' G := by
  classical
  rw [fock_eq_sum (F + F') G (F.support ∪ F'.support) support_add,
    fock_eq_sum F G (F.support ∪ F'.support) subset_union_left,
    fock_eq_sum F' G (F.support ∪ F'.support) subset_union_right, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [coeff_add]; ring

theorem fock_smul_left (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) : fock p (c • F) G = c * fock p F G := by
  classical
  rw [fock_eq_sum (c • F) G F.support (support_smul), fock_eq_sum F G F.support subset_rfl, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [coeff_smul, smul_eq_mul]; ring

theorem fock_add_right (F G G' : MvPolynomial σ ℚ_[p]) : fock p F (G + G') = fock p F G + fock p F G' := by
  unfold fock
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [coeff_add]; ring

theorem fock_smul_right (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) : fock p F (c • G) = c * fock p F G := by
  unfold fock
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [coeff_smul, smul_eq_mul]; ring

noncomputable def fockBil {N r : ℕ} (LL : Letters N)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
  LinearMap.mk₂ ℚ_[p] (fun x y => fockN p LL (φ x) y)
    (fun x x' y => by simp only [fockN, map_add, fock_add_left, add_div])
    (fun c x y => by simp only [fockN, map_smul, fock_smul_left, smul_eq_mul, mul_div_assoc])
    (fun x y y' => by simp only [fockN, fock_add_right, add_div])
    (fun c x y => by simp only [fockN, fock_smul_right, smul_eq_mul, mul_div_assoc])

theorem fockBil_apply {N r : ℕ} (LL : Letters N)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (x y) :
    fockBil LL φ x y = fockN p LL (φ x) y := rfl

def PartnerM : Prop :=
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r]
    (LL : Letters N) (T : TieData) (a : ℕ) (E κ : ℝ) (n : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → 1 ≤ E →
    (∀ i, T.S (LL.setTies T n) i ≤ n i) → (∀ x, (LL.setTies T n).deg x ≤ 2 * a) → (∀ i, T.z i ≤ 2 * a) →
    ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ →
    HypP p (LL.setTies T n) ρ ⌈κ / (N + 2)⌉₊ → HypW p (r := r) (LL.setTies T n) ⌈κ / (N + 2)⌉₊ →
    (∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ κ) →
    ∀ (nb : Fin T.t → (Fin r → ℤ) → ℕ)
      (f : ∀ i w, Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
      (U V : ∀ i w, Matrix (Fin (nb i w)) (Fin (nb i w)) ℚ_[p]) (dg : ∀ i w, Fin (nb i w) → ℚ_[p])
      (fw : ∀ i : Fin T.t, (Fin r → ℤ) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]),
      (∀ i w, LinearIndependent ℤ_[p] (f i w) ∧
        Submodule.span ℤ_[p] (Set.range (f i w)) =
          MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) →
      (∀ i w, (∀ x y, ‖U i w x y‖ ≤ 1) ∧ (∀ x y, ‖V i w x y‖ ≤ 1) ∧ ‖(U i w).det‖ = 1 ∧ ‖(V i w).det‖ = 1 ∧
        (Matrix.of fun x y => (p : ℚ_[p]) ^ (⌈κ⌉₊) *
          tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) (f i w x) (f i w y)) =
          U i w * Matrix.diagonal (dg i w) * V i w) →
      (∀ i w, fw i w ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ∧
        (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ → fw i w ≠ 0)) →
      ∃ L₁ : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]),
        L₁ ≤ YZ p (r := r) (LL.setTies T n) T.J T.thr ∧
        (∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), c ≠ 0 → x ∈ YZ p (r := r) (LL.setTies T n) T.J T.thr →
          c • x ∈ L₁ → x ∈ L₁) ∧
        (∀ u ∈ L₁, (∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ L₁ → u = c • x → IsUnit c) →
          ∃ u' ∈ YZ p (r := r) (LL.setTies T n) T.J T.thr,
            (p : ℝ) ^ (-⌊(T.t : ℝ) * (E + C * κ) + C * κ⌋) ≤
              ‖fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) u) u'‖) ∧
        ((Module.finrank ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) - Module.finrank ℤ_[p] L₁ : ℕ) : ℝ) ≤
          ∑ i, ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ)

theorem pointM_of_partner (hBad : BadCrit) (hPart : PartnerM) : PointM := by
  obtain ⟨C₁, hC₁, hP⟩ := hPart
  refine ⟨C₁, hC₁, ?_⟩
  intro C hC p _ N r _ _ LL T a E κ n ρ h2p hr hρ hadm hE hS hdeg hz hκ hHP hHW hL4 nb f U V dg fw h1 h2 h3
  obtain ⟨L₁, hle, hsat, hpart, hrank⟩ :=
    hP C hC p N r LL T a E κ n ρ h2p hr hρ hadm hE hS hdeg hz hκ hHP hHW hL4 nb f U V dg fw h1 h2 h3
  haveI hfin : Module.Finite ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) :=
    Module.Finite.iff_fg.mpr (yZ_fg _ _ _)
  have hb := hBad p (MvPolynomial (Fin N × Fin r) ℚ_[p]) (fockBil (LL.setTies T n) (T.phis p (LL.setTies T n)))
    (YZ p (r := r) (LL.setTies T n) T.J T.thr) L₁ ⌊(T.t : ℝ) * (E + C * κ) + C * κ⌋ hfin hle hsat
    (fun u hu hprim => by
      obtain ⟨u', hu', h⟩ := hpart u hu hprim
      exact ⟨u', hu', by rw [fockBil_apply]; exact h⟩)
  exact (Nat.cast_le.mpr hb).trans hrank
end S6

end Formalism.GM.TM

namespace Formalism.GM

theorem theoremM_of_point (hMean : M.MeanGam) (hMono : M.WeightSpaceDimMonotone) (hCount : M.MonoCount) (hSmith : SmithZp)
    (hPt : TM.PointM) : M.TheoremM :=
  TM.theoremM_of_point hMean hMono hCount hSmith TM.existsAdaptedBasis hPt

theorem theoremM_of_partner (hMean : M.MeanGam) (hMono : M.WeightSpaceDimMonotone) (hCount : M.MonoCount) (hBad : M.BadCrit)
    (hSmith : SmithZp) (hPart : TM.PartnerM) : M.TheoremM :=
  theoremM_of_point hMean hMono hCount hSmith (TM.pointM_of_partner hBad hPart)

theorem adaptedBasis : TM.AdaptedBasisExists := TM.existsAdaptedBasis

end Formalism.GM
