import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.L0ConstantPartCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2RmatrixTranspose

namespace Formalism.FourierDecayAlt.P.TLA.L1

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.TL

section

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem kMat_mul {st : Start A} {M N : SlopeTestRemainingChoices S A} (hM : kMat st M) (hN : kMat st N) : kMat st (M * N) := fun i j => by
  rw [Matrix.mul_apply]; exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hM i k) (hN k j)

theorem kMat_sub {st : Start A} {M N : SlopeTestRemainingChoices S A} (hM : kMat st M) (hN : kMat st N) : kMat st (M - N) := fun i j => by
  rw [Matrix.sub_apply]; exact Subalgebra.sub_mem _ (hM i j) (hN i j)

theorem kMat_neg {st : Start A} {M : SlopeTestRemainingChoices S A} (hM : kMat st M) : kMat st (-M) := fun i j => by
  rw [Matrix.neg_apply]; exact Subalgebra.neg_mem _ (hM i j)

theorem kMat_smul {st : Start A} (c : ℂ) {M : SlopeTestRemainingChoices S A} (hM : kMat st M) : kMat st (c • M) := fun i j => by
  rw [Matrix.smul_apply]; exact Subalgebra.smul_mem _ (hM i j) c

theorem kMat_one {st : Start A} : kMat st (1 : SlopeTestRemainingChoices S A) := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

theorem kMat_zero {st : Start A} : kMat st (0 : SlopeTestRemainingChoices S A) := fun _ _ => Subalgebra.zero_mem _

theorem kMat_io {st : Start A} {a : A} (ha : a ∈ kAlg st) : kMat st (io a : SlopeTestRemainingChoices S A) := fun i j => by
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact ha
  · exact Subalgebra.zero_mem _

theorem kMat_eU {st : Start A} (a : S) (i j : Fin 2) : kMat st (eU a i j : SlopeTestRemainingChoices S A) := fun x y => by
  simp only [eU, Matrix.of_apply]
  split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

theorem kMat_ins {st : Start A} (a : S) {M : M2 (SlopeTestRemainingChoices S A)} (hM : ∀ i j, kMat st (M i j)) : kMat st (ins a M) := by
  intro x y
  unfold ins
  rw [Matrix.sum_apply]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [Matrix.sum_apply]
  exact Subalgebra.sum_mem _ fun j _ => kMat_mul (kMat_eU a i j) (hM i j) x y

theorem kMat_of {st : Start A} {a b c d : SlopeTestRemainingChoices S A} (ha : kMat st a) (hb : kMat st b) (hc : kMat st c)
    (hd : kMat st d) : ∀ i j, kMat st ((!![a, b; c, d] : M2 (SlopeTestRemainingChoices S A)) i j) := by
  intro i j; fin_cases i <;> fin_cases j <;> simpa

theorem x_mem (st : Start A) {Y : ℂ} (hY : star Y = Y) : st.x Y ∈ kAlg st :=
  Algebra.subset_adjoin (Or.inl ⟨Y, hY, rfl⟩)

theorem xi_mem (st : Start A) {Y : ℂ} (hY : Y ∈ st.inv) (hr : star Y = Y) : st.xi Y ∈ kAlg st :=
  Algebra.subset_adjoin (Or.inr ⟨Y, hY, hr, rfl⟩)

theorem xi_comm {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) {Y : ℂ} (hY : Y ∈ st.inv) {g : A}
    (hg : Commute (st.x Y) g) : Commute (st.xi Y) g := by
  obtain ⟨u, v⟩ := h.x_xi Y hY
  calc st.xi Y * g = st.xi Y * g * (st.x Y * st.xi Y) := by rw [u, mul_one]
    _ = st.xi Y * (st.x Y * g) * st.xi Y := by rw [hg.eq]; simp only [mul_assoc]
    _ = g * st.xi Y := by rw [← mul_assoc, v, one_mul]

theorem kAlg_comm {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) {g : A}
    (hg : ∀ Y, Commute (st.x Y) g) {a : A} (ha : a ∈ kAlg st) : Commute a g := by
  have hle : kAlg st ≤ Subalgebra.centralizer ℂ {g} := by
    unfold kAlg
    rw [Algebra.adjoin_le_iff]
    rintro b (⟨Y, -, rfl⟩ | ⟨Y, hY, -, rfl⟩) <;> rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff] <;>
      intro m hm <;> rw [Set.mem_singleton_iff.mp hm]
    · exact (hg Y).eq.symm
    · exact (xi_comm h hY (hg Y)).eq.symm
  have := hle ha
  rw [Subalgebra.mem_centralizer_iff] at this
  exact (this g rfl).symm

theorem io_comm {s : A} {M : SlopeTestRemainingChoices S A} (h : ∀ i j, Commute s (M i j)) : Commute (io s : SlopeTestRemainingChoices S A) M := by
  show Matrix.scalar (Ix S) s * M = M * Matrix.scalar (Ix S) s
  ext i j
  simp only [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact (h i j).eq

theorem kMat_comm_io {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) {s : A}
    (hs : ∀ Y, Commute (st.x Y) s) {M : SlopeTestRemainingChoices S A} (hM : kMat st M) : Commute M (io s) :=
  (io_comm fun i j => (kAlg_comm h hs (hM i j)).symm).symm

theorem eU_comm_io (a : S) (i j : Fin 2) (s : A) : Commute (io s : SlopeTestRemainingChoices S A) (eU a i j) :=
  io_comm fun x y => by
    simp only [eU, Matrix.of_apply]
    split_ifs
    · exact Commute.one_right s
    · exact Commute.zero_right s

theorem comm_kap {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) {M : SlopeTestRemainingChoices S A} (hM : kMat st M) :
    Commute M (kapL L) :=
  kMat_comm_io h (fun Y => ((h.x_fn Y _ (by simp [zfns])).mul_right (h.x_fn Y _ (by simp [zfns]))).mul_right
    (h.x_fn Y _ (by simp [zfns]))) hM

theorem comm_tz {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) {M : SlopeTestRemainingChoices S A} (hM : kMat st M) :
    Commute M (tz L) :=
  kMat_comm_io h (fun Y => (h.x_fn Y _ (by simp [zfns])).smul_right L.TT) hM

theorem commute_level_zero_element {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) (Y : ℂ) {M : SlopeTestRemainingChoices S A} (hM : kMat st M) :
    Commute M (io (L.l0 Y)) :=
  kMat_comm_io h (fun Y' => by
    unfold LevelData.l0
    exact ((h.x_nab Y').neg_right).sub_right ((show Commute (st.x Y') (algebraMap ℂ A (Y + 1 / 2)) from
      (Algebra.commutes _ _).symm).mul_right
      ((h.x_fn Y' _ (by simp [zfns])).mul_right (h.x_fn Y' _ (by simp [zfns]))))) hM

theorem dSpan_gen {st : Start A} {X φ τ α β γ : SlopeTestRemainingChoices S A} (h1 : kMat st α) (h2 : kMat st β) (h3 : kMat st γ) :
    α * (X * β - β * X) * γ ∈ dSpan st X φ τ :=
  Submodule.subset_span (Or.inl ⟨α, β, γ, h1, h2, h3, rfl⟩)

theorem dSpan_phi {st : Start A} {X φ τ γ : SlopeTestRemainingChoices S A} (h : kMat st γ) : φ * γ ∈ dSpan st X φ τ :=
  Submodule.subset_span (Or.inr ⟨γ, h, Or.inl rfl⟩)

theorem dSpan_phitau {st : Start A} {X φ τ γ : SlopeTestRemainingChoices S A} (h : kMat st γ) : φ * τ * γ ∈ dSpan st X φ τ :=
  Submodule.subset_span (Or.inr ⟨γ, h, Or.inr rfl⟩)

theorem dSpan_mul_right {st : Start A} {X φ τ M γ' : SlopeTestRemainingChoices S A} (hM : M ∈ dSpan st X φ τ) (hγ : kMat st γ') :
    M * γ' ∈ dSpan st X φ τ := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨α, β, γ, h1, h2, h3, rfl⟩ | ⟨γ, h, rfl | rfl⟩
    · rw [mul_assoc]; exact dSpan_gen h1 h2 (kMat_mul h3 hγ)
    · rw [mul_assoc]; exact dSpan_phi (kMat_mul h hγ)
    · rw [mul_assoc]; exact dSpan_phitau (kMat_mul h hγ)
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem dSpan_mul_left {st : Start A} {X φ τ M α' : SlopeTestRemainingChoices S A} (hM : M ∈ dSpan st X φ τ) (hα : kMat st α')
    (hφ : Commute α' φ) (hτ : Commute α' τ) : α' * M ∈ dSpan st X φ τ := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨α, β, γ, h1, h2, h3, rfl⟩ | ⟨γ, h, rfl | rfl⟩
    · rw [← mul_assoc, ← mul_assoc]
      exact dSpan_gen (kMat_mul hα h1) h2 h3
    · rw [hφ.left_comm γ]; exact dSpan_phi (kMat_mul hα h)
    · rw [(hφ.mul_right hτ).left_comm γ]; exact dSpan_phitau (kMat_mul hα h)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem ins_up (a : S) (m00 m01 m11 : SlopeTestRemainingChoices S A) :
    ins a (!![m00, m01; 0, m11] : M2 (SlopeTestRemainingChoices S A)) = eU a 0 0 * m00 + eU a 0 1 * m01 + eU a 1 1 * m11 := by
  simp [ins, Fin.sum_univ_two, add_assoc]

theorem ins_low (a : S) (m00 m10 m11 : SlopeTestRemainingChoices S A) :
    ins a (!![m00, 0; m10, m11] : M2 (SlopeTestRemainingChoices S A)) = eU a 0 0 * m00 + eU a 1 0 * m10 + eU a 1 1 * m11 := by
  simp [ins, Fin.sum_univ_two, add_assoc]

theorem eU_sum (a : S) : (eU a 0 0 : SlopeTestRemainingChoices S A) + eU a 1 1 = 1 := by
  have := (Formalism.FourierDecayAlt.P.position_insertion_diagonal_compat ℂ A S a 1).1
  simpa [ins, Fin.sum_univ_two] using this

theorem plus_id {R : Type*} [Ring R] (e00 e01 e11 K T l0m E x xi lz m01 : R) (h01 : e00 + e11 = 1)
    (k0 : K * e00 = e00 * K) (k1 : K * e01 = e01 * K) (k3 : K * e11 = e11 * K) (t0 : T * e00 = e00 * T)
    (hxi : xi * x = 1) (hl : xi * l0m = l0m * xi) (hk : xi * K = K * xi) :
    l0m + K * (e00 * (E - (xi * E * x - E) + T) + e01 * m01 + e11 * (xi * E * x)) - lz =
      (l0m + K * E - lz) + (K * T * e00 + K * (e01 * m01) +
        (e11 - e00) * (xi * (lz * x - x * lz) + xi * (l0m + K * E - lz) * x - (l0m + K * E - lz))) := by
  have hΔ : xi * (lz * x - x * lz) + xi * (l0m + K * E - lz) * x - (l0m + K * E - lz) =
      K * (xi * E * x) - K * E := by
    have h2 : xi * (l0m + K * E - lz) * x = l0m * (xi * x) + K * (xi * E * x) - xi * lz * x := by
      rw [mul_sub, mul_add, ← mul_assoc xi K, hk, hl]; noncomm_ring
    rw [h2, hxi, mul_sub, ← mul_assoc xi x, hxi]; noncomm_ring
  rw [hΔ]
  have e : K * E = (e00 + e11) * (K * E) := by rw [h01, one_mul]
  have h3 : K * (e00 * (E - (xi * E * x - E) + T) + e01 * m01 + e11 * (xi * E * x)) =
      e00 * (K * (E - (xi * E * x - E) + T)) + K * (e01 * m01) + e11 * (K * (xi * E * x)) := by
    rw [mul_add, mul_add, ← mul_assoc K e00, k0, ← mul_assoc K e11, k3]; simp only [mul_assoc]
  rw [h3, mul_assoc K T e00, t0, ← mul_assoc K e00, k0]
  rw [show e11 = 1 - e00 by rw [← h01]; abel]
  noncomm_ring

theorem minus_id {R : Type*} [Ring R] (e00 e10 e11 K T l0m E lz m10 : R) (h01 : e00 + e11 = 1)
    (k0 : K * e00 = e00 * K) (k3 : K * e11 = e11 * K) (t3 : T * e11 = e11 * T) :
    l0m + K * (e00 * E + e10 * m10 + e11 * (E + T)) - lz =
      (l0m + K * E - lz) + (K * (e10 * m10) + K * T * e11) := by
  have e : K * E = (e00 + e11) * (K * E) := by rw [h01, one_mul]
  rw [mul_add, mul_add, ← mul_assoc K e00, k0, ← mul_assoc K e11, k3, mul_assoc K T e11, t3, ← mul_assoc K e11, k3]
  rw [show e11 = 1 - e00 by rw [← h01]; abel]
  noncomm_ring

theorem x_kMat (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) :
    (∀ Y : ℂ, star Y = Y → kMat st ((ofWord L st w).x Y)) ∧
      (∀ Y ∈ st.inv, star Y = Y → kMat st ((ofWord L st w).xi Y)) := by
  induction w with
  | nil => exact ⟨fun Y hY => kMat_io (x_mem st hY), fun Y hY hr => kMat_io (xi_mem st hY hr)⟩
  | cons l w ih =>
    obtain ⟨h1, h2⟩ := ih
    have hd : ∀ c : ℂ, ∀ i j, kMat st ((!![c • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] : M2 (SlopeTestRemainingChoices S A)) i j) := fun c =>
      kMat_of (kMat_smul c kMat_one) kMat_zero kMat_zero kMat_one
    by_cases hp : l.plus
    · have e : ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e]
      exact ⟨fun Y hY => kMat_mul (h1 Y hY) (kMat_ins _ (hd _)), fun Y hY hr => kMat_mul (h2 Y hY hr) (kMat_ins _ (hd _))⟩
    · have e : ofWord L st (l :: w) = (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e]
      exact ⟨fun Y hY => kMat_mul (h1 Y hY) (kMat_ins _ (hd _)), fun Y hY hr => kMat_mul (h2 Y hY hr) (kMat_ins _ (hd _))⟩

theorem main (L : LevelData A r) (st : Start A) (hL : IsStarLevel L) (hst : IsLevelStart L st)
    (w : List (Letter ℂ S)) (hA : admitted st w) :
    kMat st (ofWord L st w).c ∧ kMat st (ofWord L st w).ci ∧
    ∀ Y ∈ (ofWord L st w).inv, Y + 1 ∈ (ofWord L st w).inv →
      (ofWord L st w).l L Y - (st.frame : FrameData S A).l L Y ∈
        dSpan st ((st.frame : FrameData S A).l L Y) (kapL L) (tz L) := by
  induction w with
  | nil =>
    refine ⟨kMat_one, kMat_one, fun Y _ _ => ?_⟩
    rw [show ofWord L st ([] : List (Letter ℂ S)) = st.frame from rfl, sub_self]
    exact zero_mem _
  | cons l w ih =>
    have hA0 := hA
    obtain ⟨hnd, hre, hpt, hpw⟩ := hA
    have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
      List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hpw' := List.pairwise_cons.mp hpw
    have hAw : admitted st w :=
      ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
    obtain ⟨ihc, ihci, ihl⟩ := ih hAw
    have hfr : IsFrame L (ofWord L st w) := Formalism.FourierDecayAlt.P.frame_of_admissible_word A S r L st w hL hst hAw
    obtain ⟨p0, p1, pm1, -, -⟩ := hpt l (by simp)
    have hd := hpw'.1
    have m0 : l.pt ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p0 (fun l' hl' =>
      ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    have m1 : l.pt + 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p1 (fun l' hl' =>
      ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
    have mm1 : l.pt - 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ pm1 (fun l' hl' =>
      ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
    have hr : star l.pt = l.pt := hre l (by simp)
    have hr1 : star (l.pt + 1) = l.pt + 1 := by rw [star_add, hr, star_one]
    have hrm : star (l.pt - 1) = l.pt - 1 := by rw [star_sub, hr, star_one]
    obtain ⟨hx, hxi⟩ := x_kMat L st w
    have hrec := Formalism.FourierDecayAlt.P.admissible_rec_of_admissible A S r L st (l :: w) hA0
    have h01 := eU_sum (A := A) l.intersection_update_fsHerm_neg_one
    have kE : ∀ i j, kapL L * (eU l.intersection_update_fsHerm_neg_one i j : SlopeTestRemainingChoices S A) = eU l.intersection_update_fsHerm_neg_one i j * kapL L := fun i j => (eU_comm_io _ _ _ _).eq
    have tE : ∀ i j, tz L * (eU l.intersection_update_fsHerm_neg_one i j : SlopeTestRemainingChoices S A) = eU l.intersection_update_fsHerm_neg_one i j * tz L := fun i j => (eU_comm_io _ _ _ _).eq
    by_cases hp : l.plus
    · have e : ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e]
      refine ⟨?_, ?_, fun Y hY hY1 => ?_⟩
      · exact kMat_mul ihc (kMat_ins _ (kMat_of (kMat_smul _ (hxi _ p1 hr1)) kMat_zero kMat_zero (hx _ hr)))
      · exact kMat_mul ihci (kMat_ins _ (kMat_of (kMat_smul _ (hx _ hr1)) kMat_zero kMat_zero (hxi _ p0 hr)))
      · obtain ⟨hYf, hne0, -⟩ := hY
        obtain ⟨hY1f, -⟩ := hY1
        have ec := Formalism.FourierDecayAlt.P.ee_conjugation A S r L (ofWord L st w) Y l.pt hfr hYf hY1f m0 m1
          (fun h => hne0 (by rw [h, sub_self]))
        have hDD : (ofWord L st w).DD Y l.pt = (ofWord L st w).xi l.pt * (ofWord L st w).ee Y * (ofWord L st w).x l.pt -
            (ofWord L st w).ee Y := by
          have := sub_eq_iff_eq_add.mp ec
          rw [this]; abel
        have hl' : ((ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt).l L Y = io (L.l0 Y) + kapL L *
            ins l.intersection_update_fsHerm_neg_one !![(ofWord L st w).ee Y - (ofWord L st w).DD Y l.pt + tz L, -((Y - l.pt)⁻¹ • 1);
              0, (ofWord L st w).xi l.pt * (ofWord L st w).ee Y * (ofWord L st w).x l.pt] := rfl
        have hxk := hx _ hr
        have hxik := hxi _ p0 hr
        rw [hl', ins_up, hDD, plus_id _ _ _ _ _ _ _ _ _ _ _ h01 (kE 0 0) (kE 0 1) (kE 1 1) (tE 0 0)
          (hfr.x_xi _ m0).2 (commute_level_zero_element hst Y hxik).eq (comm_kap hst hxik).eq]
        have hδ := ihl Y hYf hY1f
        refine add_mem hδ (add_mem (add_mem (dSpan_phitau (kMat_eU _ _ _))
          (dSpan_phi (kMat_mul (kMat_eU _ _ _) (kMat_neg (kMat_smul _ kMat_one))))) ?_)
        refine dSpan_mul_left ?_ (kMat_sub (kMat_eU _ _ _) (kMat_eU _ _ _)) (comm_kap hst (kMat_sub (kMat_eU _ _ _)
          (kMat_eU _ _ _))) (comm_tz hst (kMat_sub (kMat_eU _ _ _) (kMat_eU _ _ _)))
        refine sub_mem (add_mem ?_ (dSpan_mul_right (dSpan_mul_left hδ hxik (comm_kap hst hxik) (comm_tz hst hxik)) hxk)) hδ
        have := dSpan_gen (X := (st.frame : FrameData S A).l L Y) (φ := kapL L) (τ := tz L) hxik hxk kMat_one
        rwa [mul_one] at this
    · have e : ofWord L st (l :: w) = (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e]
      refine ⟨?_, ?_, fun Y hY hY1 => ?_⟩
      · exact kMat_mul ihc (kMat_ins _ (kMat_of (kMat_smul _ (hxi _ pm1 hrm)) kMat_zero kMat_zero (hx _ hr)))
      · exact kMat_mul ihci (kMat_ins _ (kMat_of (kMat_smul _ (hx _ hrm)) kMat_zero kMat_zero (hxi _ p0 hr)))
      · have hq : (ofWord L st w).q (l.pt - 1) ≠ 0 := by
          have := hrec.2.2.2.2.2
          simp only [hp, if_false, Bool.false_eq_true] at this
          exact this.2
        have hfree := Formalism.FourierDecayAlt.P.frame_free_of_new_position A S r L st w l.intersection_update_fsHerm_neg_one hnd'.1
        have ml := Formalism.FourierDecayAlt.P.minus_letter_last_entry A S r L (ofWord L st w) l.intersection_update_fsHerm_neg_one l.pt
          ⟨hL, hfr, hfree, hr, m0, m1, mm1, hq⟩ Y hY hY1
        obtain ⟨hYf, -⟩ := hY
        obtain ⟨hY1f, -⟩ := hY1
        have hl' : ((ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt).l L Y = io (L.l0 Y) + kapL L *
            ((ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt).ee Y := rfl
        rw [hl', ml, ins_low, minus_id _ _ _ _ _ _ _ _ _ h01 (kE 0 0) (kE 1 1) (tE 1 1)]
        have hδ := ihl Y hYf hY1f
        refine add_mem hδ (add_mem (dSpan_phi (kMat_mul (kMat_eU _ _ _) (kMat_neg (kMat_smul _
          (kMat_mul (hxi _ p0 hr) (hxi _ pm1 hrm)))))) (dSpan_phitau (kMat_eU _ _ _)))

end

end Formalism.FourierDecayAlt.P.TLA.L1

namespace Formalism.FourierDecayAlt.P

theorem l_shape : Formalism.FourierDecayAlt.TL.LShape := by
  intro A S _ _ _ _ _ _ r L st w hL hst hA
  exact TLA.L1.main L st hL hst w hA

end Formalism.FourierDecayAlt.P
