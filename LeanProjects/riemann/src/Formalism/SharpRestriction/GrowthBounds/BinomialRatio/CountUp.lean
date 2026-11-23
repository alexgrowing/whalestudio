import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountDefs
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.LeAndHalfLeProdOneSubExpNegOfBounds

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

theorem finsum_le_of_inj {α τ : Type*} (F : α → ℚ) (G : τ → ℚ) (Φ : α → τ) (hG0 : ∀ t, 0 ≤ G t)
    (hGfin : (support G).Finite) (hinj : Set.InjOn Φ (support F)) (hFG : ∀ a ∈ support F, F a = G (Φ a)) :
    (support F).Finite ∧ ∑ᶠ a, F a ≤ ∑ᶠ t, G t := by
  have hsub : Φ '' support F ⊆ support G := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_support, ← hFG a ha]
    exact ha
  have hFfin : (support F).Finite := Set.Finite.of_finite_image (hGfin.subset hsub) hinj
  refine ⟨hFfin, ?_⟩
  calc ∑ᶠ a, F a = ∑ᶠ a ∈ support F, F a := (finsum_mem_support F).symm
    _ = ∑ᶠ a ∈ support F, G (Φ a) := finsum_mem_congr rfl (fun a ha => hFG a ha)
    _ = ∑ᶠ t ∈ Φ '' support F, G t := (finsum_mem_image hinj).symm
    _ = ∑ᶠ t, (Φ '' support F).indicator G t := finsum_mem_def _ _
    _ ≤ ∑ᶠ t, G t := by
        rw [finsum_eq_sum_of_support_subset _ (s := hGfin.toFinset)
            (by intro x hx; rw [Set.support_indicator] at hx; simpa using hx.2),
          finsum_eq_sum_of_support_subset G (s := hGfin.toFinset) (by intro x hx; simpa using hx)]
        exact Finset.sum_le_sum fun t _ => Set.indicator_le_self' (fun x _ => hG0 x) t

theorem finsum_curry3 {α β γ : Type*} (F : α × β × γ → ℚ) (hfin : (support F).Finite) :
    ∑ᶠ z, F z = ∑ᶠ a, ∑ᶠ b, ∑ᶠ c, F (a, b, c) := by
  rw [finsum_curry F hfin]
  refine finsum_congr fun a => ?_
  exact finsum_curry (fun bc => F (a, bc)) (hfin.preimage (fun x _ y _ hxy => (Prod.mk.inj hxy).2))

theorem antitone_of_adj {r : ℕ} {f : Fin r → ℤ} (h : ∀ i j : Fin r, i.val + 1 = j.val → f j ≤ f i) : Antitone f := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  change i ≤ j at hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (h ⟨k, by omega⟩ ⟨k + 1, hj⟩ rfl).trans (ih (by omega))

theorem Strip.anti_left {r : ℕ} {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) : Antitone nu :=
  antitone_of_adj fun i j hij => (h.2.1 i j hij).trans (h.1 i)

theorem Strip.anti_right {r : ℕ} {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) : Antitone mu :=
  antitone_of_adj fun i j hij => (h.1 j).trans (h.2.1 i j hij)

theorem IsChain.anti_last {N r : ℕ} {LL : ChainLetters (N + 1)} {ka : Fin (N + 1 + 1) → Fin r → ℤ}
    (h : IsChain LL ka) : Antitone (ka (Fin.last (N + 1))) := by
  have hs := h.2 (Fin.last N)
  rw [← Fin.succ_last]
  split_ifs at hs with hv
  · exact hs.anti_left
  · exact hs.anti_right

theorem wdim_pos {r : ℕ} {lam : Fin r → ℤ} (h : Antitone lam) : 0 < wdim lam := by
  unfold wdim
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  split_ifs with hij
  · have h1 : (lam j : ℚ) ≤ lam i := by exact_mod_cast h hij.le
    have h2' : (i : ℕ) < (j : ℕ) := hij
    have h2 : (i : ℚ) < j := by exact_mod_cast h2'
    apply div_pos <;> linarith
  · exact one_pos

theorem hockey (r B : ℕ) : ∑ i ∈ Finset.range (B + 1), Nat.choose (i + r) r = Nat.choose (B + r + 1) (r + 1) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Finset.sum_range_succ, ih, show B + 1 + r + 1 = (B + r + 1) + 1 by omega, Nat.choose_succ_succ (B + r + 1) r,
      show B + 1 + r = B + r + 1 by omega]
    ring

open Classical in
theorem hockey_fin (r B : ℕ) (hr : 1 ≤ r) :
    ∑ᶠ jp : ℕ, (if jp ≤ B then (sdXi r (B - jp) : ℚ) else 0) = (sd r B : ℚ) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have key : ∑ jp ∈ Finset.range (B + 1), Nat.choose (B - jp + r') r' = Nat.choose (B + r' + 1) (r' + 1) := by
    rw [← hockey r' B, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    congr 1
    omega
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (B + 1)) ?_]
  · unfold sd sdXi
    rw [show B + (r' + 1) = B + r' + 1 by omega, ← key, Nat.cast_sum]
    refine Finset.sum_congr rfl fun jp hjp => ?_
    rw [Finset.mem_range] at hjp
    rw [if_pos (by omega), show B - jp + (r' + 1) - 1 = B - jp + r' by omega, show r' + 1 - 1 = r' by omega]
  · intro jp hjp
    rw [Function.mem_support] at hjp
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact hjp (if_neg (by omega))

abbrev Tgt (s r : ℕ) := (Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) × (Fin r → ℤ) × ℕ

def Inter {r : ℕ} (mu : Fin (r + 1) → ℤ) (lam : Fin r → ℤ) : Prop :=
  ∀ i : Fin r, mu i.succ ≤ lam i ∧ lam i ≤ mu i.castSucc

open Classical in

def Gt {s r : ℕ} (LLk : ChainLetters (2 * s + 1)) (B : ℕ) (t : Tgt s r) : ℚ :=
  if IsChain LLk t.1 ∧ Inter (t.1 (Fin.last _)) t.2.1 ∧ t.2.2 ≤ B then wdim t.2.1 * (sdXi r (B - t.2.2) : ℚ) else 0

theorem inter_anti {r : ℕ} {mu : Fin (r + 1) → ℤ} {lam : Fin r → ℤ} (h : Inter mu lam) : Antitone lam :=
  antitone_of_adj fun i j hij => by
    have h1 := (h j).2
    have h2 := (h i).1
    have e : j.castSucc = i.succ := Fin.ext (by simp only [Fin.coe_castSucc, Fin.val_succ]; omega)
    rw [e] at h1
    exact h1.trans h2

theorem Gt_nonneg {s r : ℕ} (LLk : ChainLetters (2 * s + 1)) (B : ℕ) (t : Tgt s r) : 0 ≤ Gt LLk B t := by
  unfold Gt
  split_ifs with h
  · exact mul_nonneg (wdim_pos (inter_anti h.2.1)).le (Nat.cast_nonneg _)
  · exact le_rfl

theorem sdXi_pos (r g : ℕ) (hr : 1 ≤ r) : 0 < sdXi r g := by
  unfold sdXi
  exact Nat.choose_pos (by omega)

open Classical in
theorem chains_finite (hCD : ChainDimAt) {s r : ℕ} (LLk : ChainLetters (2 * s + 1)) :
    {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ | IsChain LLk mu}.Finite := by
  have h := hCD (2 * s + 1) (r + 1) LLk
  unfold chainSum at h
  by_contra hinf
  have hpos : (0 : ℚ) < ∏ i, (sdXi (r + 1) (LLk.deg i) : ℚ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast sdXi_pos (r + 1) _ (by omega)
  rw [finsum_of_infinite_support ?_] at h
  · linarith
  · refine Set.Infinite.mono ?_ hinf
    intro ka hc
    simp only [mem_support]
    rw [if_pos ⟨hc, fun k => k.elim0⟩]
    exact (wdim_pos (IsChain.anti_last hc)).ne'

theorem Gt_support_finite (hCD : ChainDimAt) {s r : ℕ} (LLk : ChainLetters (2 * s + 1)) (B : ℕ) :
    (support (Gt (r := r) LLk B)).Finite := by
  refine Set.Finite.subset ((chains_finite hCD (r := r) LLk).biUnion fun mu _ =>
    (Set.finite_singleton mu).prod ((Set.Finite.pi fun (i : Fin r) =>
      Set.finite_Icc (mu (Fin.last _) i.succ) (mu (Fin.last _) i.castSucc)).prod (Set.finite_Iic B))) ?_
  rintro ⟨mu, lam, jp⟩ ht
  rw [mem_support] at ht
  unfold Gt at ht
  dsimp only at ht
  split_ifs at ht with hc
  · obtain ⟨h1, h2, h3⟩ := hc
    refine Set.mem_biUnion (x := mu) h1 ?_
    simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
      Set.mem_Iic]
    exact ⟨trivial, fun i => ⟨(h2 i).1, (h2 i).2⟩, h3⟩
  · exact absurd rfl ht

theorem finsum_mulQ {α : Type*} (f : α → ℚ) (c : ℚ) : (∑ᶠ a, f a) * c = ∑ᶠ a, f a * c := by
  exact finsum_mul f c

theorem mul_finsumQ {α : Type*} (f : α → ℚ) (c : ℚ) : c * (∑ᶠ a, f a) = ∑ᶠ a, c * f a := by
  exact mul_finsum f c

open Classical in
theorem Gt_sum (hCD : ChainDimAt) (hNB : NumBranchAt) {s r : ℕ} (hr : 1 ≤ r) (LLk : ChainLetters (2 * s + 1)) (B : ℕ) :
    ∑ᶠ t, Gt (r := r) LLk B t = (∏ i, (sdXi (r + 1) (LLk.deg i) : ℚ)) * (sd r B : ℚ) := by
  rw [finsum_curry3 _ (Gt_support_finite hCD LLk B)]
  have hin : ∀ (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ),
      ∑ᶠ jp : ℕ, Gt LLk B (mu, lam, jp) =
        (if IsChain LLk mu ∧ Inter (mu (Fin.last _)) lam then wdim lam else 0) * (sd r B : ℚ) := by
    intro mu lam
    rw [← hockey_fin r B hr, mul_finsumQ]
    refine finsum_congr fun jp => ?_
    unfold Gt
    dsimp only
    by_cases h1 : IsChain LLk mu ∧ Inter (mu (Fin.last _)) lam <;> by_cases h2 : jp ≤ B
    · rw [if_pos ⟨h1.1, h1.2, h2⟩, if_pos h1, if_pos h2]
    · rw [if_neg (fun h => h2 h.2.2), if_pos h1, if_neg h2, mul_zero]
    · rw [if_neg (fun h => h1 ⟨h.1, h.2.1⟩), if_neg h1, zero_mul]
    · rw [if_neg (fun h => h1 ⟨h.1, h.2.1⟩), if_neg h1, zero_mul]
  have hmid : ∀ mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ,
      ∑ᶠ lam : Fin r → ℤ, ∑ᶠ jp : ℕ, Gt LLk B (mu, lam, jp) =
        (if IsChain LLk mu then wdim (mu (Fin.last _)) else 0) * (sd r B : ℚ) := by
    intro mu
    rw [finsum_congr (hin mu), ← finsum_mulQ]
    congr 1
    by_cases hc : IsChain LLk mu
    · rw [if_pos hc, hNB r (mu (Fin.last _)) (IsChain.anti_last hc)]
      refine finsum_congr fun lam => ?_
      by_cases hI : ∀ i : Fin r, mu (Fin.last _) i.succ ≤ lam i ∧ lam i ≤ mu (Fin.last _) i.castSucc
      · rw [if_pos (show IsChain LLk mu ∧ Inter (mu (Fin.last _)) lam from ⟨hc, hI⟩), if_pos hI]
      · rw [if_neg (show ¬ (IsChain LLk mu ∧ Inter (mu (Fin.last _)) lam) from fun h => hI h.2), if_neg hI]
    · rw [if_neg hc]
      exact finsum_eq_zero_of_forall_eq_zero fun lam => if_neg (fun h => hc h.1)
  rw [finsum_congr hmid, ← finsum_mulQ]
  congr 1
  rw [← hCD (2 * s + 1) (r + 1) LLk]
  unfold chainSum
  refine finsum_congr fun mu => ?_
  by_cases hc : IsChain LLk mu
  · rw [if_pos hc, if_pos]
    exact ⟨hc, fun k => k.elim0⟩
  · rw [if_neg hc, if_neg]
    exact fun h => hc h.1

def kLetters {s : ℕ} (A0 : ℕ) (A C : Fin s → ℕ) : ChainLetters (2 * s + 1) where
  vec := fun a => decide ((a : ℕ) = 0 ∨ (a : ℕ) % 2 = 1)
  deg := fun a => if (a : ℕ) = 0 then A0 else
    if h : ((a : ℕ) - 1) / 2 < s then (if (a : ℕ) % 2 = 1 then A ⟨((a : ℕ) - 1) / 2, h⟩ else C ⟨((a : ℕ) - 1) / 2, h⟩) else 0

theorem prod_odd_even (h : ℕ → ℚ) (n : ℕ) :
    ∏ a ∈ Finset.range (2 * n + 1), h a = h 0 * ∏ i ∈ Finset.range n, (h (2 * i + 1) * h (2 * i + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ _ n, show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring,
      Finset.prod_range_succ _ (2 * n + 1 + 1), Finset.prod_range_succ _ (2 * n + 1), ih,
      show 2 * n + 1 + 1 = 2 * n + 2 by ring]
    ring

theorem prod_kLetters {s : ℕ} (r A0 : ℕ) (A C : Fin s → ℕ) :
    ∏ a, (sdXi (r + 1) ((kLetters A0 A C).deg a) : ℚ) = (sd r A0 : ℚ) * ∏ i, ((sd r (A i) : ℚ) * (sd r (C i) : ℚ)) := by
  set kd : ℕ → ℕ := fun n => if n = 0 then A0 else if h : (n - 1) / 2 < s then
      (if n % 2 = 1 then A ⟨(n - 1) / 2, h⟩ else C ⟨(n - 1) / 2, h⟩) else 0 with hkd
  have hdeg : ∀ a, (kLetters A0 A C).deg a = kd a.val := fun a => rfl
  have hsd : ∀ g, (sdXi (r + 1) g : ℚ) = (sd r g : ℚ) := fun g => by
    unfold sdXi sd
    rw [show g + (r + 1) - 1 = g + r by omega, show r + 1 - 1 = r by omega]
  have k1 : ∀ i : Fin s, kd (2 * i.val + 1) = A i := by
    intro i
    have hi := i.isLt
    simp only [hkd]
    rw [if_neg (by omega), dif_pos (by omega), if_pos (by omega)]
    simp only [show (2 * i.val + 1 - 1) / 2 = i.val by omega, Fin.eta]
  have k2 : ∀ i : Fin s, kd (2 * i.val + 2) = C i := by
    intro i
    have hi := i.isLt
    simp only [hkd]
    rw [if_neg (by omega), dif_pos (by omega), if_neg (by omega)]
    simp only [show (2 * i.val + 2 - 1) / 2 = i.val by omega, Fin.eta]
  simp only [hdeg, hsd]
  refine (Fin.prod_univ_eq_prod_range (fun n => (sd r (kd n) : ℚ)) (2 * s + 1)).trans ?_
  rw [prod_odd_even]
  refine congrArg₂ (· * ·) (by simp [hkd]) ((Fin.prod_univ_eq_prod_range
    (fun n => (sd r (kd (2 * n + 1)) : ℚ) * (sd r (kd (2 * n + 2)) : ℚ)) s).symm.trans ?_)
  exact Finset.prod_congr rfl fun i _ => by rw [k1 i, k2 i]

abbrev FinalTheorems (s r t : ℕ) := SegBlock s r × ((Fin t → ℕ) × ℕ) × (Fin (2 * s + 1 + 1) → Fin r → ℤ)

abbrev BD (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (m : ℝ) (b : SegBlock (segS X.TT j) X.m) :
    BlockData (2 * segS X.TT j + 1) :=
  blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b

def SrcOK (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (m : ℝ)
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) (z : FinalTheorems (segS X.TT j) X.m (X.seg C0 CE1 CE2 j).t) : Prop :=
  (Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) z.1 ∧ z.1.rz = rz ∧ z.1.ry = ry) ∧
    (BD C0 CE1 CE2 X j m z.1).LevelOK z.2.1.1 z.2.1.2 ∧
    IsChain ((BD C0 CE1 CE2 X j m z.1).lettersAt z.2.1.1 z.2.1.2) z.2.2 ∧
    ChainOK (BD C0 CE1 CE2 X j m z.1).T.J (BD C0 CE1 CE2 X j m z.1).T.thr z.2.2

open Classical in

def Fs (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (m : ℝ)
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) (z : FinalTheorems (segS X.TT j) X.m (X.seg C0 CE1 CE2 j).t) : ℚ :=
  if SrcOK C0 CE1 CE2 X j m rz ry z then
    wdim (z.2.2 (Fin.last _)) * (sdXi X.m ((X.seg C0 CE1 CE2 j).bPlus - z.2.1.2) : ℚ) else 0

open Classical in
theorem chainCount_eq (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (m : ℝ)
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) :
    chainCount C0 CE1 CE2 X j m rz ry = ∑ᶠ b, ∑ᶠ x, ∑ᶠ ka, Fs C0 CE1 CE2 X j m rz ry (b, x, ka) := by
  unfold chainCount
  refine finsum_congr fun b => ?_
  split_ifs with hK
  · dsimp only
    refine finsum_congr fun x => ?_
    split_ifs with hL
    · unfold chainSum
      rw [finsum_mulQ]
      refine finsum_congr fun ka => ?_
      unfold Fs SrcOK
      dsimp only
      split_ifs with hc hs hs
      · rfl
      · exact absurd ⟨hK, hL, hc.1, hc.2⟩ hs
      · exact absurd hs.2.2 hc
      · simp
    · symm
      refine finsum_eq_zero_of_forall_eq_zero fun ka => ?_
      unfold Fs SrcOK
      dsimp only
      rw [if_neg]
      exact fun h => hL h.2.1
  · symm
    refine finsum_eq_zero_of_forall_eq_zero fun x => finsum_eq_zero_of_forall_eq_zero fun ka => ?_
    unfold Fs SrcOK
    dsimp only
    rw [if_neg]
    exact fun h => hK h.1

def mmLetters (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) :
    ChainLetters (2 * segS X.TT j + 1) :=
  kLetters ((X.seg C0 CE1 CE2 j).A0 X.p).toNat
    (fun i => coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i)
    (fun i => coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i)

def MatchUpAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∃ Φ : FinalTheorems (segS X.TT j) X.m (X.seg C0 CE1 CE2 j).t → Tgt (segS X.TT j) X.m,
        Set.InjOn Φ {z | SrcOK C0 CE1 CE2 X j m rz ry z} ∧
        ∀ z, SrcOK C0 CE1 CE2 X j m rz ry z →
          IsChain (mmLetters C0 CE1 CE2 X j rz ry) (Φ z).1 ∧ Inter ((Φ z).1 (Fin.last _)) (Φ z).2.1 ∧
            (Φ z).2.1 = z.2.2 (Fin.last _) ∧ (Φ z).2.2 = z.2.1.2

def RestMatchUp : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => MatchUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem countUp_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc H : ℝ} (hCD : ChainDimAt) (hNB : NumBranchAt)
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 H X)
    (hM : MatchUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : CountUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j m hm rz ry hd
  classical
  obtain ⟨Φ, hinj, hΦ⟩ := hM X hD hI hc j m hm rz ry hd
  have hs := hstd X hD hI hc
  have hr : 1 ≤ X.m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne X.m)
  have hsupp : ∀ z, z ∈ support (Fs C0 CE1 CE2 X j m rz ry) → SrcOK C0 CE1 CE2 X j m rz ry z := by
    intro z hz
    by_contra hn
    apply hz
    unfold Fs
    rw [if_neg hn]
  have hmain := finsum_le_of_inj (Fs C0 CE1 CE2 X j m rz ry)
    (Gt (r := X.m) (mmLetters C0 CE1 CE2 X j rz ry) (X.seg C0 CE1 CE2 j).bPlus) Φ
    (Gt_nonneg _ _) (Gt_support_finite hCD _ _) (hinj.mono hsupp) (by
      intro z hz
      have hz' := hsupp z hz
      obtain ⟨h1, h2, h3, h4⟩ := hΦ z hz'
      have hjp : z.2.1.2 ≤ (X.seg C0 CE1 CE2 j).bPlus := le_trans hz'.2.1.2 (min_le_right _ _)
      unfold Fs Gt
      rw [if_pos hz', if_pos ⟨h1, h2, by rw [h4]; exact hjp⟩, h3, h4])
  rw [chainCount_eq, ← finsum_curry3 _ hmain.1]
  refine le_trans hmain.2 ?_
  rw [Gt_sum hCD hNB hr]
  unfold mmLetters
  rw [prod_kLetters]
  have hA0 : 0 ≤ (X.seg C0 CE1 CE2 j).A0 X.p := by
    have h1 := hs.half_ratio_le_segment_base_of_std j
    have h2 : (0 : ℝ) ≤ (X.a : ℝ) / (2 * X.Q) := by
      have := hs.Q1
      positivity
    exact_mod_cast le_trans h2 h1
  have hsym : ∀ g : ℕ, symDim (X.m + 1) (g : ℤ) = sd X.m g := fun g => by
    unfold symDim sd
    rw [if_neg (by omega)]
    simp
  have hsymA : symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) = sd X.m ((X.seg C0 CE1 CE2 j).A0 X.p).toNat := by
    unfold symDim sd
    rw [if_neg (by omega)]
    simp
  unfold mmB dimMM
  rw [hsymA, hsym]
  simp only [hsym]
  push_cast
  exact le_rfl

theorem restCountUp_of (hCD : ChainDimAt) (hNB : NumBranchAt) (hM : RestMatchUp) : RestCountUp := by
  have hstd : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc =>
      ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
    TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
      fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
        fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
  refine TransportedAlt.mono ?_ (hstd.and hM)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨h1, h2⟩
  exact countUp_of hCD hNB h1 h2

end Formalism.MainNotions.ColumnSystems.Pf
