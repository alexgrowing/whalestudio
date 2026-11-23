import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThLinKConst

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lamF altF)

def MuAltH (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∀ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X →
      ∀ n, ∃ y ∈ Rp p K' vp, PowerSeries.coeff n μ - PowerSeries.coeff n (altF K' p) = (p : K') * y

def DualH (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (n' : ℕ) (B : OmBasis p n'), Even n' → ∀ a b : Fin n', a.val % 2 = b.val % 2 →
    ∑ r, (sigW p)^[a.val] (B.omS r) * (sigW p)^[b.val] (B.om r) = if a = b then 1 else 0

variable {p : ℕ} [hp : Fact p.Prime] {n' r0 r1 : ℕ} {K' : Type} [Field K'] [Algebra (K0 p) K']

theorem triple_sum_comm {α β γ M : Type} [AddCommMonoid M] [Fintype β] [Fintype γ] (s : Finset α) (f : α → β → γ → M) :
    ∑ x ∈ s, ∑ a, ∑ b, f x a b = ∑ a, ∑ b, ∑ x ∈ s, f x a b := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem th_sSer_int (R : Subring K') (t : Fin n') (a : Fin r0) (b : Fin r1) : IntR R (sSer p K' t a b) := by
  intro n
  show (∑ l ∈ range (n.degree + 1),
    if n = Finsupp.single (posSub t (2 * l), a, b) (p ^ (2 * l)) then ((-1 : K') ^ l) else 0) ∈ R
  refine Subring.sum_mem _ fun l _ => ?_
  split_ifs
  · exact R.pow_mem (R.neg_mem R.one_mem) l
  · exact R.zero_mem

set_option maxHeartbeats 200000 in

theorem th_sumR {ν : ℕ} (w1 w2 : Fin ν → WW p) (P Q : Finset (Fin n'))
    (hQ : ∀ t' ∈ Q, posAdd t' 1 ∈ P)
    (hD : ∀ t ∈ P, ∀ t' ∈ Q, ∑ r, Aw K' (w1 r) t.val * Aw K' (w2 r) (t'.val + 1) = if t = posAdd t' 1 then 1 else 0)
    (S : Fin n' → MvPowerSeries (Zidx n' r0 r1) K') :
    ∑ r, (∑ t ∈ P, MvPowerSeries.C (Aw K' (w1 r) t.val) * S t) *
        (∑ t' ∈ Q, MvPowerSeries.C (Aw K' (w2 r) (t'.val + 1)) * S t' ^ p) =
      ∑ t' ∈ Q, S t' ^ p * S (posAdd t' 1) := by
  have key : ∀ t' ∈ Q, ∑ t ∈ P, ∑ r, MvPowerSeries.C (Aw K' (w1 r) t.val) * S t *
      (MvPowerSeries.C (Aw K' (w2 r) (t'.val + 1)) * S t' ^ p) = S t' ^ p * S (posAdd t' 1) := by
    intro t' ht'
    have e : ∀ t ∈ P, ∑ r, MvPowerSeries.C (Aw K' (w1 r) t.val) * S t *
        (MvPowerSeries.C (Aw K' (w2 r) (t'.val + 1)) * S t' ^ p) =
        if t = posAdd t' 1 then S t' ^ p * S t else 0 := by
      intro t ht
      have h1 : ∀ r, MvPowerSeries.C (Aw K' (w1 r) t.val) * S t *
          (MvPowerSeries.C (Aw K' (w2 r) (t'.val + 1)) * S t' ^ p) =
          MvPowerSeries.C (Aw K' (w1 r) t.val * Aw K' (w2 r) (t'.val + 1)) * (S t' ^ p * S t) := by
        intro r
        rw [map_mul]
        ring
      rw [Finset.sum_congr rfl (fun r _ => h1 r), ← Finset.sum_mul, ← map_sum, hD t ht t' ht']
      split_ifs <;> simp
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq' P (posAdd t' 1), if_pos (hQ t' ht')]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun t _ => Finset.sum_comm]
  exact Finset.sum_congr rfl key

abbrev Pev (n' : ℕ) : Finset (Fin n') := univ.filter fun s : Fin n' => ¬ IsOddPos s

abbrev Pod (n' : ℕ) : Finset (Fin n') := univ.filter fun s : Fin n' => IsOddPos s

theorem th_par_add (hev : Even n') (s : Fin n') (d : ℕ) : IsOddPos (posAdd s (2 * d)) ↔ IsOddPos s := by
  show (s.val + 2 * d) % n' % 2 = 1 ↔ s.val % 2 = 1
  rw [Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hev)]
  omega

theorem th_par_sub (hev : Even n') (s : Fin n') (d : ℕ) : IsOddPos (posSub s (2 * d)) ↔ IsOddPos s := by
  show (s.val + n' * (2 * d) - 2 * d) % n' % 2 = 1 ↔ s.val % 2 = 1
  rw [Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hev)]
  have h2 : 2 * d ≤ n' * (2 * d) := Nat.le_mul_of_pos_left _ s.pos
  have h3 : n' * (2 * d) % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (dvd_mul_right 2 d) n')
  generalize n' * (2 * d) = m at h2 h3
  omega

theorem th_par_one (hev : Even n') (s : Fin n') : IsOddPos (posAdd s 1) ↔ ¬ IsOddPos s := by
  show (s.val + 1) % n' % 2 = 1 ↔ ¬ s.val % 2 = 1
  rw [Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hev)]
  omega

theorem th_coordZ_inl (B : OmBasis p n') (r : Fin (n' / 2)) (a : Fin r0) (b : Fin r1) :
    coordZ B K' 1 (Sum.inl (r, a, b)) = linK K' (B.omS r) (Pev n') a b 0 := by
  simp only [coordZ, linK, Aw, wK', one_mul, add_zero, pow_zero, pow_one]

theorem th_coordZ_inr (B : OmBasis p n') (r : Fin (n' / 2)) (a : Fin r0) (b : Fin r1) :
    coordZ B K' 1 (Sum.inr (r, a, b)) = linK K' (B.om r) (Pod n') a b 0 := by
  simp only [coordZ, linK, Aw, wK', one_mul, add_zero, pow_zero, pow_one]

theorem th_dual_K (hT2 : DualH p) (hev : Even n') (B : OmBasis p n') (a b : Fin n') (hab : a.val % 2 = b.val % 2) :
    ∑ r, Aw K' (B.omS r) a.val * Aw K' (B.om r) b.val = if a = b then 1 else 0 := by
  have := congrArg (wK' p K') (hT2 n' B hev a b hab)
  simp only [wK', map_sum, map_mul] at this
  rw [apply_ite (algebraMap (WW p) (K0 p)), apply_ite (algebraMap (K0 p) K')] at this
  simpa [Aw, wK'] using this

theorem th_Aw_posAdd {w : WW p} (hper : (sigW p)^[n'] w = w) (s : Fin n') (d : ℕ) :
    Aw K' w (posAdd s d).val = Aw K' w (s.val + d) := by
  unfold Aw
  congr 1
  exact Function.IsPeriodicPt.iterate_mod_apply hper _

private theorem intR_C_of_mem {ι F : Type} [Field F] (R : Subring F) {c : F} (hc : c ∈ R) :
    IntR R (MvPowerSeries.C c : MvPowerSeries ι F) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hc
  · exact R.zero_mem

private theorem intR_add' {ι F : Type} [Field F] (R : Subring F) {f g : MvPowerSeries ι F}
    (hf : IntR R f) (hg : IntR R g) : IntR R (f + g) := by
  intro n
  rw [map_add]
  exact R.add_mem (hf n) (hg n)

private theorem intR_mul' {ι F : Type} [Field F] (R : Subring F) {f g : MvPowerSeries ι F}
    (hf : IntR R f) (hg : IntR R g) : IntR R (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact R.sum_mem fun x _ => R.mul_mem (hf _) (hg _)

private theorem intR_pow {ι F : Type} [Field F] (R : Subring F) {f : MvPowerSeries ι F}
    (hf : IntR R f) (k : ℕ) : IntR R (f ^ k) := by
  induction k with
  | zero =>
    classical
    intro n
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  | succ k ih =>
    rw [pow_succ]
    exact intR_mul' R ih hf

private theorem intR_sum' {ι F α : Type} [Field F] (R : Subring F) (s : Finset α)
    (f : α → MvPowerSeries ι F) (h : ∀ i ∈ s, IntR R (f i)) : IntR R (∑ i ∈ s, f i) := by
  intro n
  rw [map_sum]
  exact R.sum_mem fun i hi => h i hi n

private theorem cg_of_eq' {ι F : Type} [Field F] (R : Subring F) (pp : F)
    {f g : MvPowerSeries ι F} (h : f = g) : Cg R pp f g :=
  ⟨0, fun n => by rw [map_zero]; exact R.zero_mem, by rw [h, mul_zero, add_zero]⟩

private theorem cg_sub_multiset_valuation {ι F : Type} [Field F] (R : Subring F) (pp : F)
    {f g f' g' : MvPowerSeries ι F} (h : Cg R pp f g) (h' : Cg R pp f' g') :
    Cg R pp (f - f') (g - g') := by
  obtain ⟨Y, hY, rfl⟩ := h
  obtain ⟨Y', hY', rfl⟩ := h'
  refine ⟨Y - Y', fun n => ?_, by ring⟩
  rw [map_sub]
  exact R.sub_mem (hY n) (hY' n)

private theorem cg_trans' {ι F : Type} [Field F] (R : Subring F) (pp : F)
    {f g k : MvPowerSeries ι F} (h : Cg R pp f g) (h' : Cg R pp g k) : Cg R pp f k := by
  obtain ⟨Y, hY, rfl⟩ := h
  obtain ⟨Y', hY', rfl⟩ := h'
  exact ⟨Y' + Y, intR_add' R hY' hY, by ring⟩

private theorem cg_mul' {ι F : Type} [Field F] (R : Subring F) (pp : F) (hpp : pp ∈ R)
    {f g f' g' : MvPowerSeries ι F} (h : Cg R pp f g) (h' : Cg R pp f' g')
    (hg : IntR R g) (hf' : IntR R f') : Cg R pp (f * f') (g * g') := by
  obtain ⟨Y, hY, rfl⟩ := h
  obtain ⟨Y', hY', rfl⟩ := h'
  exact ⟨g * Y' + Y * (g' + MvPowerSeries.C pp * Y'),
    intR_add' R (intR_mul' R hg hY') (intR_mul' R hY hf'), by ring⟩

private theorem cg_pow' {ι F : Type} [Field F] (R : Subring F) (pp : F) (hpp : pp ∈ R)
    {f g : MvPowerSeries ι F} (h : Cg R pp f g) (hf : IntR R f) (hg : IntR R g) (k : ℕ) :
    Cg R pp (f ^ k) (g ^ k) := by
  induction k with
  | zero => exact cg_of_eq' R pp (by rw [pow_zero, pow_zero])
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact cg_mul' R pp hpp ih h (intR_pow R hg k) hf

private theorem cg_sum' {ι F α : Type} [Field F] (R : Subring F) (pp : F) (s : Finset α)
    {f g : α → MvPowerSeries ι F} (h : ∀ i, Cg R pp (f i) (g i)) :
    Cg R pp (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  choose Y hY heq using h
  exact ⟨∑ i ∈ s, Y i, intR_sum' R s Y (fun i _ => hY i), by
    rw [Finset.sum_congr rfl (fun i _ => heq i), Finset.sum_add_distrib, Finset.mul_sum]⟩

private theorem cg_C_mul' {ι F : Type} [Field F] (R : Subring F) (pp : F) {c : F} (hc : c ∈ R)
    {f g : MvPowerSeries ι F} (h : Cg R pp f g) :
    Cg R pp (MvPowerSeries.C c * f) (MvPowerSeries.C c * g) := by
  obtain ⟨Y, hY, rfl⟩ := h
  exact ⟨MvPowerSeries.C c * Y, intR_mul' R (intR_C_of_mem R hc) hY, by ring⟩

private theorem intR_of_cg_of_intR {ι F : Type} [Field F] (R : Subring F) (pp : F) (hpp : pp ∈ R)
    {f g : MvPowerSeries ι F} (h : Cg R pp f g) (hg : IntR R g) : IntR R f := by
  obtain ⟨Y, hY, rfl⟩ := h
  exact intR_add' R hg (intR_mul' R (intR_C_of_mem R hpp) hY)

theorem restTwoSums_of (hT1 : MuAltH p) (hT2 : DualH p)
    (hF : ∀ (n' r0 r1 : ℕ) (K' : Type) [Field K'] (R : Subring K'), FrobSumH p n' r0 r1 K' R) (hW : FrobWH p) :
    TwoSumsCondition p := by
  intro hp5 c hc n r0 r1 h2 hev B L _ _ vp hvp μ hμ0 hμ
  have hpR : (p : L) ∈ Rp p L vp := natCast_mem (Rp p L vp) p
  have hFS := hF n r0 r1 L (Rp p L vp)
  have hM := hT1 L vp hvp μ hμ0 hμ
  have hc0 : wK' p L c ∈ Rp p L vp := th_Aw_mem vp c 0
  have hc1 : wK' p L (sigW p c) ∈ Rp p L vp := th_Aw_mem vp c 1
  have hsI : ∀ (t : Fin n) (a : Fin r0) (b : Fin r1), IntR (Rp p L vp) (sSer p L t a b) :=
    fun t a b => th_sSer_int _ t a b
  have hLin0 : ∀ (w : WW p) (P : Finset (Fin n)) (e : Fin n → ℕ) (a : Fin r0) (b : Fin r1),
      IntR (Rp p L vp) (∑ t ∈ P, MvPowerSeries.C (Aw L w (e t)) * sSer p L t a b) :=
    fun w P e a b => intR_sum' _ P _ fun t _ =>
      intR_mul' _ (intR_C_of_mem _ (th_Aw_mem vp w _)) (hsI t a b)
  have hEv1 : ∀ s ∈ Pev n, ∀ d, posAdd s (2 * d) ∈ Pev n := by
    intro s hs d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rwa [th_par_add hev]
  have hEv2 : ∀ s ∈ Pev n, ∀ d, posSub s (2 * d) ∈ Pev n := by
    intro s hs d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rwa [th_par_sub hev]
  have hOd1 : ∀ s ∈ Pod n, ∀ d, posAdd s (2 * d) ∈ Pod n := by
    intro s hs d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rwa [th_par_add hev]
  have hOd2 : ∀ s ∈ Pod n, ∀ d, posSub s (2 * d) ∈ Pod n := by
    intro s hs d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rwa [th_par_sub hev]
  have hX : ∀ (r : Fin (n / 2)) (a : Fin r0) (b : Fin r1),
      Cg (Rp p L vp) (p : L) (sOf B L μ (Sum.inl (r, a, b)))
        (∑ t ∈ Pev n, MvPowerSeries.C (Aw L (B.omS r) t.val) * sSer p L t a b) := by
    intro r a b
    have h := th_claimM vp hFS hW μ hM (B.omS r) (B.fixS r) (Pev n) hEv1 hEv2 a b
    rw [← th_coordZ_inl] at h
    exact h
  have hZ : ∀ (r : Fin (n / 2)) (a : Fin r0) (b : Fin r1),
      Cg (Rp p L vp) (p : L) (sOf B L μ (Sum.inr (r, a, b)))
        (∑ t ∈ Pod n, MvPowerSeries.C (Aw L (B.om r) t.val) * sSer p L t a b) := by
    intro r a b
    have h := th_claimM vp hFS hW μ hM (B.om r) (B.fix r) (Pod n) hOd1 hOd2 a b
    rw [← th_coordZ_inr] at h
    exact h
  have hT1' : ∀ (r : Fin (n / 2)) (a : Fin r0) (b : Fin r1),
      Cg (Rp p L vp) (p : L)
        (MvPowerSeries.C (wK' p L c) * (sOf B L μ (Sum.inl (r, a, b)) * sOf B L μ (Sum.inr (r, a, b)) ^ p))
        (MvPowerSeries.C (wK' p L c) *
          ((∑ t ∈ Pev n, MvPowerSeries.C (Aw L (B.omS r) t.val) * sSer p L t a b) *
            (∑ t ∈ Pod n, MvPowerSeries.C (Aw L (B.om r) (t.val + 1)) * sSer p L t a b ^ p))) := by
    intro r a b
    have hZi : IntR (Rp p L vp) (sOf B L μ (Sum.inr (r, a, b))) :=
      intR_of_cg_of_intR _ _ hpR (hZ r a b) (hLin0 (B.om r) (Pod n) (fun t => t.val) a b)
    have hZp := cg_pow' _ _ hpR (hZ r a b) hZi (hLin0 (B.om r) (Pod n) (fun t => t.val) a b) p
    have hF1 := th_frob_lin vp hFS hW (B.om r) (Pod n) (fun t => t.val) (fun t => sSer p L t a b)
      (fun t => hsI t a b)
    have hZB := cg_trans' _ _ hZp hF1
    have hXZ := cg_mul' _ _ hpR (hX r a b) hZB
      (hLin0 (B.omS r) (Pev n) (fun t => t.val) a b) (intR_pow _ hZi p)
    exact cg_C_mul' _ _ hc0 hXZ
  have hT2' : ∀ (r : Fin (n / 2)) (a : Fin r0) (b : Fin r1),
      Cg (Rp p L vp) (p : L)
        (MvPowerSeries.C (wK' p L (sigW p c)) *
          (sOf B L μ (Sum.inr (r, a, b)) * sOf B L μ (Sum.inl (r, a, b)) ^ p))
        (MvPowerSeries.C (wK' p L (sigW p c)) *
          ((∑ t ∈ Pod n, MvPowerSeries.C (Aw L (B.om r) t.val) * sSer p L t a b) *
            (∑ t ∈ Pev n, MvPowerSeries.C (Aw L (B.omS r) (t.val + 1)) * sSer p L t a b ^ p))) := by
    intro r a b
    have hXi : IntR (Rp p L vp) (sOf B L μ (Sum.inl (r, a, b))) :=
      intR_of_cg_of_intR _ _ hpR (hX r a b) (hLin0 (B.omS r) (Pev n) (fun t => t.val) a b)
    have hXp := cg_pow' _ _ hpR (hX r a b) hXi (hLin0 (B.omS r) (Pev n) (fun t => t.val) a b) p
    have hF2 := th_frob_lin vp hFS hW (B.omS r) (Pev n) (fun t => t.val) (fun t => sSer p L t a b)
      (fun t => hsI t a b)
    have hXA := cg_trans' _ _ hXp hF2
    have hZX := cg_mul' _ _ hpR (hZ r a b) hXA
      (hLin0 (B.om r) (Pod n) (fun t => t.val) a b) (intR_pow _ hXi p)
    exact cg_C_mul' _ _ hc1 hZX
  have hAll := cg_sum' _ _ (Finset.univ : Finset (Eidx n r0 r1))
    fun e : Eidx n r0 r1 => cg_sub_multiset_valuation _ _ (hT1' e.1 e.2.1 e.2.2) (hT2' e.1 e.2.1 e.2.2)
  obtain ⟨Y, hY, heq⟩ := hAll
  obtain ⟨u, hu_def⟩ : ∃ u : Fin n → L,
      u = fun s => if IsOddPos s then wK' p L c else -wK' p L (sigW p c) := ⟨_, rfl⟩
  have hu : ∀ s, u s ∈ Rp p L vp := by
    intro s
    rw [hu_def]
    dsimp only
    split_ifs
    · exact hc0
    · exact (Rp p L vp).neg_mem hc1
  refine ⟨u, hu, Y, hY, ?_⟩
  refine heq.trans ?_
  congr 1
  have hR : (hhS p L u : MvPowerSeries (Zidx n r0 r1) L) = ∑ a : Fin r0, ∑ b : Fin r1, ∑ s : Fin n,
      MvPowerSeries.C (u s) * (sSer p L s a b ^ p * sSer p L (posAdd s 1) a b) := by
    unfold hhS
    simp only [Finset.mul_sum]
    exact triple_sum_comm _ _
  have hQ1 : ∀ t' ∈ Pod n, posAdd t' 1 ∈ Pev n := by
    intro t' ht'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht' ⊢
    rw [th_par_one hev]
    exact not_not.mpr ht'
  have hQ2 : ∀ t' ∈ Pev n, posAdd t' 1 ∈ Pod n := by
    intro t' ht'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht' ⊢
    rw [th_par_one hev]
    exact ht'
  have hD1 : ∀ t ∈ Pev n, ∀ t' ∈ Pod n,
      ∑ r, Aw L (B.omS r) t.val * Aw L (B.om r) (t'.val + 1) = if t = posAdd t' 1 then 1 else 0 := by
    intro t ht t' ht'
    have hpar : t.val % 2 = (posAdd t' 1).val % 2 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsOddPos] at ht ht'
      rw [th_odd_posAdd hev]
      omega
    rw [← th_dual_K (K' := L) hT2 hev B t (posAdd t' 1) hpar]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [th_Aw_posAdd (K' := L) (B.fix r)]
  have hD2 : ∀ t ∈ Pod n, ∀ t' ∈ Pev n,
      ∑ r, Aw L (B.om r) t.val * Aw L (B.omS r) (t'.val + 1) = if t = posAdd t' 1 then 1 else 0 := by
    intro t ht t' ht'
    have hpar : (posAdd t' 1).val % 2 = t.val % 2 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsOddPos] at ht ht'
      rw [th_odd_posAdd hev]
      omega
    have h := th_dual_K (K' := L) hT2 hev B (posAdd t' 1) t hpar
    calc ∑ r, Aw L (B.om r) t.val * Aw L (B.omS r) (t'.val + 1)
        = ∑ r, Aw L (B.omS r) (posAdd t' 1).val * Aw L (B.om r) t.val := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [th_Aw_posAdd (K' := L) (B.fixS r), mul_comm]
      _ = if posAdd t' 1 = t then 1 else 0 := h
      _ = if t = posAdd t' 1 then 1 else 0 := by
          by_cases h1 : t = posAdd t' 1
          · rw [if_pos h1, if_pos h1.symm]
          · rw [if_neg h1, if_neg (Ne.symm h1)]
  rw [hR]
  simp only [Fintype.sum_prod_type]
  rw [triple_sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e1 := th_sumR (B.omS) (B.om) (Pev n) (Pod n) hQ1 hD1 (fun t => sSer p L t a b)
  have e2 := th_sumR (B.om) (B.omS) (Pod n) (Pev n) hQ2 hD2 (fun t => sSer p L t a b)
  beta_reduce at e1 e2
  rw [e1, e2]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => IsOddPos s)
    (fun s => MvPowerSeries.C (u s) * (sSer p L s a b ^ p * sSer p L (posAdd s 1) a b))]
  rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [hu_def]
    dsimp only
    rw [if_pos (Finset.mem_filter.mp hs).2]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [hu_def]
    dsimp only
    rw [if_neg (Finset.mem_filter.mp hs).2, map_neg, neg_mul]

end Formalism.MainNotions.FormalGroupSystem.Pf
