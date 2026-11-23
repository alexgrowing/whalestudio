import Formalism.SharpRestriction.Divisibility.OrbitPlaces

noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

theorem orbit_map_add_natCast (D : D7) (p : ℕ) (z : Pl D) (s : ZMod (nP D p)) (e : ℕ) :
    orbMap D p z (s + (e : ZMod (nP D p))) = posPl D p (orbMap D p z s) e := by
  unfold orbMap
  rw [posPl_add, ← posPl_mod D p z (s.val + e), ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]

theorem base_shift_add_nsmul (X : Inst D L) (h t : HH D) (m : ℕ) : X.bs h (t + m • h) = X.bs h t := by
  induction m with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]

theorem base_shift_idempotent (X : Inst D L) (h t : HH D) : X.bs h (X.bs h t) = X.bs h t := by
  obtain ⟨i, hi⟩ := X.bs_orb h t
  calc X.bs h (X.bs h t) = X.bs h (X.bs h t + i • h) := (base_shift_add_nsmul X h (X.bs h t) i).symm
    _ = X.bs h t := by rw [hi]

theorem posPl_false_eq_odd_add_nsmul {p : ℕ} (hsg : IsSg D p) (t0 : HH D) (n : ℕ) :
    posPl D p (false, t0) n = (decide (Odd n), t0 + n • hP D p) := by
  first
    | (simp [posPl, Formalism.MainNotions.G.partner]; try exact fun _ => hsg)
    | (simp [posPl, Formalism.BasicNotions.partner]; try exact fun _ => hsg)

theorem sum_tops_on_orbit (X : Inst D L) {p : ℕ} (hsg : IsSg D p) {t0 : HH D} (ht0 : t0 ∈ reps X p)
    (TT : Finset (ZMod (nP D p))) (hTT : ∀ s, s ∈ TT ↔ IsTopPl D (orbMap D p (false, t0) s))
    (F : HH D → ℝ) :
    ∑ t ∈ topsOn X p t0, F t = ∑ s ∈ TT, F (orbMap D p (false, t0) s).2 := by
  have hst : stepP D p = 2 • hP D p := if_pos hsg
  have hb0 : X.bs (2 • hP D p) t0 = t0 := by
    unfold reps at ht0
    rw [hst] at ht0
    obtain ⟨t', _, rfl⟩ := Finset.mem_image.1 ht0
    exact base_shift_idempotent X _ t'
  symm
  refine Finset.sum_nbij (fun s => (orbMap D p (false, t0) s).2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro s hs
    have hT := (hTT s).1 hs
    have e1 : orbMap D p (false, t0) s = (decide (Odd s.val), t0 + s.val • hP D p) :=
      posPl_false_eq_odd_add_nsmul hsg t0 s.val
    rw [e1] at hT ⊢
    have hev : ¬ Odd s.val := by simpa using hT.1
    obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hev
    simp only [topsOn, Finset.mem_filter]
    refine ⟨hT.2, ?_⟩
    rw [hst, hm, show (m + m) • hP D p = m • (2 • hP D p) by rw [smul_smul, mul_two], base_shift_add_nsmul, hb0]
  · intro s1 hs1 s2 hs2 heq
    have hT1 := (hTT s1).1 hs1
    have hT2 := (hTT s2).1 hs2
    have : orbMap D p (false, t0) s1 = orbMap D p (false, t0) s2 :=
      Prod.ext (hT1.1.trans hT2.1.symm) heq
    exact ZMod.val_injective _ (posPl_inj D p (false, t0) _ _ (ZMod.val_lt s1) (ZMod.val_lt s2) this)
  · intro t ht
    have ht' := Finset.mem_coe.1 ht
    simp only [topsOn, Finset.mem_filter] at ht'
    obtain ⟨hTT', hbt⟩ := ht'
    obtain ⟨m, hm⟩ := X.bs_orb (stepP D p) t
    rw [hbt, hst] at hm
    have ho : orbMap D p (false, t0) ((m + m : ℕ) : ZMod (nP D p)) = (false, t) := by
      unfold orbMap
      rw [ZMod.val_natCast, posPl_mod, posPl_false_eq_odd_add_nsmul hsg]
      have hodd : ¬ Odd (m + m) := Nat.not_odd_iff_even.2 ⟨m, rfl⟩
      refine Prod.ext (by simp [hodd]) ?_
      show t0 + (m + m) • hP D p = t
      rw [show (m + m) • hP D p = m • (2 • hP D p) by rw [smul_smul, mul_two]]
      exact hm
    refine ⟨((m + m : ℕ) : ZMod (nP D p)), ?_, ?_⟩
    · rw [Finset.mem_coe, hTT, ho]
      exact ⟨rfl, hTT'⟩
    · show (orbMap D p (false, t0) _).2 = t
      rw [ho]

theorem tsum_le_tsum_of_nonneg_le {f g : ℕ → ℝ} (hf0 : ∀ e, 0 ≤ f e) (hle : ∀ e, f e ≤ g e) (hg : Summable g) :
    ∑' e, f e ≤ ∑' e, g e := by
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hle hg
  first
    | exact Summable.tsum_le_tsum hle hfs hg
    | exact tsum_le_tsum hle hfs hg

theorem orbit_local_term_nonneg (Lc : Formalism.MainNotions.product_zeroth_first_parts.Loc) (s : ZMod Lc.d) : 0 ≤ Lc.baseTerm s := by
  apply tsum_nonneg
  intro e
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem mem_top_orbit_set_iff (E : Ent D) (p : ℕ) [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p]) (s : ZMod (nP D p)) :
    s ∈ (orbLoc E p h u i z Th).TT ↔ IsTopPl D (orbMap D p z s) := by
  first
    | exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
    | simp [orbLoc]

theorem orbit_local_capacity_eq (E : Ent D) (p : ℕ) [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p]) (s : ZMod (nP D p)) :
    (((orbLoc E p h u i z Th).cap s : ℕ) : ℝ) = E.cap u i (orbMap D p z s) := by
  have hT := mem_top_orbit_set_iff E p h u i z Th s
  simp only [Formalism.MainNotions.product_zeroth_first_parts.Loc.cap, Ent.cap, Nat.cast_ite]
  split_ifs <;> first
    | (simp [Ent.row, orbLoc]; done)
    | tauto
    | simp_all

theorem summable_truncated_geometric (x l : ℝ) (hl : 1 < l) (c : ℕ → ℝ) (hc : ∀ e, 0 ≤ c e) (P : ℕ → Prop) [DecidablePred P] :
    Summable fun e : ℕ => if P e then max (x / l ^ e - c e) 0 else 0 := by
  have hl0 : (0 : ℝ) < l := by linarith
  have hq0 : (0 : ℝ) ≤ 1 / l := one_div_nonneg.2 hl0.le
  have hq1 : 1 / l < 1 := (div_lt_one hl0).2 hl
  have hg : Summable (fun e : ℕ => |x| * (1 / l) ^ e) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left |x|
  refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hg
  · split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  · have hpow : (0 : ℝ) < l ^ e := pow_pos hl0 e
    have h2 : (0 : ℝ) ≤ |x| * (1 / l) ^ e := mul_nonneg (abs_nonneg x) (pow_nonneg hq0 e)
    have h1 : x / l ^ e ≤ |x| * (1 / l) ^ e := by
      rw [one_div_pow, ← div_eq_mul_one_div]
      first
        | exact div_le_div_of_nonneg_right (le_abs_self x) hpow.le
        | exact (div_le_div_iff_of_pos_right hpow).2 (le_abs_self x)
        | exact (div_le_div_right hpow).2 (le_abs_self x)
    split_ifs
    · exact max_le (by linarith [hc e]) h2
    · exact h2

theorem orbit_place_term_le_sum {X : Inst D L} {E : Ent D} (hS : Shape D L X E) (K : Consts) (hK1 : 0 ≤ K.dl1)
    (hK2 : 0 ≤ K.dl2) {p : ℕ} [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) {i : ℕ} (hi : i < D.R.m)
    {r : Pl D} (hr : r ∈ repsPl X p) (hk : r ∈ kindBC D p)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p]) :
    g0Pl X K p (i + 1) r ≤ ∑ s ∈ (orbLoc E p h u i r Th).TT, (orbLoc E p h u i r Th).baseTerm s := by
  have hnn : 0 ≤ ∑ s ∈ (orbLoc E p h u i r Th).TT, (orbLoc E p h u i r Th).baseTerm s :=
    Finset.sum_nonneg fun s _ => orbit_local_term_nonneg _ s
  unfold g0Pl
  split_ifs with hr1
  swap
  · exact hnn
  refine max_le ?_ hnn
  have hsg : IsSg D p := by
    rcases (Finset.mem_filter.1 hk).2 with h1 | h1
    · exact h1
    · rw [hr1] at h1; exact absurd h1 (by decide)
  obtain ⟨t0, ht0, rfl⟩ : ∃ t0 ∈ reps X p, r = (false, t0) := by
    unfold repsPl at hr
    rw [if_pos hsg] at hr
    obtain ⟨t0, ht0, e⟩ := Finset.mem_image.1 hr
    exact ⟨t0, ht0, e.symm⟩
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) h.five)
  have ha : 1 < L.sc.a := hS.xa.2
  have hlog : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg hp1 (by linarith)
  have hdl : 0 ≤ dl X K p t0 := by
    unfold dl
    exact add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hK1 (Nat.cast_nonneg _)) (sq_nonneg _)) hlog)
      (mul_nonneg (mul_nonneg hK2 (Nat.cast_nonneg _)) (sq_nonneg _))
  unfold g0
  refine (sub_le_self _ hdl).trans ?_
  rw [sum_tops_on_orbit X hsg ht0 (orbLoc E p h u i (false, t0) Th).TT (mem_top_orbit_set_iff E p h u i (false, t0) Th)]
  refine Finset.sum_le_sum fun s hs => ?_
  have hs' : IsTopPl D (orbMap D p (false, t0) s) := (mem_top_orbit_set_iff E p h u i (false, t0) Th s).1 hs
  set t := (orbMap D p (false, t0) s).2 with ht
  have hom : orbMap D p (false, t0) s = (false, t) := Prod.ext hs'.1 rfl
  have htT : t ∈ D.host.TT := hs'.2
  have hpart : ∀ e : ℕ, orbMap D p (false, t0) (s + (e : ZMod (nP D p))) = partner D p t e := by
    intro e; rw [orbit_map_add_natCast, hom, positionPlace_conjugate_partner]
  have hpart1 : ∀ e, Odd e → (partner D p t e).1 = true := by
    intro e he
    show decide (IsSg D p ∧ Odd e) = true
    exact decide_eq_true ⟨hsg, he⟩
  have hExcl : ∀ e, Odd e → ¬ Excl D p t e := by
    rintro e he ⟨_, s', _, _, hd⟩
    have h2 := congrArg Prod.fst hd.2.1
    rw [hpart1 e he] at h2
    exact Bool.noConfusion h2
  have hdTop : (orbLoc E p h u i (false, t0) Th).dTop s = ⊤ := by
    unfold Formalism.MainNotions.product_zeroth_first_parts.Loc.dTop
    refine top_unique (le_iInf₂ fun e he => ?_)
    exfalso
    have hT0 := (mem_top_orbit_set_iff E p h u i (false, t0) Th _).1 he.2
    have hT : IsTopPl D (partner D p t e) := by rw [← hpart e]; exact hT0
    have h2 := hT.1
    rw [hpart1 e he.1] at h2
    exact Bool.noConfusion h2
  unfold Formalism.MainNotions.product_zeroth_first_parts.Loc.baseTerm
  rw [hdTop]
  have hl : ((orbLoc E p h u i (false, t0) Th).l : ℝ) = (p : ℝ) := rfl
  apply tsum_le_tsum_of_nonneg_le
  · intro e
    split_ifs
    · exact le_max_left _ _
    · exact le_refl 0
  · intro e
    by_cases he : Odd e
    · have hne : (e : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top e
      rw [if_pos ⟨he, hExcl e he⟩, if_pos ⟨he, hne⟩, max_comm]
      refine max_le_max ?_ le_rfl
      have hal := hS.alG u i hi t htT
      have hcap := hS.capG u i hi (orbMap D p (false, t0) (s + (e : ZMod (nP D p))))
      rw [← orbit_local_capacity_eq E p h u i (false, t0) Th, hpart] at hcap
      have hpe : (0 : ℝ) < (p : ℝ) ^ e := pow_pos (by linarith) e
      have hrow : ((((orbLoc E p h u i (false, t0) Th).nu s).rowLen 0 : ℕ) : ℝ) -
          ((((orbLoc E p h u i (false, t0) Th).nu s).rowLen 1 : ℕ) : ℝ) =
          E.row u i (false, t) 0 - E.row u i (false, t) 1 := by
        rw [← hom]; rfl
      rw [hl, hrow]
      unfold capU
      exact sub_le_sub (div_le_div_of_nonneg_right hal hpe.le) hcap
    · rw [if_neg (fun h' => he h'.1), if_neg (fun h' => he h'.1)]
  · exact summable_truncated_geometric _ _ (by rw [hl]; exact hp1) _ (fun e => Nat.cast_nonneg _) _

end PI.OrbBoundFW
