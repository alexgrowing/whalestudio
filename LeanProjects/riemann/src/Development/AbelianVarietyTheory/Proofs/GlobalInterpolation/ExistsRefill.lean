import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.Refill

open Formalism.MainNotions.G

theorem bsH_orb {φ : Formalism.HC.Frame} (h t : φ.A) : ∃ i : ℕ, Arith.bsH h t + i • h = t := by
  classical
  unfold Arith.bsH
  split_ifs with hex
  · exact Nat.find_spec hex
  · exact ⟨0, by simp⟩

theorem bsH_step {φ : Formalism.HC.Frame} (h t : φ.A) : Arith.bsH h (t + h) = Arith.bsH h t := by
  classical
  have hiff : ∀ v : ℕ, (∃ i : ℕ, φ.ofNat v + i • h = t + h) ↔ ∃ i : ℕ, φ.ofNat v + i • h = t := by
    intro v
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i + (addOrderOf h - 1), ?_⟩
      have h1 : (addOrderOf h - 1) • h + h = 0 := by
        rw [← succ_nsmul, Nat.sub_add_cancel (addOrderOf_pos h), addOrderOf_nsmul_eq_zero]
      rw [add_nsmul, ← add_assoc, hi, add_assoc, add_comm h, h1, add_zero]
    · rintro ⟨i, hi⟩
      exact ⟨i + 1, by rw [succ_nsmul, ← add_assoc, hi]⟩
  have hex : ∃ v : ℕ, ∃ i : ℕ, φ.ofNat v + i • h = t := ⟨t.val, 0, by simp⟩
  have hex' : ∃ v : ℕ, ∃ i : ℕ, φ.ofNat v + i • h = t + h := ⟨(t + h).val, 0, by simp⟩
  unfold Arith.bsH
  rw [dif_pos hex, dif_pos hex']
  congr 1
  exact Nat.find_congr' (fun {v} => hiff v)

theorem finite_over (D : D7) (p : ℕ) : {w : D.what₂.places.Pl | D.what₂.places.resChar w = p}.Finite := by
  by_cases hp : p = 0
  · refine Set.Finite.subset Set.finite_empty ?_
    intro w hw
    exact absurd (hw.trans hp) (D.what₂.places.resChar_prime w).ne_zero
  have hI : (Ideal.span {(p : 𝓞 D.what₂.LL)} : Ideal (𝓞 D.what₂.LL)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine Set.Finite.subset ((Ideal.finite_factors hI).preimage D.plEq.injective.injOn) ?_
  intro w hw
  have hw' : D.what₂.places.resChar w = p := hw
  have h1 := D.what₂.places.val_resChar w
  have h0 : ((p : ℕ) : D.what₂.LL) ≠ 0 := by exact_mod_cast hp
  rw [hw', D.val_eq w _ h0] at h1
  have h2 : vAdd (D.plEq w) ((p : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by exact_mod_cast h1
  have h3 := D.what₂.places.ramIdx_pos w
  show (D.plEq w).asIdeal ∣ _
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_dvd (K := D.what₂.LL)]
  refine lt_of_le_of_ne (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _) (fun h => ?_)
  unfold vAdd at h2
  have h4 : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL (p : 𝓞 D.what₂.LL)) = ((p : ℕ) : D.what₂.LL) := map_natCast _ _
  have h5 : (D.plEq w).valuation D.what₂.LL ((p : ℕ) : D.what₂.LL) = 1 := h4 ▸ h
  rw [h5, WithZero.log_one] at h2
  omega

theorem finite_le (D : D7) (B : ℕ) : {w : D.what₂.places.Pl | D.what₂.places.resChar w ≤ B}.Finite := by
  refine Set.Finite.subset ((Set.finite_Iic B).biUnion (fun p _ => finite_over D p)) ?_
  intro w hw
  exact Set.mem_biUnion (x := D.what₂.places.resChar w) hw rfl

theorem plGG_inj (D : D7) : Function.Injective (plGG D) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ h
  have h2 : D.R.iota s = D.R.iota t := by
    have := congrArg Prod.snd h
    cases a <;> cases b <;> exact this
  have h3 := D.R.iota_bijective.1 h2
  subst h3
  have h1 := congrArg (fun g => g.1.1) h
  cases a <;> cases b
  · rfl
  · exact absurd h1 (by simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2])
  · exact absurd h1 (by simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2])
  · rfl

theorem eTau_tauPl (D : D7) (z : Bool × HH D) : (D.eTau (tauPl D z) : D.R.GG) = plGG D z := by
  simp [tauPl]

theorem top_iff (D : D7) (z : Bool × HH D) : plGG D z ∈ D.host.topPlaces ↔ IsTopPl D z := by
  classical
  unfold Host.topPlaces IsTopPl
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, ht, h⟩
    have : (false, t) = z := plGG_inj D h
    subst this
    exact ⟨rfl, ht⟩
  · rintro ⟨h1, h2⟩
    refine ⟨z.2, h2, ?_⟩
    simp [plGG, h1]

theorem thick_iff (D : D7) (z : Bool × HH D) : plGG D z ∈ D.host.thickPlaces ↔ IsThickPl D z := by
  classical
  unfold Host.thickPlaces IsThickPl
  rw [Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, h⟩
    have : (true, D.R.dig s + D.host.u0) = z := plGG_inj D h
    subst this
    exact ⟨rfl, s, hs, rfl⟩
  · rintro ⟨h1, s, h2, h3⟩
    refine ⟨s, h2, ?_⟩
    simp [plGG, h1, h3]

variable {D : D7}

open Classical in

def offC (L : SizeData₂ D) (j : ℕ) (z : Bool × HH D) : ℝ :=
  if j ∈ SizeData₂.lifts D then wPl D j z - (if z.1 = false ∧ z.2 ∈ D.host.TT then (bL L z.2 : ℝ) else 0)
  else if IsTopPl D z then L.sc.b' / L.sc.x else if IsThickPl D z then L.sc.b else L.sc.w'' D.R.n

theorem offC_top (L : SizeData₂ D) (j : ℕ) (z : Bool × HH D) (h : IsTopPl D z) :
    L.sc.b' / L.sc.x ≤ offC L j z ∧ offC L j z ≤ L.sc.b' / L.sc.x + L.etaSz := by
  have he := L.etaSz_pos
  unfold offC
  by_cases hj : j ∈ SizeData₂.lifts D
  · have h' : z.1 = false ∧ z.2 ∈ D.host.TT := h
    rw [if_pos hj, if_pos h']
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    have h3 := L.win_top j h1 h2 (tauPl D z) ⟨z.2, h.2⟩ (by rw [eTau_tauPl]; simp [plGG, h.1])
    unfold wPl bL
    rw [dif_pos h.2]
    constructor <;> linarith [h3.1, h3.2]
  · rw [if_neg hj, if_pos h]
    constructor <;> linarith

theorem offC_thick (L : SizeData₂ D) (j : ℕ) (z : Bool × HH D) (h : IsThickPl D z) :
    L.sc.b ≤ offC L j z ∧ offC L j z ≤ L.sc.b + L.etaSz + 1 := by
  have he := L.etaSz_pos
  have hn : ¬ IsTopPl D z := fun h' => by have := h'.1.symm.trans h.1; simp at this
  unfold offC
  by_cases hj : j ∈ SizeData₂.lifts D
  · have h' : ¬ (z.1 = false ∧ z.2 ∈ D.host.TT) := hn
    rw [if_pos hj, if_neg h', sub_zero]
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    exact L.win_thick j h1 h2 (tauPl D z) (by rw [eTau_tauPl, thick_iff]; exact h)
  · rw [if_neg hj, if_neg hn, if_pos h]
    constructor <;> linarith

theorem offC_thin (L : SizeData₂ D) (j : ℕ) (z : Bool × HH D) (h : IsThinPl D z) :
    L.sc.w'' D.R.n ≤ offC L j z ∧ offC L j z ≤ L.sc.w'' D.R.n + L.etaSz := by
  have he := L.etaSz_pos
  unfold offC
  by_cases hj : j ∈ SizeData₂.lifts D
  · have h' : ¬ (z.1 = false ∧ z.2 ∈ D.host.TT) := h.1
    rw [if_pos hj, if_neg h', sub_zero]
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    refine L.win_thin j h1 h2 (tauPl D z) ?_
    rw [eTau_tauPl]
    exact ⟨plGG_mem_Psi D z, by rw [top_iff]; exact h.1, by rw [thick_iff]; exact h.2⟩
  · rw [if_neg hj, if_neg h.1, if_neg h.2]
    constructor <;> linarith

def inst (L : SizeData₂ D) (K : Consts) (Ce : ℝ) : Inst D L where
  bs := Arith.bsH
  bs_orb := bsH_orb
  bs_step := bsH_step
  off := offC L
  off_top := offC_top L
  off_thin := offC_thin L
  off_thick := offC_thick L
  kapI := fun p n' TT a b => sInf (G.kapISet L K p n' TT a b)
  ep := fun p => ⌈Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a⌉₊

theorem inst_canon (L : SizeData₂ D) (K : Consts) (Ce : ℝ) : CanonInst (inst L K Ce) := by
  refine ⟨fun _ _ => rfl, fun j hj t => ?_⟩
  show offC L j (false, t) = _
  unfold offC
  rw [if_neg hj]
  by_cases ht : t ∈ D.host.TT
  · rw [if_pos ht, if_pos (show IsTopPl D (false, t) from ⟨rfl, ht⟩)]
  · rw [if_neg ht, if_neg (show ¬ IsTopPl D (false, t) from fun h => ht h.2),
      if_neg (show ¬ IsThickPl D (false, t) from fun h => by simpa using h.1)]

theorem inst_fill (L : SizeData₂ D) (K : Consts) (Ce : ℝ) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (τ : D.what₂.Tau)
    (z : Bool × HH D) (h : (D.eTau τ : D.R.GG) = plGG D z) : fill (inst L K Ce) (bL L) j z = wj D j τ := by
  have hτ : tauPl D z = τ := by
    unfold tauPl
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext h.symm
  unfold fill
  show _ + offC L j z = _
  unfold offC wPl
  rw [if_pos hj, hτ]
  ring

theorem one_le_fill {L : SizeData₂ D} (X : Inst D L) (hw : 1 ≤ L.sc.w'' D.R.n) (j : ℕ) (z : Bool × HH D) :
    1 ≤ fill X (bL L) j z := by
  have hx := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (by unfold Scale.L; positivity)
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a Scale.X'; positivity
  have hw' : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := div_le_div_of_nonneg_left hb'.le hx0 (by nlinarith)
  unfold fill
  by_cases h1 : IsTopPl D z
  · have h' : z.1 = false ∧ z.2 ∈ D.host.TT := h1
    rw [if_pos h']
    unfold bL
    rw [dif_pos h1.2]
    linarith [(X.off_top j z h1).1, L.bT_ge ⟨z.2, h1.2⟩]
  · have h' : ¬ (z.1 = false ∧ z.2 ∈ D.host.TT) := h1
    rw [if_neg h', zero_add]
    by_cases h2 : IsThickPl D z
    · linarith [(X.off_thick j z h2).1]
    · linarith [(X.off_thin j z ⟨h1, h2⟩).1]

theorem VV_empty {L : SizeData₂ D} (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (h : ¬ Cand D L K p) :
    VV X K a b p = ∅ := by
  unfold VV
  rw [if_neg (fun h' => h h'.1)]

theorem tau_eq_zero_of_not_candidate {L : SizeData₂ D} (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (h : ¬ Cand D L K p) :
    tauP X K a b p = 0 := by
  unfold tauP
  rw [if_pos (VV_empty X K a b p h)]

theorem ioP_eq_zero_of_not_cand {L : SizeData₂ D} (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (h : ¬ Cand D L K p) :
    ioP X K a b p = 0 := by
  unfold ioP
  rw [dif_neg (by rw [VV_empty X K a b p h]; simp)]

theorem TTP_subset {L : SizeData₂ D} (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) :
    TTP X K a b p ⊆ D.host.TT := by
  unfold TTP
  split_ifs
  · exact subset_rfl
  · exact Finset.filter_subset _ _

def Big (L : SizeData₂ D) (S : Finset D.what₂.places.Pl) : Prop :=
  ∀ w, w ∉ S → L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ) ∧
    D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) ∧ D.what₂.places.resChar w ≠ D.host.d ∧
    (∀ u, D.what₂.places.resChar w ≠ (D.mem u).A.T ∧ ¬ D.what₂.places.resChar w ∣ (D.mem u).C.DGam) ∧
    D.what₂.muAt w = D.what₂.mu0

theorem exists_big (L : SizeData₂ D) (hf : {w | D.what₂.muAt w ≠ D.what₂.mu0}.Finite) (hG : ∀ u, 0 < (D.mem u).C.DGam) :
    ∃ S, Big L S := by
  classical
  set B : ℕ := ⌈L.sc.X'' D.R.n⌉₊ + D.host.g 0 + D.host.g 1 + D.host.d + ∑ u, ((D.mem u).A.T + (D.mem u).C.DGam) with hB
  refine ⟨((finite_le D B).union hf).toFinset, fun w hw => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hw
  have h1 : B < D.what₂.places.resChar w := not_le.1 hw.1
  have h2 : D.what₂.muAt w = D.what₂.mu0 := not_not.1 hw.2
  refine ⟨?_, ?_, by omega, fun u => ?_, h2⟩
  · have : ⌈L.sc.X'' D.R.n⌉₊ < D.what₂.places.resChar w := by omega
    exact lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast this)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · have h3 : (D.mem u).A.T + (D.mem u).C.DGam ≤ ∑ u, ((D.mem u).A.T + (D.mem u).C.DGam) :=
      Finset.single_le_sum (f := fun u => (D.mem u).A.T + (D.mem u).C.DGam) (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
    refine ⟨by omega, fun h => ?_⟩
    have := Nat.le_of_dvd (hG u) h
    omega

open Classical in

def refill (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Cr : ℝ) (EX : ErrX D) (c : ErrC) (S : Finset D.what₂.places.Pl)
    (hS : Big L S) (hA : HostArith D.host) (hw : 1 ≤ L.sc.w'' D.R.n) (hX : L.sc.X' ≤ L.sc.X'' D.R.n)
    (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j ∈ SizeData₂.lifts D, Fval L j w = 0) : SizeData₂ D :=
  { L with
    supp := S
    gain := fun j w => if IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w) then
      gainP X K (aL L) (bL L) (D.what₂.places.resChar w) j else 0
    F := fun j w => Fval L j w
    E := fun u j w => Eval L EX K c u j w
    tau := fun w => tauP X K (aL L) (bL L) (D.what₂.places.resChar w)
    io := fun w => ioP X K (aL L) (bL L) (D.what₂.places.resChar w)
    gain_supp := fun j w h => by
      unfold gainP
      rw [if_pos (Or.inr (hS w h).1), ite_self]
    F_supp := fun j w h => FvalP_above L j (hS w h).1 (hS w h).2.1 (hS w h).2.2.1
    E_supp := fun u j w h => Eval_above L EX K c u j w (hS w h).1 ((hS w h).2.2.2.1 u).1 (hS w h).2.1 (hS w h).2.2.1
      ((hS w h).2.2.2.1 u).2
    tau_supp := fun w h => tau_eq_zero_of_not_candidate X K _ _ _ (fun hc => by linarith [hc.2.1, (hS w h).1])
    io_supp := fun w h => ioP_eq_zero_of_not_cand X K _ _ _ (fun hc => by linarith [hc.2.1, (hS w h).1])
    gain_g := fun j w h => by
      have h1 : D.host.cls (D.what₂.places.resChar w) = .splitK := by
        refine hA.2.2.2 _ ?_
        rcases Finset.mem_insert.1 h with h | h
        · rw [h]; exact D.host.g_level 0
        · rw [Finset.mem_singleton.1 h]; exact D.host.g_level 1
      refine if_neg ?_
      rintro (h2 | h2) <;> exact absurd (h1.symm.trans h2) (by decide)
    untwisted := fun w h j h1 h2 => ⟨(L.untwisted w h j h1 h2).1, hu w h j (Finset.mem_Icc.2 ⟨h1, h2⟩)⟩
    not_inert := fun w h1 h2 => ⟨fun j => if_neg (fun h => h.elim h2 h1), tau_eq_zero_of_not_candidate X K _ _ _ (fun hc => h2 hc.2.2.1),
      ioP_eq_zero_of_not_cand X K _ _ _ (fun hc => h2 hc.2.2.1)⟩
    drop := {p | NoGain X K Cr p ∧ ∀ u, p ≠ (D.mem u).A.T}
    drop_alt := fun u h => h.2 u rfl
    F_conj := fun j w => Fval_conj L j w
    F_above := fun j _ h1 h2 h3 => FvalP_above L j h1 h2 h3
    TTw := fun w => Finset.univ.filter (fun t => (t : HH D) ∈ TTP X K (aL L) (bL L) (D.what₂.places.resChar w))
    TTw_full := fun w h => by
      refine Finset.filter_true_of_mem (fun t _ => ?_)
      unfold TTP
      rw [if_pos h]
      exact t.2
    wPart := fun j t p e => fill X (bL L) j (partner D p t e)
    wPart_ge := fun j t p e => one_le_fill X hw j _ }

theorem exists_refill : ∀ (C : FC) (cD ch : ℝ) (D : D7) (L0 : SizeData₂ D) (EX : ErrX D), Std C → Val C cD ch L0 → HostArith D.host → 1 ≤ L0.sc.w'' D.R.n → L0.sc.X' ≤ L0.sc.X'' D.R.n → {w | D.what₂.muAt w ≠ D.what₂.mu0}.Finite → (∀ u, 0 < (D.mem u).C.DGam) → (∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j ∈ SizeData₂.lifts D, Fval L0 j w = 0) → ∃ (L : SizeData₂ D) (X : G.Inst D L), L.sc = L0.sc ∧ L.aT = L0.aT ∧ L.bT = L0.bT ∧ Val C cD ch L ∧ CanonInst X ∧ G.EpDef X C.cX.Ce ∧ G.KapIDef X C.GK ∧ L.FDef ∧ L.EDef EX C.GK C.cX.err ∧ (∀ w, ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n → w ∈ L.supp) ∧ (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → w ∈ L.supp) ∧ (∀ w, G.ParametersFill X C.GK w) ∧ ∀ p : ℕ, p.Prime → (p ∈ L.drop ↔ NoGain X C.GK C.Cr p ∧ ∀ u, p ≠ (D.mem u).A.T) := by
  intro C cD ch D L0 EX _ hV hA hw hX hf hG hu
  obtain ⟨S, hS⟩ := exists_big L0 hf hG
  refine ⟨refill L0 (inst L0 C.GK C.cX.Ce) C.GK C.Cr EX C.cX.err S hS hA hw hX hu, inst _ C.GK C.cX.Ce, rfl, rfl, rfl,
    ⟨hV.ranks, hV.host, hV.hc, hV.dlog, hV.Del_eq, hV.eta_eq, hV.La_eq, hV.bT_le, hV.logFiveDepth_eq, hV.Ct_eq, hV.Cc_eq,
      hV.CGam_eq, hV.secondConstant_eq, hV.words, hV.etaF_eq⟩, inst_canon _ _ _, fun _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun w h => ?_, fun w h => ?_, fun w => ?_, fun p _ => Iff.rfl⟩
  · by_contra h'
    exact absurd (hS w h').1 (not_lt.2 h)
  · by_contra h'
    exact h (hS w h').2.2.2.2
  · refine ⟨fun j hj τ z h => inst_fill _ _ _ j hj τ z h, fun _ _ _ => rfl, ?_, fun _ h j _ => if_pos h, rfl, rfl,
      hV.La_eq.symm⟩
    show Finset.map _ (Finset.filter _ _) = TTP (inst L0 C.GK C.cX.Ce) C.GK (aL L0) (bL L0) (D.what₂.places.resChar w)
    ext t
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro ht
      exact ⟨⟨t, TTP_subset _ _ _ _ _ ht⟩, ht, rfl⟩

end GlobalTheory.Refill

end
