import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

noncomputable section
namespace GlobalTheory.LvT.LevModel
open Formalism.BasicNotions Classical

def ratInt (q : ℕ) [Fact q.Prime] : Subring ℚ := (PadicInt.subring q).comap (Rat.castHom ℚ_[q])

lemma mem_ratInt {q : ℕ} [Fact q.Prime] (x : ℚ) : x ∈ ratInt q ↔ ‖(x : ℚ_[q])‖ ≤ 1 := by
  exact Iff.rfl

def toZp (q : ℕ) [Fact q.Prime] : ratInt q →+* ℤ_[q] :=
  ((Rat.castHom ℚ_[q]).comp (ratInt q).subtype).codRestrict (PadicInt.subring q) (fun x => x.2)

lemma toZp_coe {q : ℕ} [Fact q.Prime] (x : ratInt q) : ((toZp q x : ℤ_[q]) : ℚ_[q]) = ((x : ℚ) : ℚ_[q]) := rfl

def ratLoc (q : ℕ) [hq : Fact q.Prime] (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = q) : LocF q F where
  K := ℚ
  O := ratInt q
  frac x := by
    rw [mem_ratInt, mem_ratInt]
    by_cases h : ‖(x : ℚ_[q])‖ ≤ 1
    · exact Or.inl h
    · right
      push_cast
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h))
  q_ne := by exact_mod_cast hq.out.ne_zero
  sep x hx := by
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
    have hx' : (x : ℚ_[q]) ≠ 0 := by exact_mod_cast hx
    have hn : ‖((x * (q : ℚ) ^ (-(x : ℚ_[q]).valuation) : ℚ) : ℚ_[q])‖ = 1 := by
      push_cast
      rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hx', neg_neg,
        ← zpow_add₀ (by exact_mod_cast hq.out.ne_zero)]
      simp
    refine ⟨(x : ℚ_[q]).valuation, x * (q : ℚ) ^ (-(x : ℚ_[q]).valuation), ?_, ?_, ?_⟩
    · rw [mem_ratInt, hn]
    · rw [mem_ratInt, Rat.cast_inv, norm_inv, hn]; simp
    · rw [zpow_neg]; field_simp
  res := (ZMod.ringEquivOfPrime F hq.out hF).toRingHom.comp ((PadicInt.toZMod (p := q)).comp (toZp q))
  res_surj := by
    intro a
    obtain ⟨b, rfl⟩ := (ZMod.ringEquivOfPrime F hq.out hF).surjective a
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective b
    exact ⟨n, by simp⟩
  res_ker x := by
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
    have h1 : ((ZMod.ringEquivOfPrime F hq.out hF).toRingHom.comp ((PadicInt.toZMod (p := q)).comp (toZp q))) x = 0 ↔
        toZp q x ∈ RingHom.ker (PadicInt.toZMod (p := q)) := by
      simp [RingHom.mem_ker]
    rw [h1, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      have h2 : ((x : ℚ) : ℚ_[q]) = (q : ℚ_[q]) * (c : ℚ_[q]) := by
        rw [← toZp_coe, hc]; simp
      refine ⟨⟨(x : ℚ) / q, ?_⟩, by field_simp⟩
      rw [mem_ratInt]
      have hq1 : (q : ℚ_[q]) ≠ 0 := by exact_mod_cast hq.out.ne_zero
      push_cast
      rw [h2, mul_div_cancel_left₀ _ hq1]
      exact c.2
    · rintro ⟨y, hy⟩
      refine ⟨toZp q y, ?_⟩
      apply Subtype.ext
      rw [toZp_coe, hy]; simp [toZp_coe]

section Pairs

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

lemma mem_std (x : Fin n → Lc.K) : x ∈ Lc.std n ↔ ∀ a, x a ∈ Lc.O := by
  simp only [LocF.std, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.2

def stdPair (Lc : LocF q F) (a : Fin n) : LocF.PP Lc n :=
  ⟨⟨Lc.std n, fun x => if h : x ∈ Lc.std n then Lc.res ⟨x a, (mem_std x).1 h a⟩ else 0⟩,
   { lat := ⟨1, fun x => by simp⟩
     add := fun x hx y hy => by
       dsimp only at hx hy ⊢
       rw [dif_pos hx, dif_pos hy, dif_pos ((Lc.std n).add_mem hx hy), ← map_add]; rfl
     smul := fun c x hx => by
       dsimp only at hx ⊢
       rw [dif_pos hx, dif_pos ((Lc.std n).smul_mem c hx), ← map_mul]; rfl
     off := fun x hx => dif_neg hx
     ne := by
       have h : (fun _ => 1 : Fin n → Lc.K) ∈ Lc.std n := (mem_std _).2 fun _ => Lc.O.one_mem
       refine ⟨fun _ => 1, ?_⟩
       dsimp only
       rw [dif_pos h]
       exact (map_one Lc.res).trans_ne one_ne_zero }⟩

def mvO (g : GL (Fin n) Lc.K) : (Fin n → Lc.K) →ₗ[Lc.O] (Fin n → Lc.K) :=
  (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) Lc.K)).restrictScalars Lc.O

lemma inv_mv (g : GL (Fin n) Lc.K) (x : Fin n → Lc.K) :
    mvO g⁻¹ (Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) x) = x := by
  show Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K)
    (Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) x) = x
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

def actPP (g : GL (Fin n) Lc.K) (p : LocF.PP Lc n) : LocF.PP Lc n :=
  ⟨⟨p.1.L.comap (mvO g⁻¹), fun x => p.1.f (mvO g⁻¹ x)⟩,
   { lat := by
       obtain ⟨h, hh⟩ := p.2.lat
       refine ⟨g * h, fun x => ?_⟩
       rw [← hh x, Units.val_mul, ← Matrix.mulVec_mulVec]
       show mvO g⁻¹ _ ∈ p.1.L ↔ _
       rw [inv_mv]
     add := fun x hx y hy => by
       show p.1.f (mvO g⁻¹ (x + y)) = _
       rw [map_add]; exact p.2.add _ hx _ hy
     smul := fun c x hx => by
       show p.1.f (mvO g⁻¹ (c • x)) = _
       rw [map_smul]; exact p.2.smul c _ hx
     off := fun x hx => p.2.off _ hx
     ne := by
       obtain ⟨x, hx⟩ := p.2.ne
       refine ⟨Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) x, ?_⟩
       show p.1.f (mvO g⁻¹ _) ≠ 0
       rwa [inv_mv] }⟩

theorem isAct_actPP (g : GL (Fin n) Lc.K) (p : LocF.PP Lc n) : LocF.PP.IsAct g p (actPP g p) := by
  intro x
  refine ⟨?_, ?_⟩
  · show mvO g⁻¹ _ ∈ p.1.L ↔ _
    rw [inv_mv]
  · show p.1.f (mvO g⁻¹ _) = _
    rw [inv_mv]

private lemma mulVec_mvO_inv (g : GL (Fin n) Lc.K) (y : Fin n → Lc.K) :
    Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) (mvO g⁻¹ y) = y := by
  show Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K)
    (Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) y) = y
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem isAct_unique {g : GL (Fin n) Lc.K} {p p₁ p₂ : LocF.PP Lc n} (h₁ : LocF.PP.IsAct g p p₁)
    (h₂ : LocF.PP.IsAct g p p₂) : p₁ = p₂ := by
  apply Subtype.ext
  apply LocF.Raw.ext
  · ext y
    rw [← mulVec_mvO_inv g y, (h₁ _).1, (h₂ _).1]
  · funext y
    rw [← mulVec_mvO_inv g y, (h₁ _).2, (h₂ _).2]

theorem exists_dil (a : Fˣ) (p : LocF.PP Lc n) : ∃ p', LocF.PP.IsDil (a : F) p p' := by
  refine ⟨⟨⟨p.1.L, fun x => (a : F) * p.1.f x⟩,
    { lat := p.2.lat
      add := fun x hx y hy => by
        show (a : F) * p.1.f (x + y) = (a : F) * p.1.f x + (a : F) * p.1.f y
        rw [p.2.add x hx y hy, mul_add]
      smul := fun c x hx => by
        show (a : F) * p.1.f (c • x) = Lc.res c * ((a : F) * p.1.f x)
        rw [p.2.smul c x hx, mul_left_comm]
      off := fun x hx => by
        show (a : F) * p.1.f x = 0
        rw [p.2.off x hx, mul_zero]
      ne := by
        obtain ⟨x, hx⟩ := p.2.ne
        exact ⟨x, mul_ne_zero a.ne_zero hx⟩ }⟩, rfl, fun x => rfl⟩

lemma q_inv_not_mem (Lc : LocF q F) : ((q : Lc.K))⁻¹ ∉ Lc.O := by
  intro h
  have h1 : Lc.res 1 = 0 := (Lc.res_ker 1).2 ⟨⟨_, h⟩, by
    show (1 : Lc.K) = (q : Lc.K) * (q : Lc.K)⁻¹
    rw [mul_inv_cancel₀ Lc.q_ne]⟩
  rw [map_one] at h1
  exact one_ne_zero h1

def dq (Lc : LocF q F) (a : Fin n) : GL (Fin n) Lc.K :=
  diagGL Lc.K n fun b => if b = a then (Units.mk0 (q : Lc.K) Lc.q_ne)⁻¹ else 1

lemma dq_inv_mv (a : Fin n) (x : Fin n → Lc.K) (b : Fin n) :
    mvO (dq Lc a)⁻¹ x b = if b = a then (q : Lc.K) * x b else x b := by
  show Matrix.mulVec (Matrix.diagonal fun c =>
    (((if c = a then (Units.mk0 (q : Lc.K) Lc.q_ne)⁻¹ else 1 : Lc.Kˣ)⁻¹ : Lc.Kˣ) : Lc.K)) x b = _
  rw [Matrix.mulVec_diagonal]
  split_ifs with h
  · simp
  · simp

private lemma stdPair_f_apply (a : Fin n) {x : Fin n → Lc.K} (h : x ∈ Lc.std n) :
    (stdPair Lc a).1.f x = Lc.res ⟨x a, (mem_std x).1 h a⟩ := by
  unfold stdPair
  exact dif_pos h

theorem inc_std (a : Fin n) : (stdPair Lc a).Inc (actPP (dq Lc a) (stdPair Lc a)) := by
  have hq : (q : Lc.K) ≠ 0 := Lc.q_ne
  have hqO : (q : Lc.K) ∈ Lc.O := natCast_mem Lc.O q
  have he : (Pi.single a 1 : Fin n → Lc.K) ∈ Lc.std n := (mem_std _).2 fun b => by
    by_cases hb : b = a
    · subst hb
      rw [Pi.single_eq_same]
      exact Lc.O.one_mem
    · rw [Pi.single_eq_of_ne hb]
      exact Lc.O.zero_mem
  have hfe : (stdPair Lc a).1.f (Pi.single a 1) = 1 := by
    rw [stdPair_f_apply a he]
    have h1 : (⟨(Pi.single a (1 : Lc.K) : Fin n → Lc.K) a, (mem_std _).1 he a⟩ : Lc.O) = 1 :=
      Subtype.ext (by simp)
    rw [h1, map_one]
  refine ⟨Pi.single a 1, hfe, he, ?_, ?_⟩
  · ext y
    have hz : ∀ b, mvO (dq Lc a)⁻¹ y b = if b = a then (q : Lc.K) * y b else y b :=
      fun b => dq_inv_mv a y b
    change mvO (dq Lc a)⁻¹ y ∈ Lc.std n ∧ (stdPair Lc a).1.f (mvO (dq Lc a)⁻¹ y) = 0 ↔ y ∈ Lc.std n
    constructor
    · rintro ⟨hL, hf⟩
      rw [stdPair_f_apply a hL] at hf
      obtain ⟨w, hw⟩ := (Lc.res_ker _).1 hf
      refine (mem_std y).2 fun b => ?_
      by_cases hb : b = a
      · rw [hb]
        have h0 : mvO (dq Lc a)⁻¹ y a = (q : Lc.K) * w := hw
        rw [hz, if_pos rfl] at h0
        rw [mul_left_cancel₀ hq h0]
        exact w.2
      · have h2 := (mem_std _).1 hL b
        rwa [hz, if_neg hb] at h2
    · intro hy
      have hy' := (mem_std y).1 hy
      have hL : mvO (dq Lc a)⁻¹ y ∈ Lc.std n := (mem_std _).2 fun b => by
        rw [hz]
        split_ifs
        · exact Lc.O.mul_mem hqO (hy' b)
        · exact hy' b
      refine ⟨hL, ?_⟩
      rw [stdPair_f_apply a hL]
      exact (Lc.res_ker _).2 ⟨⟨y a, hy' a⟩, by
        show mvO (dq Lc a)⁻¹ y a = (q : Lc.K) * y a
        rw [hz, if_pos rfl]⟩
  · have hz2 : mvO (dq Lc a)⁻¹ (((q : Lc.K))⁻¹ • (Pi.single a 1 : Fin n → Lc.K)) = Pi.single a 1 := by
      funext b
      rw [dq_inv_mv]
      by_cases hb : b = a
      · subst hb
        simp [hq]
      · simp [hb]
    show (stdPair Lc a).1.f (mvO (dq Lc a)⁻¹ (((q : Lc.K))⁻¹ • (Pi.single a 1 : Fin n → Lc.K))) = 1
    rw [hz2]
    exact hfe

private lemma iter_mvO_dq_inv_apply (a : Fin n) (k : ℕ) (y : Fin n → Lc.K) (b : Fin n) :
    (⇑(mvO (dq Lc a)⁻¹))^[k] y b = if b = a then (q : Lc.K) ^ k * y b else y b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', dq_inv_mv, ih]
    split_ifs <;> ring

private lemma mem_iter_actPP_stdPair_iff (a : Fin n) (k : ℕ) (y : Fin n → Lc.K) :
    y ∈ ((actPP (dq Lc a))^[k] (stdPair Lc a)).1.L ↔ (⇑(mvO (dq Lc a)⁻¹))^[k] y ∈ Lc.std n := by
  induction k generalizing y with
  | zero => exact Iff.rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply' (actPP (dq Lc a)), Function.iterate_succ_apply]
    exact ih _

theorem infinite_PP (Lc : LocF q F) (a : Fin n) : Infinite (LocF.PP Lc n) := by
  have hq : (q : Lc.K) ≠ 0 := Lc.q_ne
  have hqO : (q : Lc.K) ∈ Lc.O := natCast_mem Lc.O q
  have key : ∀ j k, (((q : Lc.K))⁻¹ ^ k • (Pi.single a 1 : Fin n → Lc.K)) ∈
      ((actPP (dq Lc a))^[j] (stdPair Lc a)).1.L ↔ (q : Lc.K) ^ j * ((q : Lc.K))⁻¹ ^ k ∈ Lc.O := by
    intro j k
    rw [mem_iter_actPP_stdPair_iff, mem_std]
    simp only [iter_mvO_dq_inv_apply]
    constructor
    · intro h
      simpa using h a
    · intro h b
      by_cases hb : b = a
      · subst hb
        simpa using h
      · simp [hb]
  have hA : ∀ k, (((q : Lc.K))⁻¹ ^ k • (Pi.single a 1 : Fin n → Lc.K)) ∈
      ((actPP (dq Lc a))^[k] (stdPair Lc a)).1.L := fun k => by
    rw [key, ← mul_pow, mul_inv_cancel₀ hq, one_pow]
    exact Lc.O.one_mem
  have hpow : ∀ m, ((q : Lc.K))⁻¹ ^ (m + 1) ∉ Lc.O := fun m hm => q_inv_not_mem Lc (by
    have h2 : ((q : Lc.K))⁻¹ ^ (m + 1) * (q : Lc.K) ^ m = ((q : Lc.K))⁻¹ := by
      rw [pow_succ, mul_comm (((q : Lc.K))⁻¹ ^ m), mul_assoc, ← mul_pow, inv_mul_cancel₀ hq,
        one_pow, mul_one]
    rw [← h2]
    exact Lc.O.mul_mem hm (Lc.O.pow_mem hqO m))
  have hB : ∀ j m, (((q : Lc.K))⁻¹ ^ (j + m + 1) • (Pi.single a 1 : Fin n → Lc.K)) ∉
      ((actPP (dq Lc a))^[j] (stdPair Lc a)).1.L := fun j m h => by
    rw [key, show j + m + 1 = j + (m + 1) by omega, pow_add, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hq, one_pow, one_mul] at h
    exact hpow m h
  refine Infinite.of_injective (fun k : ℕ => (actPP (dq Lc a))^[k] (stdPair Lc a)) ?_
  intro j k hjk
  have hjk' : (actPP (dq Lc a))^[j] (stdPair Lc a) = (actPP (dq Lc a))^[k] (stdPair Lc a) := hjk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h3 := hA (j + m + 1)
    rw [← hjk'] at h3
    exact hB j m h3
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h3 := hA (k + m + 1)
    rw [hjk'] at h3
    exact hB k m h3

end Pairs

variable {D : D7} {u : D.what₂.Word}

theorem infinite_group {X : Ch D u} {i : ℕ} (M : PtModel X i) (c : X.C.cls i) (v : X.A.vT) : Infinite M.G := by
  have : Infinite (LocF.PP (M.Lc v) (D.R.N i)) := infinite_PP (M.Lc v)
    ⟨0, lt_of_lt_of_le (by have := D.R.m_add_three_le_k; omega : 0 < D.R.k) (Nat.le_add_right _ _)⟩
  have : Infinite M.Pt := Infinite.of_injective
    (fun x : LocF.PP (M.Lc v) (D.R.N i) => ((M.rep c).1, Function.update (M.rep c).2 v x)) (by
      intro x y hxy
      have h2 := congrArg (fun p : M.Pt => p.2 v) hxy
      simpa using h2)
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have : Finite M.Pt := Finite.of_surjective (fun cg : X.C.cls i × M.G => cg.2 • M.rep cg.1) (by
    intro p
    obtain ⟨c', g, h⟩ := M.rep_surj p
    exact ⟨(c', g), h⟩)
  exact not_finite M.Pt

def emptyModel (X : Ch D u) (i : ℕ) [IsEmpty (X.C.cls i)] : PtModel X i :=
  haveI : Fact X.A.T.Prime := ⟨X.A.T_prime⟩
  { Lc := fun v => ratLoc X.A.T (X.A.Fv v) (X.A.card_Fv v)
    G := PUnit
    Z := PEmpty
    actP := { smul := fun _ p => p, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl }
    loc := fun _ => 1
    smul_fst := fun _ p => p.1.elim
    smul_snd := fun _ p => p.1.elim
    rep := fun c => isEmptyElim c
    rep_surj := fun p => p.1.elim
    rep_inj := fun c => isEmptyElim c
    card_stab := fun c => isEmptyElim c
    Val := ⊥
    act := 1
    H := 0
    H_act := fun _ _ _ => rfl
    H_pos := fun y hy => absurd (Subsingleton.elim y 0) hy
    H_symm := fun _ _ => by simp
    ipV_eq := fun c => isEmptyElim c
    mem_Fi := fun φ => ⟨fun _ c => isEmptyElim c, fun _ => by rw [Subsingleton.elim φ 0]; exact zero_mem _⟩
    piL := fun _ c => isEmptyElim c
    piL_add := fun _ c => isEmptyElim c
    piL_smul := fun _ c => isEmptyElim c
    piL_surj := fun _ c => isEmptyElim c
    piL_f := fun _ c => isEmptyElim c
    piK := fun _ c => isEmptyElim c
    piK_add := fun _ c => isEmptyElim c
    piK_smul := fun _ c => isEmptyElim c
    piK_surj := fun _ c => isEmptyElim c
    piK_te := fun _ c => isEmptyElim c
    up_eq := fun _ c => isEmptyElim c
    dn_eq := fun _ c => isEmptyElim c
    dil_eq := fun _ c => isEmptyElim c }

theorem empty_kernels (X : Ch D u) [∀ i, IsEmpty (X.C.cls i)] :
    ∃ (Lv : LevTie X) (Kt : KerTie Lv), ∀ i h, (Kt i h).TgtEq ∧ (Kt i h).DilLaw ∧ (Kt i h).UKLaw := by
  refine ⟨fun i _ => emptyModel X i, fun i h =>
    { k := fun _ _ => 0
      src := fun _ _ _ _ => rfl
      Kmap_eq := fun c _ _ => isEmptyElim c }, fun i h => ⟨?_, ?_, ?_⟩⟩
  · intro g' p p' y
    exact (p.1 : PEmpty).elim
  · intro v a p q' p' q'' _ _
    rfl
  · intro v p p' y
    exact (p.1 : PEmpty).elim

end GlobalTheory.LvT.LevModel
