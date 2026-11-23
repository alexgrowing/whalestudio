import Formalism.HermitianCurvature.StatementR

namespace Formalism.FourierDecayAlt.P.RuleSS

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem I_mul {h a a' b b' : A} (ha : a * h = h * a') (hb : b * h = h * b') :
    a * b * h = h * (a' * b') := by
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

theorem I_add {h a a' b b' : A} (ha : a * h = h * a') (hb : b * h = h * b') :
    (a + b) * h = h * (a' + b') := by
  rw [add_mul, ha, hb, mul_add]

theorem I_comp {h k a a' a'' : A} (h1 : a * h = h * a') (h2 : a' * k = k * a'') :
    a * (h * k) = (h * k) * a'' := by
  rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem I_of_comm {h a : A} (hc : Commute a h) : a * h = h * a := hc.eq

theorem rev_prod_inter {M : Type} [Monoid M] (d : M) :
    ∀ (n : ℕ) (f g : Fin n → M), (∀ i, f i * d = d * g i) →
      (List.ofFn f).reverse.prod * d = d * (List.ofFn g).reverse.prod
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
      rw [List.ofFn_succ, List.ofFn_succ, List.reverse_cons, List.reverse_cons, List.prod_append,
        List.prod_append, List.prod_singleton, List.prod_singleton, mul_assoc, h 0, ← mul_assoc,
        rev_prod_inter d n (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ), mul_assoc]

theorem ofFn_shift (x : A) :
    ∀ (n : ℕ) (f : Fin n → A) (k : Fin n → ℂ), (∀ m, x * f m = f m * (x + algebraMap ℂ A (k m))) →
      x * (List.ofFn f).prod = (List.ofFn f).prod * (x + algebraMap ℂ A (∑ m, k m))
  | 0, _, _, _ => by simp
  | n + 1, f, k, h => by
      have ih := ofFn_shift x n (fun i => f i.succ) (fun i => k i.succ) (fun i => h i.succ)
      rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, map_add]
      set P := (List.ofFn fun i => f i.succ).prod
      calc x * (f 0 * P) = (x * f 0) * P := by noncomm_ring
        _ = f 0 * (x * P + algebraMap ℂ A (k 0) * P) := by rw [h 0]; noncomm_ring
        _ = f 0 * (P * (x + algebraMap ℂ A (∑ i : Fin n, k i.succ)) + P * algebraMap ℂ A (k 0)) := by
            rw [ih, Algebra.commutes]
        _ = _ := by noncomm_ring

theorem add_shift {x h : A} {s : ℂ} (hx : x * h = h * (x + algebraMap ℂ A s)) (Y Y' : ℂ)
    (hY : Y' = Y + s) : (algebraMap ℂ A Y + x) * h = h * (algebraMap ℂ A Y' + x) := by
  rw [add_mul, hx, Algebra.commutes Y h, hY, map_add]; noncomm_ring

theorem sub_shift {x h : A} {s : ℂ} (hx : x * h = h * (x + algebraMap ℂ A s)) (Y Y' : ℂ)
    (hY : Y' = Y - s) : (algebraMap ℂ A Y - x) * h = h * (algebraMap ℂ A Y' - x) := by
  rw [sub_mul, hx, Algebra.commutes Y h, hY, map_sub]; noncomm_ring

theorem add_comm0 {x h : A} (hx : Commute x h) (Y : ℂ) :
    (algebraMap ℂ A Y + x) * h = h * (algebraMap ℂ A Y + x) :=
  ((Algebra.commute_algebraMap_left Y h).add_left hx).eq

theorem sub_comm0 {x h : A} (hx : Commute x h) (Y : ℂ) :
    (algebraMap ℂ A Y - x) * h = h * (algebraMap ℂ A Y - x) :=
  ((Algebra.commute_algebraMap_left Y h).sub_left hx).eq

variable {r : ℕ} (L : LevelData A r)

theorem Ar_inter (h : A) (Y Y' : ℂ)
    (hp : ∀ l, (algebraMap ℂ A Y + L.p l) * h = h * (algebraMap ℂ A Y' + L.p l))
    (hc : ∀ l, L.c l * h = h * L.c l) (hci : ∀ l, L.ci l * h = h * L.ci l) :
    L.Ar Y * h = h * L.Ar Y' ∧ L.Br Y * h = h * L.Br Y' := by
  have key : L.Tprod Y * diagonal (fun _ : Fin 2 => h) = diagonal (fun _ => h) * L.Tprod Y' := by
    unfold LevelData.Tprod
    apply rev_prod_inter
    intro l
    ext i j
    rw [mul_diagonal, diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [LevelData.Tl, hp l, hc l, hci l]
  have k00 := congrFun (congrFun key 0) 0
  have k10 := congrFun (congrFun key 1) 0
  rw [mul_diagonal, diagonal_mul] at k00 k10
  exact ⟨k00, k10⟩

theorem Avr_inter (h : A) (Y Y' : ℂ)
    (hp : ∀ l, (algebraMap ℂ A Y - L.pb l) * h = h * (algebraMap ℂ A Y' - L.pb l))
    (hc : ∀ l, L.cb l * h = h * L.cb l) (hci : ∀ l, L.cbi l * h = h * L.cbi l) :
    L.Avr Y * h = h * L.Avr Y' ∧ L.Bvr Y * h = h * L.Bvr Y' := by
  have key : L.Tvprod Y * diagonal (fun _ : Fin 2 => h) = diagonal (fun _ => h) * L.Tvprod Y' := by
    unfold LevelData.Tvprod
    apply rev_prod_inter
    intro l
    ext i j
    rw [mul_diagonal, diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [LevelData.Tvl, hp l, hc l, hci l]
  have k00 := congrFun (congrFun key 0) 0
  have k10 := congrFun (congrFun key 1) 0
  rw [mul_diagonal, diagonal_mul] at k00 k10
  exact ⟨k00, k10⟩

theorem fcomm {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : Commute x y := L.fns_comm x hx y hy

theorem mem_c (l) : L.c l ∈ L.fns := by simp [LevelData.fns]
theorem mem_ci (l) : L.ci l ∈ L.fns := by simp [LevelData.fns]
theorem mem_cb (l) : L.cb l ∈ L.fns := by simp [LevelData.fns]
theorem mem_cbi (l) : L.cbi l ∈ L.fns := by simp [LevelData.fns]
theorem mem_ζ : L.ζ ∈ L.fns := by simp [LevelData.fns]
theorem mem_ζb : L.ζb ∈ L.fns := by simp [LevelData.fns]
theorem mem_GG : L.GG ∈ L.fns := by simp [LevelData.fns]
theorem mem_GGi : L.GGi ∈ L.fns := by simp [LevelData.fns]

omit [Algebra ℂ A] in
theorem comm_ofFn {n : ℕ} {x : A} {f : Fin n → A} (h : ∀ i, Commute x (f i)) :
    Commute x (List.ofFn f).prod :=
  Commute.list_prod_right _ _ (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact h i)

theorem comm_fns_D {x : A} (hx : x ∈ L.fns) :
    Commute x L.Dr ∧ Commute x L.Dri ∧ Commute x L.Drb ∧ Commute x L.Drbi :=
  ⟨comm_ofFn fun m => fcomm L hx (mem_c L m), comm_ofFn fun m => fcomm L hx (mem_ci L m),
    comm_ofFn fun m => fcomm L hx (mem_cb L m), comm_ofFn fun m => fcomm L hx (mem_cbi L m)⟩

theorem p_Dr (l) : L.p l * L.Dr = L.Dr * (L.p l + algebraMap ℂ A 1) := by
  have h := ofFn_shift (L.p l) r L.c (fun m => if l = m then 1 else 0) (fun m => by
    rw [L.p_c]; split_ifs <;> simp [mul_add])
  rw [show (∑ m : Fin r, if l = m then (1:ℂ) else 0) = 1 by simp] at h
  exact h

theorem p_Dri (l) : L.p l * L.Dri = L.Dri * (L.p l + algebraMap ℂ A (-1)) := by
  have h := ofFn_shift (L.p l) r L.ci (fun m => if l = m then -1 else 0) (fun m => by
    rw [L.p_ci]; split_ifs <;> simp [mul_add, sub_eq_add_neg])
  rw [show (∑ m : Fin r, if l = m then (-1:ℂ) else 0) = -1 by simp] at h
  exact h

theorem pb_Drb (l) : L.pb l * L.Drb = L.Drb * (L.pb l + algebraMap ℂ A 1) := by
  have h := ofFn_shift (L.pb l) r L.cb (fun m => if l = m then 1 else 0) (fun m => by
    rw [L.pb_cb]; split_ifs <;> simp [mul_add])
  rw [show (∑ m : Fin r, if l = m then (1:ℂ) else 0) = 1 by simp] at h
  exact h

theorem pb_Drbi (l) : L.pb l * L.Drbi = L.Drbi * (L.pb l + algebraMap ℂ A (-1)) := by
  have h := ofFn_shift (L.pb l) r L.cbi (fun m => if l = m then -1 else 0) (fun m => by
    rw [L.pb_cbi]; split_ifs <;> simp [mul_add, sub_eq_add_neg])
  rw [show (∑ m : Fin r, if l = m then (-1:ℂ) else 0) = -1 by simp] at h
  exact h

theorem leftCorrection_intertwine {h : A} (hn : Commute L.nab h) (hz : Commute L.ζb h) (hg : Commute L.GGi h) (Y : ℂ) :
    L.l0 Y * h = h * L.l0 Y := by
  unfold LevelData.l0
  exact ((hn.neg_left).sub_left ((Algebra.commute_algebraMap_left _ h).mul_left (hz.mul_left hg))).eq

theorem dualCorrection_intertwine {h : A} (hn : Commute L.nabs h) (hz : Commute L.ζ h) (hg : Commute L.GGi h) (Y : ℂ) :
    L.m0 Y * h = h * L.m0 Y := by
  unfold LevelData.m0
  exact ((hn.neg_left).sub_left ((Algebra.commute_algebraMap_left _ h).mul_left (hz.mul_left hg))).eq

omit L in
theorem lin_shift (n z S : A) (c c' e : ℂ) (hn : n * S = S * n + algebraMap ℂ A e * (z * S))
    (hz : z * S = S * z) (hc : c' = c + e) :
    (-n - algebraMap ℂ A c * z) * S = S * (-n - algebraMap ℂ A c' * z) := by
  calc (-n - algebraMap ℂ A c * z) * S = -(n * S) - algebraMap ℂ A c * (z * S) := by noncomm_ring
    _ = -(S * n + algebraMap ℂ A e * (S * z)) - algebraMap ℂ A c * (S * z) := by rw [hn, hz]
    _ = -(S * n) - (algebraMap ℂ A e * S) * z - (algebraMap ℂ A c * S) * z := by noncomm_ring
    _ = -(S * n) - (S * algebraMap ℂ A e) * z - (S * algebraMap ℂ A c) * z := by
        rw [Algebra.commutes e S, Algebra.commutes c S]
    _ = S * (-n - algebraMap ℂ A (c + e) * z) := by rw [map_add]; noncomm_ring
    _ = _ := by rw [hc]

theorem four_inter (h : A) (Ya Y1 Yl Yl' Yv Yv' Ym Ym' : ℂ)
    (hA : L.Ar Ya * h = h * L.Ar Y1) (hB : L.Br Ya * h = h * L.Br Y1)
    (hl : L.l0 Yl * h = h * L.l0 Yl')
    (hAv : L.Avr Yv * h = h * L.Avr Yv') (hBv : L.Bvr Yv * h = h * L.Bvr Yv')
    (hm : L.m0 Ym * h = h * L.m0 Ym')
    (hDr : Commute L.Dr h) (hDrb : Commute L.Drb h) (hGG : Commute L.GG h) :
    L.Dr * L.Ar Ya * h = h * (L.Dr * L.Ar Y1) ∧
    L.Drb * L.GG * (L.l0 Yl * L.Ar Ya + L.Br Ya) * h = h * (L.Drb * L.GG * (L.l0 Yl' * L.Ar Y1 + L.Br Y1)) ∧
    L.Drb * L.Avr Yv * h = h * (L.Drb * L.Avr Yv') ∧
    L.Dr * L.GG * (L.m0 Ym * L.Avr Yv + L.Bvr Yv) * h = h * (L.Dr * L.GG * (L.m0 Ym' * L.Avr Yv' + L.Bvr Yv')) :=
  ⟨I_mul hDr.eq hA, I_mul (I_mul hDrb.eq hGG.eq) (I_add (I_mul hl hA) hB), I_mul hDrb.eq hAv,
    I_mul (I_mul hDr.eq hGG.eq) (I_add (I_mul hm hAv) hBv)⟩

theorem _root_.Formalism.FourierDecayAlt.P.intertwinerConjugation : Formalism.FourierDecayAlt.R.RuleSS := by
  intro A _ _ r L SS SSs hSf hSp hSpb hSn hSns hTf hTp hTpb hTn hTns Y
  have DD : ∀ {x : A}, x ∈ L.fns → Commute x L.Dr ∧ Commute x L.Dri ∧ Commute x L.Drb ∧ Commute x L.Drbi :=
    fun hx => comm_fns_D L hx

  have cDrDrb : Commute L.Dr L.Drb := (comm_ofFn fun m => ((DD (mem_c L m)).2.2.1).symm).symm
  have cDrDri : Commute L.Dr L.Dri := (comm_ofFn fun m => ((DD (mem_c L m)).2.1).symm).symm
  have cDrDrbi : Commute L.Dr L.Drbi := (comm_ofFn fun m => ((DD (mem_c L m)).2.2.2).symm).symm
  have cDrbDri : Commute L.Drb L.Dri := (comm_ofFn fun m => ((DD (mem_cb L m)).2.1).symm).symm
  have cDrbDrbi : Commute L.Drb L.Drbi := (comm_ofFn fun m => ((DD (mem_cb L m)).2.2.2).symm).symm

  have sDrb := four_inter L L.Drb Y Y Y Y Y (Y - 1) Y Y
    (Ar_inter L _ Y Y (fun l => add_comm0 (comm_ofFn fun m => L.p_cb l m) Y)
      (fun l => (DD (mem_c L l)).2.2.1.eq) (fun l => (DD (mem_ci L l)).2.2.1.eq)).1
    (Ar_inter L _ Y Y (fun l => add_comm0 (comm_ofFn fun m => L.p_cb l m) Y)
      (fun l => (DD (mem_c L l)).2.2.1.eq) (fun l => (DD (mem_ci L l)).2.2.1.eq)).2
    (leftCorrection_intertwine L (comm_ofFn fun m => L.nab_cb m) (DD (mem_ζb L)).2.2.1 (DD (mem_GGi L)).2.2.1 Y)
    (Avr_inter L _ Y (Y - 1) (fun l => sub_shift (pb_Drb L l) Y (Y - 1) rfl)
      (fun l => (DD (mem_cb L l)).2.2.1.eq) (fun l => (DD (mem_cbi L l)).2.2.1.eq)).1
    (Avr_inter L _ Y (Y - 1) (fun l => sub_shift (pb_Drb L l) Y (Y - 1) rfl)
      (fun l => (DD (mem_cb L l)).2.2.1.eq) (fun l => (DD (mem_cbi L l)).2.2.1.eq)).2
    (dualCorrection_intertwine L (comm_ofFn fun m => L.nabs_cb m) (DD (mem_ζ L)).2.2.1 (DD (mem_GGi L)).2.2.1 Y)
    cDrDrb (Commute.refl _) (DD (mem_GG L)).2.2.1

  have sDri := four_inter L L.Dri Y (Y - 1) Y Y (Y - 1) (Y - 1) Y Y
    (Ar_inter L _ Y (Y - 1) (fun l => add_shift (p_Dri L l) Y (Y - 1) (by ring))
      (fun l => (DD (mem_c L l)).2.1.eq) (fun l => (DD (mem_ci L l)).2.1.eq)).1
    (Ar_inter L _ Y (Y - 1) (fun l => add_shift (p_Dri L l) Y (Y - 1) (by ring))
      (fun l => (DD (mem_c L l)).2.1.eq) (fun l => (DD (mem_ci L l)).2.1.eq)).2
    (leftCorrection_intertwine L (comm_ofFn fun m => L.nab_ci m) (DD (mem_ζb L)).2.1 (DD (mem_GGi L)).2.1 Y)
    (Avr_inter L _ (Y - 1) (Y - 1) (fun l => sub_comm0 (comm_ofFn fun m => L.pb_ci l m) _)
      (fun l => (DD (mem_cb L l)).2.1.eq) (fun l => (DD (mem_cbi L l)).2.1.eq)).1
    (Avr_inter L _ (Y - 1) (Y - 1) (fun l => sub_comm0 (comm_ofFn fun m => L.pb_ci l m) _)
      (fun l => (DD (mem_cb L l)).2.1.eq) (fun l => (DD (mem_cbi L l)).2.1.eq)).2
    (dualCorrection_intertwine L (comm_ofFn fun m => L.nabs_ci m) (DD (mem_ζ L)).2.1 (DD (mem_GGi L)).2.1 Y)
    cDrDri cDrbDri (DD (mem_GG L)).2.1

  have hlS : L.l0 Y * SS = SS * L.l0 (Y - 1) := by
    unfold LevelData.l0
    exact lin_shift _ _ _ (Y + 1/2) (Y - 1 + 1/2) (-1)
      (by rw [hSn, map_neg, map_one, neg_one_mul, sub_eq_add_neg])
      (Commute.mul_left (hSf _ (mem_ζb L)) (hSf _ (mem_GGi L))).eq (by ring)
  have hmS : L.m0 Y * SS = SS * L.m0 (Y - 1) := by
    unfold LevelData.m0
    exact lin_shift _ _ _ (Y - 1/2) (Y - 1 - 1/2) (-1)
      (by rw [hSns, map_neg, map_one, neg_one_mul, sub_eq_add_neg])
      (Commute.mul_left (hSf _ (mem_ζ L)) (hSf _ (mem_GGi L))).eq (by ring)
  have sSS := four_inter L SS (Y - 1) (Y - 1) Y (Y - 1) (Y - 1) (Y - 1) Y (Y - 1)
    (Ar_inter L SS (Y - 1) (Y - 1) (fun l => add_comm0 (hSp l) _)
      (fun l => hSf _ (mem_c L l)) (fun l => hSf _ (mem_ci L l))).1
    (Ar_inter L SS (Y - 1) (Y - 1) (fun l => add_comm0 (hSp l) _)
      (fun l => hSf _ (mem_c L l)) (fun l => hSf _ (mem_ci L l))).2
    hlS
    (Avr_inter L SS (Y - 1) (Y - 1) (fun l => sub_comm0 (hSpb l) _)
      (fun l => hSf _ (mem_cb L l)) (fun l => hSf _ (mem_cbi L l))).1
    (Avr_inter L SS (Y - 1) (Y - 1) (fun l => sub_comm0 (hSpb l) _)
      (fun l => hSf _ (mem_cb L l)) (fun l => hSf _ (mem_cbi L l))).2
    hmS
    (comm_ofFn fun m => (hSf _ (mem_c L m)).symm).symm
    (comm_ofFn fun m => (hSf _ (mem_cb L m)).symm).symm (hSf _ (mem_GG L))

  have hlT : L.l0 Y * SSs = SSs * L.l0 (Y + 1) := by
    unfold LevelData.l0
    exact lin_shift _ _ _ (Y + 1/2) (Y + 1 + 1/2) 1
      (by rw [hTn, map_one, one_mul])
      (Commute.mul_left (hTf _ (mem_ζb L)) (hTf _ (mem_GGi L))).eq (by ring)
  have hmT : L.m0 Y * SSs = SSs * L.m0 (Y + 1) := by
    unfold LevelData.m0
    exact lin_shift _ _ _ (Y - 1/2) (Y + 1 - 1/2) 1
      (by rw [hTns, map_one, one_mul])
      (Commute.mul_left (hTf _ (mem_ζ L)) (hTf _ (mem_GGi L))).eq (by ring)
  have sSSs := four_inter L SSs Y Y Y (Y + 1) Y Y Y (Y + 1)
    (Ar_inter L SSs Y Y (fun l => add_comm0 (hTp l) _)
      (fun l => hTf _ (mem_c L l)) (fun l => hTf _ (mem_ci L l))).1
    (Ar_inter L SSs Y Y (fun l => add_comm0 (hTp l) _)
      (fun l => hTf _ (mem_c L l)) (fun l => hTf _ (mem_ci L l))).2
    hlT
    (Avr_inter L SSs Y Y (fun l => sub_comm0 (hTpb l) _)
      (fun l => hTf _ (mem_cb L l)) (fun l => hTf _ (mem_cbi L l))).1
    (Avr_inter L SSs Y Y (fun l => sub_comm0 (hTpb l) _)
      (fun l => hTf _ (mem_cb L l)) (fun l => hTf _ (mem_cbi L l))).2
    hmT
    (comm_ofFn fun m => (hTf _ (mem_c L m)).symm).symm
    (comm_ofFn fun m => (hTf _ (mem_cb L m)).symm).symm (hTf _ (mem_GG L))

  have sDr := four_inter L L.Dr Y (Y + 1) (Y + 1) (Y + 1) Y Y (Y + 1) (Y + 1)
    (Ar_inter L _ Y (Y + 1) (fun l => add_shift (p_Dr L l) Y (Y + 1) rfl)
      (fun l => (DD (mem_c L l)).1.eq) (fun l => (DD (mem_ci L l)).1.eq)).1
    (Ar_inter L _ Y (Y + 1) (fun l => add_shift (p_Dr L l) Y (Y + 1) rfl)
      (fun l => (DD (mem_c L l)).1.eq) (fun l => (DD (mem_ci L l)).1.eq)).2
    (leftCorrection_intertwine L (comm_ofFn fun m => L.nab_c m) (DD (mem_ζb L)).1 (DD (mem_GGi L)).1 (Y + 1))
    (Avr_inter L _ Y Y (fun l => sub_comm0 (comm_ofFn fun m => L.pb_c l m) _)
      (fun l => (DD (mem_cb L l)).1.eq) (fun l => (DD (mem_cbi L l)).1.eq)).1
    (Avr_inter L _ Y Y (fun l => sub_comm0 (comm_ofFn fun m => L.pb_c l m) _)
      (fun l => (DD (mem_cb L l)).1.eq) (fun l => (DD (mem_cbi L l)).1.eq)).2
    (dualCorrection_intertwine L (comm_ofFn fun m => L.nabs_c m) (DD (mem_ζ L)).1 (DD (mem_GGi L)).1 (Y + 1))
    (Commute.refl _) cDrDrb.symm (DD (mem_GG L)).1

  have sDrbi := four_inter L L.Drbi (Y + 1) (Y + 1) (Y + 1) (Y + 1) Y (Y + 1) (Y + 1) (Y + 1)
    (Ar_inter L _ (Y + 1) (Y + 1) (fun l => add_comm0 (comm_ofFn fun m => L.p_cbi l m) _)
      (fun l => (DD (mem_c L l)).2.2.2.eq) (fun l => (DD (mem_ci L l)).2.2.2.eq)).1
    (Ar_inter L _ (Y + 1) (Y + 1) (fun l => add_comm0 (comm_ofFn fun m => L.p_cbi l m) _)
      (fun l => (DD (mem_c L l)).2.2.2.eq) (fun l => (DD (mem_ci L l)).2.2.2.eq)).2
    (leftCorrection_intertwine L (comm_ofFn fun m => L.nab_cbi m) (DD (mem_ζb L)).2.2.2 (DD (mem_GGi L)).2.2.2 (Y + 1))
    (Avr_inter L _ Y (Y + 1) (fun l => sub_shift (pb_Drbi L l) Y (Y + 1) (by ring))
      (fun l => (DD (mem_cb L l)).2.2.2.eq) (fun l => (DD (mem_cbi L l)).2.2.2.eq)).1
    (Avr_inter L _ Y (Y + 1) (fun l => sub_shift (pb_Drbi L l) Y (Y + 1) (by ring))
      (fun l => (DD (mem_cb L l)).2.2.2.eq) (fun l => (DD (mem_cbi L l)).2.2.2.eq)).2
    (dualCorrection_intertwine L (comm_ofFn fun m => L.nabs_cbi m) (DD (mem_ζ L)).2.2.2 (DD (mem_GGi L)).2.2.2 (Y + 1))
    cDrDrbi cDrbDrbi (DD (mem_GG L)).2.2.2
  obtain ⟨a1, b1, c1, d1⟩ := sDrb
  obtain ⟨a2, b2, c2, d2⟩ := sDri
  obtain ⟨a3, b3, c3, d3⟩ := sSS
  obtain ⟨a4, b4, c4, d4⟩ := sSSs
  obtain ⟨a5, b5, c5, d5⟩ := sDr
  obtain ⟨a6, b6, c6, d6⟩ := sDrbi
  exact ⟨I_comp (I_comp a1 a2) a3, I_comp (I_comp b1 b2) b3, I_comp (I_comp c1 c2) c3,
    I_comp (I_comp d1 d2) d3, I_comp a4 (I_comp a5 a6), I_comp b4 (I_comp b5 b6),
    I_comp c4 (I_comp c5 c6), I_comp d4 (I_comp d5 d6)⟩

end Formalism.FourierDecayAlt.P.RuleSS
