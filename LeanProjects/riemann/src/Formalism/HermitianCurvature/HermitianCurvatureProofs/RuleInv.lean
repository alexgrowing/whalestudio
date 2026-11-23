import Formalism.HermitianCurvature.StatementR

namespace Formalism.FourierDecayAlt.R.PInv

open Matrix LevelData

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem comm_mat_prod (x : A) :
    ∀ l : List (Matrix (Fin 2) (Fin 2) A), (∀ M ∈ l, ∀ i j, Commute x (M i j)) →
      ∀ i j, Commute x (l.prod i j)
  | [], _ => by
      intro i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | M :: l, h => by
      intro i j
      rw [List.prod_cons, Matrix.mul_apply]
      exact Commute.sum_right _ _ _ fun k _ =>
        (h M (by simp) i k).mul_right (comm_mat_prod x l (fun N hN => h N (by simp [hN])) k j)

theorem prod_mul_prod_eq_one : ∀ (n : ℕ) (f g : Fin n → A), (∀ i, f i * g i = 1) →
    (∀ i j, Commute (f i) (g j)) → (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h1, hc => by
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
      have hP : Commute (List.ofFn fun i => f i.succ).prod (g 0) :=
        Commute.list_prod_left _ _ (by
          intro a ha
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
          exact hc _ _)
      have ih := prod_mul_prod_eq_one n (fun i => f i.succ) (fun i => g i.succ)
        (fun i => h1 _) (fun i j => hc _ _)
      calc f 0 * (List.ofFn fun i => f i.succ).prod * (g 0 * (List.ofFn fun i => g i.succ).prod)
          = f 0 * ((List.ofFn fun i => f i.succ).prod * g 0) * (List.ofFn fun i => g i.succ).prod := by
            noncomm_ring
        _ = f 0 * g 0 * ((List.ofFn fun i => f i.succ).prod * (List.ofFn fun i => g i.succ).prod) := by
            rw [hP.eq]; noncomm_ring
        _ = 1 := by rw [h1, ih, one_mul]

variable {r : ℕ} (L : LevelData A r)

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_fcomm {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : Commute x y :=
  L.fns_comm x hx y hy

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_cb (l) : L.cb l ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_cbi (l) : L.cbi l ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_c (l) : L.c l ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ci (l) : L.ci l ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ζ : L.ζ ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ζi : L.ζi ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ζb : L.ζb ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ζbi : L.ζbi ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_GG : L.GG ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_GGi : L.GGi ∈ L.fns := by simp [LevelData.fns]

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_comm_ofFn {x : A} {f : Fin r → A} (h : ∀ i, Commute x (f i)) :
    Commute x (List.ofFn f).prod :=
  Commute.list_prod_right _ _ (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact h i)

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_comm_Tprod {x : A} (hp : ∀ l, Commute x (L.p l)) (hc : ∀ l, Commute x (L.c l))
    (hci : ∀ l, Commute x (L.ci l)) (Y : ℂ) (i j) : Commute x (L.Tprod Y i j) := by
  apply comm_mat_prod
  intro M hM
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hM)
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [LevelData.Tl, (hp l).add_left, Algebra.commutes, hc l, hci l, Commute.neg_right,
      Commute.add_right, Commute.zero_right]
  exact Commute.add_right (Algebra.commute_algebraMap_right Y x) (hp l)

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_comm_Tvprod {x : A} (hp : ∀ l, Commute x (L.pb l)) (hc : ∀ l, Commute x (L.cb l))
    (hci : ∀ l, Commute x (L.cbi l)) (Y : ℂ) (i j) : Commute x (L.Tvprod Y i j) := by
  apply comm_mat_prod
  intro M hM
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hM)
  intro i j
  fin_cases i <;> fin_cases j <;> simp [LevelData.Tvl, hc l, hci l]
  exact Commute.sub_right (Algebra.commute_algebraMap_right Y x) (hp l)

theorem comm_alg (x : A) (y : ℂ) : Commute x (algebraMap ℂ A y) := Algebra.commute_algebraMap_right y x

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_S_mem {x : A} (hx : x ∈ L.fns) : x ∈ Algebra.adjoin ℂ L.fns := Algebra.subset_adjoin hx

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_S_prod {f : Fin r → A} (hf : ∀ i, f i ∈ L.fns) :
    (List.ofFn f).prod ∈ Algebra.adjoin ℂ L.fns :=
  Subalgebra.list_prod_mem _ (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact L.inv_S_mem (hf i))

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_Drbi_Drb : L.Drbi * L.Drb = 1 :=
  prod_mul_prod_eq_one r L.cbi L.cb L.cbi_cb (fun i j => L.inv_fcomm (L.inv_mem_cbi i) (L.inv_mem_cb j))
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_Drb_Drbi : L.Drb * L.Drbi = 1 :=
  prod_mul_prod_eq_one r L.cb L.cbi L.cb_cbi (fun i j => L.inv_fcomm (L.inv_mem_cb i) (L.inv_mem_cbi j))
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_Dri_Dr : L.Dri * L.Dr = 1 :=
  prod_mul_prod_eq_one r L.ci L.c L.ci_c (fun i j => L.inv_fcomm (L.inv_mem_ci i) (L.inv_mem_c j))
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_Dr_Dri : L.Dr * L.Dri = 1 :=
  prod_mul_prod_eq_one r L.c L.ci L.c_ci (fun i j => L.inv_fcomm (L.inv_mem_c i) (L.inv_mem_ci j))

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_hR_bar (Y : ℂ) :
    L.G * L.Dbi * L.Dbi * L.Ahatv Y = L.Dr * L.GG * (L.ζbi * L.ζbi * L.Avr Y) := by
  letI : CommRing (Algebra.adjoin ℂ L.fns) := Algebra.adjoinCommRingOfComm ℂ L.fns_comm
  let Dr' : Algebra.adjoin ℂ L.fns := ⟨L.Dr, L.inv_S_prod L.inv_mem_c⟩
  let Drb' : Algebra.adjoin ℂ L.fns := ⟨L.Drb, L.inv_S_prod L.inv_mem_cb⟩
  let Drbi' : Algebra.adjoin ℂ L.fns := ⟨L.Drbi, L.inv_S_prod L.inv_mem_cbi⟩
  let GG' : Algebra.adjoin ℂ L.fns := ⟨L.GG, L.inv_S_mem L.inv_mem_GG⟩
  let z' : Algebra.adjoin ℂ L.fns := ⟨L.ζbi, L.inv_S_mem L.inv_mem_ζbi⟩
  have h1 : Drb' * Drbi' = 1 := Subtype.ext L.inv_Drb_Drbi
  have hS : Dr' * Drb' * GG' * (z' * Drbi') * (z' * Drbi') * Drb' = Dr' * GG' * (z' * z') := by
    linear_combination (Dr' * GG' * z' * z' * (Drb' * Drbi' + 1)) * h1
  have hA := congrArg Subtype.val hS
  simp only [LevelData.G, LevelData.Dbi, LevelData.Ahatv]
  calc L.Dr * L.Drb * L.GG * (L.ζbi * L.Drbi) * (L.ζbi * L.Drbi) * (L.Drb * L.Avr Y)
      = (L.Dr * L.Drb * L.GG * (L.ζbi * L.Drbi) * (L.ζbi * L.Drbi) * L.Drb) * L.Avr Y := by
        noncomm_ring
    _ = (L.Dr * L.GG * (L.ζbi * L.ζbi)) * L.Avr Y := by rw [show L.Dr * L.Drb * L.GG * (L.ζbi * L.Drbi) * (L.ζbi * L.Drbi) * L.Drb = L.Dr * L.GG * (L.ζbi * L.ζbi) from hA]
    _ = L.Dr * L.GG * (L.ζbi * L.ζbi * L.Avr Y) := by noncomm_ring

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_hR_hol (Y : ℂ) :
    L.G * L.Di * L.Di * L.Ahat Y = L.Drb * L.GG * (L.ζi * L.ζi * L.Ar Y) := by
  letI : CommRing (Algebra.adjoin ℂ L.fns) := Algebra.adjoinCommRingOfComm ℂ L.fns_comm
  let Dr' : Algebra.adjoin ℂ L.fns := ⟨L.Dr, L.inv_S_prod L.inv_mem_c⟩
  let Drb' : Algebra.adjoin ℂ L.fns := ⟨L.Drb, L.inv_S_prod L.inv_mem_cb⟩
  let Dri' : Algebra.adjoin ℂ L.fns := ⟨L.Dri, L.inv_S_prod L.inv_mem_ci⟩
  let GG' : Algebra.adjoin ℂ L.fns := ⟨L.GG, L.inv_S_mem L.inv_mem_GG⟩
  let z' : Algebra.adjoin ℂ L.fns := ⟨L.ζi, L.inv_S_mem L.inv_mem_ζi⟩
  have h1 : Dr' * Dri' = 1 := Subtype.ext L.inv_Dr_Dri
  have hS : Dr' * Drb' * GG' * (z' * Dri') * (z' * Dri') * Dr' = Drb' * GG' * (z' * z') := by
    linear_combination (Drb' * GG' * z' * z' * (Dr' * Dri' + 1)) * h1
  have hA := congrArg Subtype.val hS
  simp only [LevelData.G, LevelData.Di, LevelData.Ahat]
  calc L.Dr * L.Drb * L.GG * (L.ζi * L.Dri) * (L.ζi * L.Dri) * (L.Dr * L.Ar Y)
      = (L.Dr * L.Drb * L.GG * (L.ζi * L.Dri) * (L.ζi * L.Dri) * L.Dr) * L.Ar Y := by
        noncomm_ring
    _ = (L.Drb * L.GG * (L.ζi * L.ζi)) * L.Ar Y := by rw [show L.Dr * L.Drb * L.GG * (L.ζi * L.Dri) * (L.ζi * L.Dri) * L.Dr = L.Drb * L.GG * (L.ζi * L.ζi) from hA]
    _ = L.Drb * L.GG * (L.ζi * L.ζi * L.Ar Y) := by noncomm_ring

theorem ruleInv : RuleInv := by
  intro A _ _ r L Y

  have zb_p : ∀ l, Commute L.ζbi (L.p l) := fun l => (L.p_ζbi l).symm
  have zb_pb : ∀ l, Commute L.ζbi (L.pb l) := fun l => (L.pb_ζbi l).symm
  have z_p : ∀ l, Commute L.ζi (L.p l) := fun l => (L.p_ζi l).symm
  have z_pb : ∀ l, Commute L.ζi (L.pb l) := fun l => (L.pb_ζi l).symm
  have fc := fun {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) => L.inv_fcomm hx hy
  have zbAr : ∀ i j, Commute L.ζbi (L.Tprod Y i j) :=
    L.inv_comm_Tprod zb_p (fun l => fc L.inv_mem_ζbi (L.inv_mem_c l)) (fun l => fc L.inv_mem_ζbi (L.inv_mem_ci l)) Y
  have zbAv : ∀ i j, Commute L.ζbi (L.Tvprod Y i j) :=
    L.inv_comm_Tvprod zb_pb (fun l => fc L.inv_mem_ζbi (L.inv_mem_cb l)) (fun l => fc L.inv_mem_ζbi (L.inv_mem_cbi l)) Y
  have zAr : ∀ i j, Commute L.ζi (L.Tprod Y i j) :=
    L.inv_comm_Tprod z_p (fun l => fc L.inv_mem_ζi (L.inv_mem_c l)) (fun l => fc L.inv_mem_ζi (L.inv_mem_ci l)) Y
  have zAv : ∀ i j, Commute L.ζi (L.Tvprod Y i j) :=
    L.inv_comm_Tvprod z_pb (fun l => fc L.inv_mem_ζi (L.inv_mem_cb l)) (fun l => fc L.inv_mem_ζi (L.inv_mem_cbi l)) Y
  have zbDr : Commute L.ζbi L.Dr := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζbi (L.inv_mem_c l)
  have zbDrb : Commute L.ζbi L.Drb := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζbi (L.inv_mem_cb l)
  have zDr : Commute L.ζi L.Dr := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζi (L.inv_mem_c l)
  have zDrb : Commute L.ζi L.Drb := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζi (L.inv_mem_cb l)
  have zbGG : Commute L.ζbi L.GG := fc L.inv_mem_ζbi L.inv_mem_GG
  have zGG : Commute L.ζi L.GG := fc L.inv_mem_ζi L.inv_mem_GG
  have zb_l0 : Commute L.ζbi (L.l0 Y) := by
    simp only [LevelData.l0]
    exact ((show Commute L.ζbi L.nab from L.nab_ζbi.symm).neg_right).sub_right ((comm_alg _ _).mul_right
      ((fc L.inv_mem_ζbi L.inv_mem_ζb).mul_right (fc L.inv_mem_ζbi L.inv_mem_GGi)))
  have z_m0 : Commute L.ζi (L.m0 Y) := by
    simp only [LevelData.m0]
    exact ((show Commute L.ζi L.nabs from L.nabs_ζi.symm).neg_right).sub_right ((comm_alg _ _).mul_right
      ((fc L.inv_mem_ζi L.inv_mem_ζ).mul_right (fc L.inv_mem_ζi L.inv_mem_GGi)))
  have hm : L.m0 Y * L.ζbi = L.ζbi * L.m0 Y - L.ζbi * L.ζbi := by
    have hX : Commute L.ζbi (algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)) :=
      (comm_alg _ _).mul_right ((fc L.inv_mem_ζbi L.inv_mem_ζ).mul_right (fc L.inv_mem_ζbi L.inv_mem_GGi))
    simp only [LevelData.m0]
    calc (-L.nabs - algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)) * L.ζbi
        = -(L.nabs * L.ζbi) - algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi) * L.ζbi := by noncomm_ring
      _ = -(L.ζbi * L.nabs + L.ζbi * L.ζbi) - L.ζbi * (algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)) := by
          rw [L.nabs_ζbi, hX.eq]
      _ = _ := by noncomm_ring
  have hl : L.l0 Y * L.ζi = L.ζi * L.l0 Y + L.ζi * L.ζi := by
    have hX : Commute L.ζi (algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)) :=
      (comm_alg _ _).mul_right ((fc L.inv_mem_ζi L.inv_mem_ζb).mul_right (fc L.inv_mem_ζi L.inv_mem_GGi))
    simp only [LevelData.l0]
    calc (-L.nab - algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)) * L.ζi
        = -(L.nab * L.ζi) - algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi) * L.ζi := by noncomm_ring
      _ = -(L.ζi * L.nab - L.ζi * L.ζi) - L.ζi * (algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)) := by
          rw [L.nab_ζi, hX.eq]
      _ = _ := by noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (zbDr.mul_right (zbAr 0 0)).eq
  · exact ((zbDrb.mul_right zbGG).mul_right ((zb_l0.mul_right (zbAr 0 0)).add_right (zbAr 1 0))).eq
  · exact (zbDrb.mul_right (zbAv 0 0)).eq
  · rw [inv_hR_bar]
    have e1 : (L.m0 Y * L.Avr Y + L.Bvr Y) * L.ζbi
        = (L.ζbi * L.m0 Y - L.ζbi * L.ζbi) * L.Avr Y + L.ζbi * L.Bvr Y := by
      have hA1 : Commute L.ζbi (L.Avr Y) := zbAv 0 0
      have hB1 : Commute L.ζbi (L.Bvr Y) := zbAv 1 0
      rw [add_mul, mul_assoc, ← hA1.eq, ← mul_assoc, hm, ← hB1.eq]
    have hDG : Commute L.ζbi (L.Dr * L.GG) := zbDr.mul_right zbGG
    simp only [LevelData.R0v]
    calc L.Dr * L.GG * (L.m0 Y * L.Avr Y + L.Bvr Y) * L.ζbi - L.ζbi * (L.Dr * L.GG * (L.m0 Y * L.Avr Y + L.Bvr Y))
        = L.Dr * L.GG * ((L.m0 Y * L.Avr Y + L.Bvr Y) * L.ζbi) - (L.ζbi * (L.Dr * L.GG)) * (L.m0 Y * L.Avr Y + L.Bvr Y) := by
          noncomm_ring
      _ = L.Dr * L.GG * ((L.ζbi * L.m0 Y - L.ζbi * L.ζbi) * L.Avr Y + L.ζbi * L.Bvr Y) - (L.Dr * L.GG * L.ζbi) * (L.m0 Y * L.Avr Y + L.Bvr Y) := by
          rw [e1, hDG.eq]
      _ = _ := by noncomm_ring
  · exact (zDr.mul_right (zAr 0 0)).eq
  · exact (zDrb.mul_right (zAv 0 0)).eq
  · exact ((zDr.mul_right zGG).mul_right ((z_m0.mul_right (zAv 0 0)).add_right (zAv 1 0))).eq
  · rw [inv_hR_hol]
    have e1 : (L.l0 Y * L.Ar Y + L.Br Y) * L.ζi
        = (L.ζi * L.l0 Y + L.ζi * L.ζi) * L.Ar Y + L.ζi * L.Br Y := by
      have hA1 : Commute L.ζi (L.Ar Y) := zAr 0 0
      have hB1 : Commute L.ζi (L.Br Y) := zAr 1 0
      rw [add_mul, mul_assoc, ← hA1.eq, ← mul_assoc, hl, ← hB1.eq]
    have hDG : Commute L.ζi (L.Drb * L.GG) := zDrb.mul_right zGG
    simp only [LevelData.R0]
    calc L.Drb * L.GG * (L.l0 Y * L.Ar Y + L.Br Y) * L.ζi - L.ζi * (L.Drb * L.GG * (L.l0 Y * L.Ar Y + L.Br Y))
        = L.Drb * L.GG * ((L.l0 Y * L.Ar Y + L.Br Y) * L.ζi) - (L.ζi * (L.Drb * L.GG)) * (L.l0 Y * L.Ar Y + L.Br Y) := by
          noncomm_ring
      _ = L.Drb * L.GG * ((L.ζi * L.l0 Y + L.ζi * L.ζi) * L.Ar Y + L.ζi * L.Br Y) - (L.Drb * L.GG * L.ζi) * (L.l0 Y * L.Ar Y + L.Br Y) := by
          rw [e1, hDG.eq]
      _ = _ := by noncomm_ring

end Formalism.FourierDecayAlt.R.PInv

theorem Formalism.FourierDecayAlt.P.inverseCommutators : Formalism.FourierDecayAlt.R.RuleInv := Formalism.FourierDecayAlt.R.PInv.ruleInv
