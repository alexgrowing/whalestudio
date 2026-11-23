import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefTraceCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NotCdomRaiseOfLt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommonEigenvectors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProductIntervalFrames
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.Qx8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frameG_exists {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ g : Mx k r, g ∈ UH (Hpk k r) ∧
      (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
      g *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) = z := by
  set s : ℝ := Real.sqrt (Tz k r z) with hs
  have hss : (s : ℂ) * (s : ℂ) = ((Tz k r z : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hs, Real.mul_self_sqrt hT.le]
  set a : Fin (2 * r + k + 1) → ℂ := (s : ℂ) • bvec (wI k r (Fin.last k)) with ha
  have haW : inWb k r a := by
    intro i hi
    rw [ha, Pi.smul_apply, inWb_bvec_wI _ i hi, smul_zero]
  have haa : herm (Hpk k r) a a = ((-(Tz k r z) : ℝ) : ℂ) := by
    rw [ha, herm_smul_left', herm_smul_right', herm_wI, if_pos rfl, if_pos rfl]
    have : star (s : ℂ) = s := Complex.conj_ofReal s
    rw [this]
    push_cast
    linear_combination -hss
  have hzz : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := by
    rw [TwoByOneBlock.herm_self_eq]; push_cast; rfl
  obtain ⟨g, hgU, hga, hfix⟩ := TwoByOneBlock.trans (Hpk k r) hpk_herm a z (-(Tz k r z)) (by linarith [hT]) haa hzz
  have horth : ∀ (w : Fin (2 * r + k + 1) → ℂ), inWb k r w → ∀ c : Fin r,
      herm (Hpk k r) (bvec (eI k r c)) w = 0 ∧ herm (Hpk k r) (bvec (esI k r c)) w = 0 := by
    intro w hw c
    rw [inWb_iff] at hw
    rw [herm_bvec_left, hpk_e, dot_bvec, herm_bvec_left, hpk_es, dot_bvec, Pi.star_apply, Pi.star_apply, (hw c).1,
      (hw c).2]
    simp
  exact ⟨g, hgU, fun c => ⟨hfix _ (horth a haW c).1 (horth z hz c).1, hfix _ (horth a haW c).2 (horth z hz c).2⟩, hga⟩

end Formalism.FourierDecayAlt.P.Qx8

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GTRIntPf

theorem u_step (P : M.Par) (hOK : P.OK) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ P.k - 1) : P.u (i + 1) + 1 ≤ P.u i := by
  have hg := hOK.gap i (Finset.mem_Icc.2 ⟨h1, h2⟩)
  unfold M.Par.lo M.Par.hi at hg
  have e1 := le_max_left (P.u (i + 1)) (P.u' (i + 1))
  have e2 := min_le_left (P.u i) (P.u' i)
  linarith

theorem u_mono (P : M.Par) (hOK : P.OK) (a : ℕ) (ha : 1 ≤ a) :
    ∀ d : ℕ, a + d ≤ P.k → P.u (a + d) + d ≤ P.u a := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 := u_step P hOK (a + d) (by omega) (by omega)
    rw [show a + (d + 1) = a + d + 1 by omega]
    push_cast
    linarith

theorem u_int (P : M.Par) (hOK : P.OK) (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ P.k) : ∃ n : ℤ, P.u i - P.u 1 = n :=
  hOK.int_u i (Finset.mem_Icc.2 ⟨hi, hik⟩)

theorem sum_int {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, ∃ n : ℤ, f i = n) :
    ∃ n : ℤ, ∑ i ∈ s, f i = n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨n, hn⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    obtain ⟨m, hm⟩ := h a (Finset.mem_insert_self a s)
    exact ⟨m + n, by rw [Finset.sum_insert ha, hm, hn]; push_cast; ring⟩

theorem sdec (P : M.Par) (hOK : P.OK) :
    SDec (fun j : Fin P.k => ((P.u ((j : ℕ) + 1) : ℝ) : ℂ) - (P.k : ℂ) / 2 + 1 / 2) := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  obtain ⟨na, hna⟩ := u_int P hOK ((a : ℕ) + 1) (by omega) (by have := a.isLt; omega)
  obtain ⟨nb, hnb⟩ := u_int P hOK ((b : ℕ) + 1) (by omega) (by have := b.isLt; omega)
  have hm := u_mono P hOK ((a : ℕ) + 1) (by omega) ((b : ℕ) - a) (by have := b.isLt; omega)
  rw [show (a : ℕ) + 1 + ((b : ℕ) - a) = (b : ℕ) + 1 by omega] at hm
  have hba : (1 : ℝ) ≤ (((b : ℕ) - (a : ℕ) : ℕ) : ℝ) := by
    have : 1 ≤ (b : ℕ) - (a : ℕ) := by omega
    exact_mod_cast this
  have hdiff : P.u ((a : ℕ) + 1) - P.u ((b : ℕ) + 1) = ((na - nb : ℤ) : ℝ) := by
    push_cast; linarith
  have hge : (1 : ℤ) ≤ na - nb := by
    have : (1 : ℝ) ≤ ((na - nb : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨(na - nb - 1).toNat, ?_⟩
  have hN : (((na - nb - 1).toNat : ℕ) : ℤ) = na - nb - 1 := Int.toNat_of_nonneg (by omega)
  have hNR : (((na - nb - 1).toNat : ℕ) : ℝ) = ((na - nb : ℤ) : ℝ) - 1 := by
    have := congrArg (fun x : ℤ => (x : ℝ)) hN
    push_cast at this ⊢
    linarith
  have hNC : (((na - nb - 1).toNat : ℕ) : ℂ) = (((((na - nb - 1).toNat : ℕ) : ℝ)) : ℂ) := by push_cast; rfl
  rw [hNC, hNR, ← hdiff]
  push_cast
  ring

theorem first_weight_half_integral {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (P : M.Par) (z : Fin (2 * P.r + P.k + 1) → ℂ) (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp))
    (hOK : P.OK) (hk : 2 ≤ P.k) (hz : inWb P.k P.r z) (hT : 0 < Tz P.k P.r z) (hty : IsType P.k P.r z π P.u) :
    ∃ n : ℤ, P.u 1 = n + ((P.k : ℝ) - 1) / 2 := by
  obtain ⟨hnt, hrep, hcont, -, -, hcap⟩ := hty
  have hR : IsRepW P.k P.r z π := ⟨hrep, hcont⟩
  obtain ⟨g, hgU, hgfix, hgz⟩ := Qx8.frameG_exists hz hT
  set Bs := QrCap.fr P.k P.r g with hBs
  have hB : IsFrameOf P.k P.r [z] Bs := QrCap.fr_frame hgU hgfix _ hgz
  set E := EB π Bs with hE
  have hFG := frame_general_linear Wp P.k P.r P.k z π Bs hR hB
  have hgl : GlRel E := hFG.1
  set m : Fin P.k → ℂ := fun j => ((P.u ((j : ℕ) + 1) : ℝ) : ℂ) - (P.k : ℂ) / 2 + 1 / 2 with hm
  have hq : ∀ (w : ℂ) (v : Wp), qdet E w v = cpol m w • v := by
    intro w v
    rw [← hFG.2 w v, hcap Bs hB w v, ProductIntervalFrames.prod_Icc_one]
    congr 1
    unfold cpol
    apply Finset.prod_congr rfl
    intro j _
    simp only [hm]
    ring
  have htop : CapSp E m = ⊤ := by
    rw [eq_top_iff]
    intro v _
    exact mem_CapSp.2 (hq · v)
  have hne : CapSp E m ≠ ⊥ := by
    rw [htop]
    exact top_ne_bot
  have hstabT : Stab E (⊤ : Submodule ℂ Wp) := fun _ _ _ _ => Submodule.mem_top
  obtain ⟨ν, v, -, hv0, hHW, -⟩ := exists_singular_maximal_vector Wp P.k E hgl ⊤ hstabT top_ne_bot
  have hsd := sdec P hOK
  have hν := (capelli_singular Wp P.k E m hgl hne).2 hsd ν v (by rw [htop]; exact Submodule.mem_top) hv0 hHW
  set c0 : Fin P.k := ⟨0, by omega⟩ with hc0
  have hν0 : ν c0 = m c0 := by rw [hν c0]; simp [hc0]

  set θ : Fin P.k → ℝ := fun c => if c = c0 then 2 * Real.pi else 0 with hθ
  have hDg : QrCap.Dg θ = QrCap.Dg (0 : Fin P.k → ℝ) := by
    unfold QrCap.Dg
    congr 1
    funext c
    simp only [hθ, Pi.zero_apply]
    split_ifs
    · push_cast
      rw [show (2 * (Real.pi : ℂ)) * Complex.I = 2 * Real.pi * Complex.I by ring, Complex.exp_two_pi_mul_I]
      simp
    · rfl
  have hblk : PI.UpqRep.blockW P.k P.r (QrCap.Dg θ) = 1 := by
    rw [hDg, ← QrCap.diag_exp_blockW]
    have : QrCap.dθ P.k P.r (0 : Fin P.k → ℝ) = 0 := by
      funext i
      unfold QrCap.dθ
      split_ifs <;> simp
    rw [this, NormedSpace.exp_zero]
    exact Matrix.diagonal_one
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det _).2 (WeylGroupFacts.isUnit_of_uh hgU)
  have hπ1 : π (NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • unitB (Hpk P.k P.r) Bs c c)) = 1 := by
    rw [QrCap.torus hgU θ, hblk, mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)]
    exact hrep.1
  have hop := QrCap.op_torus hR hB θ
  rw [hπ1] at hop
  set A : Wp →L[ℂ] Wp := ∑ c, ((θ c : ℂ) * Complex.I) • ecOp π (unitB (Hpk P.k P.r) Bs c c) with hA
  have hAv : A v = ((2 * Real.pi : ℂ) * Complex.I * ν c0) • v := by
    rw [hA, ContinuousLinearMap.sum_apply, Finset.sum_eq_single c0]
    · rw [ContinuousLinearMap.smul_apply]
      have h1 : ecOp π (unitB (Hpk P.k P.r) Bs c0 c0) v = ν c0 • v := hHW.1 c0
      rw [h1, smul_smul]
      simp [hθ]
    · intro b _ hb
      simp [hθ, hb]
    · intro h; exact absurd (Finset.mem_univ c0) h
  have hexp := QrCap.exp_eig A _ v hAv
  rw [← hop] at hexp
  have h1 : Complex.exp ((2 * Real.pi : ℂ) * Complex.I * ν c0) = 1 := by
    by_contra hne1
    have : (1 - Complex.exp ((2 * Real.pi : ℂ) * Complex.I * ν c0)) • v = 0 := by
      rw [sub_smul, one_smul]
      have := hexp
      simp only [ContinuousLinearMap.one_apply] at this
      rw [← this, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact hne1 (sub_eq_zero.1 h).symm
    · exact hv0 h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
  have hνn : ν c0 = n := by
    have hpi : (2 * Real.pi : ℂ) * Complex.I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    rw [hn]; ring
  refine ⟨n, ?_⟩
  have hre := congrArg Complex.re (hν0.symm.trans hνn)
  simp only [hm, hc0] at hre
  simp at hre
  linarith

end GTRIntPf

open GTRIntPf in
theorem radial_gauge_integrality_holds : GTRInt := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hpl hk ρ
  obtain ⟨hOK, hz, hz', hTz, hTz', hty, hty'⟩ := hpl
  have hT : 0 < Tz P.k P.r z := by rw [hTz]; exact hOK.T_pos
  obtain ⟨N0, hN0⟩ := first_weight_half_integral P z π hOK hk hz hT hty

  have hU : ∃ n : ℤ, ∑ i ∈ Finset.Icc 1 P.k, ((P.u i - P.u 1) + (P.u' i - P.u 1)) = n := by
    apply sum_int
    intro i hi
    obtain ⟨a, ha⟩ := hOK.int_u i hi
    obtain ⟨b, hb⟩ := hOK.int_u' i hi
    exact ⟨a + b, by rw [ha, hb]; push_cast; ring⟩
  have hRh : ∃ n : ℤ, ∑ i ∈ Finset.Icc 1 (P.k - 1), (M.rho P ρ i - P.u 1 - 1 / 2) = n := by
    apply sum_int
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
    unfold M.rho
    rw [dif_pos ⟨hi1, hi2⟩]
    unfold M.Par.lo
    obtain ⟨a, ha⟩ := hOK.int_u (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    obtain ⟨b, hb⟩ := hOK.int_u' (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    rcases max_choice (P.u (i + 1)) (P.u' (i + 1)) with h | h
    · exact ⟨a + ((ρ ⟨i - 1, by omega⟩ : Fin _) : ℕ), by rw [h]; push_cast; linarith⟩
    · exact ⟨b + ((ρ ⟨i - 1, by omega⟩ : Fin _) : ℕ), by rw [h]; push_cast; linarith⟩
  obtain ⟨nU, hnU⟩ := hU
  obtain ⟨nR, hnR⟩ := hRh
  have hcU : ∑ i ∈ Finset.Icc 1 P.k, ((P.u i - P.u 1) + (P.u' i - P.u 1)) = uSum P - 2 * P.k * P.u 1 := by
    unfold uSum
    rw [Finset.sum_congr rfl (fun i _ => show (P.u i - P.u 1) + (P.u' i - P.u 1) = (P.u i + P.u' i) - 2 * P.u 1 by ring),
      Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    rw [show P.k + 1 - 1 = P.k by omega]
    ring
  have hcR : ∑ i ∈ Finset.Icc 1 (P.k - 1), (M.rho P ρ i - P.u 1 - 1 / 2) =
      rhoSum P ρ - ((P.k : ℝ) - 1) * (P.u 1 + 1 / 2) := by
    unfold rhoSum
    rw [Finset.sum_congr rfl (fun i _ => show M.rho P ρ i - P.u 1 - 1 / 2 = M.rho P ρ i - (P.u 1 + 1 / 2) by ring),
      Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    rw [show P.k - 1 + 1 - 1 = P.k - 1 by omega, Nat.cast_sub (by omega)]
    push_cast
    ring

  obtain ⟨t, ht⟩ : ∃ t : ℕ, (P.k : ℝ) * ((P.k : ℝ) - 1) = 2 * t := by
    obtain ⟨t, ht⟩ := Nat.even_mul_pred_self P.k
    refine ⟨t, ?_⟩
    have : ((P.k * (P.k - 1) : ℕ) : ℝ) = ((t + t : ℕ) : ℝ) := by rw [ht]
    push_cast [Nat.cast_sub (show 1 ≤ P.k by omega)] at this
    linarith
  refine ⟨nU - nR + (P.k + 1) * N0 + t, ?_⟩
  have e1 : uSum P = nU + 2 * P.k * P.u 1 := by linarith
  have e2 : rhoSum P ρ = nR + ((P.k : ℝ) - 1) * (P.u 1 + 1 / 2) := by linarith
  rw [e1, e2, hN0]
  push_cast
  linear_combination ht / 2

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
