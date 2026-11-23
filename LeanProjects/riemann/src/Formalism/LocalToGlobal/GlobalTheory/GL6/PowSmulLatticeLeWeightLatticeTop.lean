import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLcInt
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticePropsOfModel
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGlob

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions NumberField

section GenU

variable {O : Subring ℂ} {r : ℕ}

theorem diagonal_update_mem_elementary (j : Fin r) {p : ℂ} (hp : p ∈ O) :
    Matrix.diagonal (Function.update (1 : Fin r → ℂ) j p) ∈ bwA_EO O r := by
  have e : Matrix.diagonal (Function.update (1 : Fin r → ℂ) j p) = 1 + Matrix.single j j (p - 1) := by
    ext a b
    rw [Matrix.add_apply, Matrix.single_apply, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      by_cases ha : j = a
      · subst ha; simp
      · simp [ha, Function.update_of_ne (Ne.symm ha)]
    · have h2 : ¬ (j = a ∧ j = b) := fun h => hab (h.1 ▸ h.2)
      simp [hab, h2]
  rw [e]; exact bwD_gen_mem j j (O.sub_mem hp O.one_mem)

theorem elementary_product_of_column_reduction (hL : bwD_Loc O) (N M : Matrix (Fin r) (Fin r) ℂ)
    (hM : bwD_Int O M) (hNM : N * M = 1)
    (j : Fin r) (av : Fin r → ℂ) (hav : ∀ k, av k ∈ O)
    (hcol : ∀ k, k ≠ j → ∀ a, N a k - N a j * av k ∈ O) : M ∈ bwA_EO O r := by
  classical
  set p := M.det with hpdef
  have hdet : N.det * p = 1 := by rw [hpdef, ← Matrix.det_mul, hNM, Matrix.det_one]
  have hMN : M * N = 1 := mul_eq_one_comm.1 hNM
  have hadj : M.adjugate = p • N := by
    calc M.adjugate = M.adjugate * (M * N) := by rw [hMN, Matrix.mul_one]
      _ = p • N := by rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hpN : ∀ a b, N a b * p ∈ O := fun a b => by
    have := bwD_Int_adj hM a b
    rw [hadj, Matrix.smul_apply, smul_eq_mul, mul_comm] at this; exact this
  set X : Matrix (Fin r) (Fin r) ℂ := ∑ k ∈ Finset.univ.erase j, Matrix.single j k (av k) with hX
  have hXX0 : ∀ k ∈ Finset.univ.erase j, ∀ k' ∈ Finset.univ.erase j,
      Matrix.single j k (av k) * Matrix.single j k' (av k') = 0 := fun k hk k' _ =>
    Matrix.single_mul_single_of_ne _ _ _ _ (Finset.ne_of_mem_erase hk) _
  have hXX0' : ∀ k ∈ Finset.univ.erase j, ∀ k' ∈ Finset.univ.erase j,
      Matrix.single j k (-av k) * Matrix.single j k' (-av k') = 0 := fun k hk k' _ =>
    Matrix.single_mul_single_of_ne _ _ _ _ (Finset.ne_of_mem_erase hk) _
  have hXX : X * X = 0 := by
    rw [hX, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun i' hi' => hXX0 i hi i' hi'))
  have hQE : 1 - X ∈ bwA_EO O r := by
    have e : 1 - X = 1 + ∑ k ∈ Finset.univ.erase j, Matrix.single j k (-av k) := by
      rw [hX, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      simp only [Matrix.single_neg]
    rw [e]
    exact bwD_sum_mem _ _ (fun k _ => bwD_gen_mem _ _ (O.neg_mem (hav k))) hXX0'
  have hQdet : (1 + X).det = 1 := bwD_sum_det _ _
    (fun k hk => Matrix.det_transvection_of_ne j k (Finset.ne_of_mem_erase hk).symm (av k)) hXX0
  have hNX : ∀ a b, (N * X) a b = if b ∈ Finset.univ.erase j then N a j * av b else 0 := by
    intro a b
    rw [hX, Finset.mul_sum, Matrix.sum_apply]
    simp_rw [bwD_mul_single_apply]
    rw [Finset.sum_ite_eq]
  have h1X : (1 - X) * (1 + X) = 1 := by rw [sub_mul, one_mul, mul_add, mul_one, hXX]; abel
  set N' := N * (1 - X) with hN'def
  have hN' : ∀ a b, N' a b = N a b - if b ∈ Finset.univ.erase j then N a j * av b else 0 := by
    intro a b; rw [hN'def, mul_sub, mul_one, Matrix.sub_apply, hNX]
  have hN'Q : N' * (1 + X) = N := by rw [hN'def, Matrix.mul_assoc, h1X, Matrix.mul_one]
  have hN'det : N'.det = N.det := by
    have := congrArg Matrix.det hN'Q; rw [Matrix.det_mul, hQdet, mul_one] at this; exact this
  set N'' := N' * Matrix.diagonal (Function.update 1 j p) with hN''def
  have hN''I : bwD_Int O N'' := by
    intro a b
    rw [hN''def, Matrix.mul_diagonal, hN']
    by_cases hb : b = j
    · subst hb
      rw [if_neg (fun h => (Finset.mem_erase.1 h).1 rfl), sub_zero, Function.update_self]
      exact hpN a b
    · rw [if_pos (Finset.mem_erase.2 ⟨hb, Finset.mem_univ _⟩), Function.update_of_ne hb, Pi.one_apply, mul_one]
      exact hcol b hb a
  have hN''det : N''.det = 1 := by
    rw [hN''def, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ j), hN'det]
    simpa using hdet
  have hinvE : N''.adjugate ∈ bwA_EO O r :=
    bwD_elim hL _ (bwD_Int_adj hN''I) ⟨N'', hN''I, by rw [Matrix.mul_adjugate, hN''det, one_smul]⟩
  have hY : N * ((1 - X) * Matrix.diagonal (Function.update 1 j p) * N''.adjugate) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hN'def, ← hN''def, Matrix.mul_adjugate, hN''det, one_smul]
  have hYN := mul_eq_one_comm.1 hY
  have hM' : M = (1 - X) * Matrix.diagonal (Function.update 1 j p) * N''.adjugate := by
    calc M = ((1 - X) * Matrix.diagonal (Function.update 1 j p) * N''.adjugate) * N * M := by
          rw [hYN, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc _ N M, hNM, Matrix.mul_one]
  rw [hM']
  exact (bwA_EO O r).mul_mem ((bwA_EO O r).mul_mem hQE (diagonal_update_mem_elementary j (bwD_det_mem hM))) hinvE

theorem pow_mul_zpow_mem_of_shift (T : ℕ) (p : ℂ) (hpO : p ∈ O) (hTp : (T : ℂ) * p⁻¹ ∈ O) (n : ℕ) (s : ℤ)
    (hns : 0 ≤ (n : ℤ) + s) : (T : ℂ) ^ n * p ^ s ∈ O := by
  by_cases hs : 0 ≤ s
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, s = m := ⟨s.toNat, (Int.toNat_of_nonneg hs).symm⟩
    rw [hm, zpow_natCast]
    exact O.mul_mem (O.pow_mem (natCast_mem O T) n) (O.pow_mem hpO m)
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, s = -(m : ℤ) := ⟨(-s).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    have hmn : m ≤ n := by omega
    rw [hm, zpow_neg, zpow_natCast, ← Nat.sub_add_cancel hmn, pow_add, mul_assoc, ← inv_pow, ← mul_pow]
    exact O.mul_mem (O.pow_mem (natCast_mem O T) _) (O.pow_mem hTp m)

end GenU

section SpecU

open Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical
open scoped Matrix

variable (D : D7) (u : D.what₂.Word)

theorem basis_change_mem_elementary (Tt : FormsTied D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (v : (D.mem u).A.vT)
    (τ : D.what₂.Tau) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B') :
    (((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map (embT D τ) ∈
        bwA_EO (bwA_Ow D w) (D.R.N i) ∧
      ((((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map (embT D τ)).det ∈
        bwA_Ow D w ∧
      ((((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map (embT D τ)).det ≠ 0 ∧
      ((D.mem u).A.T : ℂ) *
        (((((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
          (embT D τ)).det)⁻¹ ∈ bwA_Ow D w := by
  have hLk : Lk Tt.atT i hi v c ≤ Ld D u i hi c := sup_le (bwL_lcInt D u Tt i hi c) Submodule.smul_le_right
  set σ := embT D τ with hσ
  set N := (((B'⁻¹ * B : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map σ
    with hNdef
  set M := (((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map σ
    with hMdef
  set colB : Fin (D.R.N i) → Fin (D.R.N i) → D.host.E :=
    fun k r => (B : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r k with hcolB
  have hNa : ∀ a k, N a k = σ ((((B'⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) *ᵥ colB k) a) := by
    intro a k; rw [hcolB, bwD_mulVec_col, ← Units.val_mul]; rfl
  have hNM : N * M = 1 := by
    rw [hNdef, hMdef, ← Matrix.map_mul, ← Units.val_mul,
      show B'⁻¹ * B * (B⁻¹ * B') = 1 by group, Units.val_one, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hMI : bwD_Int (bwA_Ow D w) M := by
    intro a k
    obtain ⟨s, hs, hsL⟩ := bwD_col_loc D u w hw hB' k
    have := bwD_locBasis_int D u w hw τ hB _ s hs (hLk hsL) a
    rw [bwD_mulVec_col, ← Units.val_mul] at this
    exact this
  choose sB hsB hsBL using fun k => bwD_col_loc D u w hw hB k
  have hT0 : ∀ k, (sB k : D.host.E) ≠ 0 := fun k => Nat.cast_ne_zero.2 (fun h => hsB k (h ▸ dvd_zero _))
  have htN : ∀ a b, ((D.mem u).A.T : ℂ) * N a b ∈ bwA_Ow D w := by
    intro a b
    have hL : (sB b : D.host.E) • (((D.mem u).A.T : D.host.E) • colB b) ∈ (Lk Tt.atT i hi v c : Set _) := by
      rw [smul_comm]
      have := bwA_T_smul_Ld_mem_Lk D u Tt.atT i hi v c _ (hsBL b)
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E] at this
      exact this
    have := bwD_locBasis_int D u w hw τ hB' _ (sB b) (hsB b) hL a
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast] at this
    rw [hNa]; exact this
  obtain ⟨j, av, hav, hcol⟩ : ∃ (j : Fin (D.R.N i)) (av : Fin (D.R.N i) → ℂ), (∀ k, av k ∈ bwA_Ow D w) ∧
      ∀ k, k ≠ j → ∀ a, N a k - N a j * av k ∈ bwA_Ow D w := by
    set φ : Fin (D.R.N i) → (D.mem u).A.Fv v := fun k => (D.fm u).fv i v c ((Tt.lv i hi).pr v c ⟨_, hsBL k⟩) with hφ
    by_cases hex : ∃ j, φ j ≠ 0
    · obtain ⟨j, hj⟩ := hex
      choose α hα using fun k => Tt.atT.res_surj v (φ k / φ j)
      refine ⟨j, fun k => σ ((α k : D.host.E) * (sB j : D.host.E) / (sB k : D.host.E)), fun k => ?_, fun k _ a => ?_⟩
      · refine bwD_mem_Ow D u w hw _ _ (sB k) (hsB k) ⟨α k * (sB j : 𝓞 D.host.E), ?_⟩
        rw [map_mul, map_natCast]; field_simp [hT0 k]
      · set q : D.host.E := (α k : D.host.E) * (sB j : D.host.E) / (sB k : D.host.E) with hq
        have hz : (D.fm u).fv i v c ((Tt.lv i hi).pr v c (⟨_, hsBL k⟩ - α k • ⟨_, hsBL j⟩)) = 0 := by
          rw [map_sub, map_sub, (Tt.lv i hi).pr_smul, map_smul, hα k, smul_eq_mul, div_mul_cancel₀ _ hj, sub_self]
        have hzL := ((Tt.lv i hi).fv_ker v c _).1 hz
        have hx : (sB k : D.host.E) • (colB k - q • colB j) ∈ (Lk Tt.atT i hi v c : Set _) := by
          have e : (sB k : D.host.E) • (colB k - q • colB j) =
              ((⟨_, hsBL k⟩ - α k • ⟨_, hsBL j⟩ : Ld D u i hi c) : Fin (D.R.N i) → D.host.E) := by
            ext r
            simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hq]
            rw [Algebra.smul_def]
            field_simp [hT0 k]
            ring
          rw [e]; exact hzL
        have := bwD_locBasis_int D u w hw τ hB' _ (sB k) (hsB k) hx a
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul] at this
        rw [hNa, hNa, mul_comm (σ _)]; exact this
    · push Not at hex
      refine ⟨⟨0, D.R.N_pos i⟩, 0, fun _ => (bwA_Ow D w).zero_mem, fun k _ a => ?_⟩
      rw [Pi.zero_apply, mul_zero, sub_zero, hNa]
      exact bwD_locBasis_int D u w hw τ hB' _ (sB k) (hsB k)
        (((Tt.lv i hi).fv_ker v c _).1 (hex k)) a
  obtain ⟨-, -, -, -, hpO, hp0, hdet, htdet, -⟩ := bwD_decomp (bwD_loc_Ow D w) N M _ hMI hNM htN j av hav hcol
  refine ⟨elementary_product_of_column_reduction (bwD_loc_Ow D w) N M hMI hNM j av hav hcol, hpO, hp0, ?_⟩
  rw [← eq_inv_of_mul_eq_one_left hdet]
  exact htdet

theorem pow_smul_mem_weight_lattice (Tt : FormsTied D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (hs : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) (i : ℕ) (hi : i ≤ D.R.m) (n : ℕ)
    (hn : 0 ≤ (n : ℤ) + shiftOf (lamT u i) ((D.fm u).tauOf w v))
    (x : ((D.fm u).lat i).V) (hx : x ∈ ((D.fm u).lat i).L) :
    ((D.mem u).A.T : D.what₂.LL) ^ n • x ∈ (D.fm u).Bw i w v := by
  rw [(Tt.bw i hi) w hw hs v]
  intro c B B' hB hB'
  have hB0 : IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c)) B := by
    rw [hw, ← bwG_Ld_coe]; exact hB
  obtain ⟨P, hP, hxP⟩ := ((Tt.val i hi).lat x).1 hx w c B hB0
  set τv := (D.fm u).tauOf w v with hτv
  obtain ⟨hME, hpO, hM0, hTM⟩ := basis_change_mem_elementary D u Tt w hw v τv i hi c B B' hB hB'
  set Mv := (((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
    (embT D τv) with hMv
  set Nτ : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ := fun τ => if τ = τv then Mv else 1 with hNτ
  set Mfun : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ := fun τ =>
    if τ = τv then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ
      else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ with hMfun
  have hNM : (fun τ => Nτ τ * Mfun τ) = atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 := by
    funext τ
    simp only [hNτ, hMfun]
    split_ifs with h
    · subst h
      simp only [atInf, hMv]
      rw [← Matrix.map_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
    · rw [one_mul]
  have ho : ∀ τ, τ ≠ τv → Nτ τ = 1 := fun τ hτ => by simp only [hNτ]; rw [if_neg hτ]
  have hprod : (∏ τ, (Nτ τ).det ^ shiftOf (lamT u i) τ) = Mv.det ^ shiftOf (lamT u i) τv := by
    rw [Finset.prod_eq_single τv]
    · simp only [hNτ, if_pos rfl]
    · intro τ _ hτ; rw [ho τ hτ, Matrix.det_one, one_zpow]
    · simp
  have hc : tpow D u n * Mv.det ^ shiftOf (lamT u i) τv ∈ bwA_Ow D w := by
    exact pow_mul_zpow_mem_of_shift _ _ hpO hTM n _ hn
  refine ⟨tpow D u n • (MvPolynomial.C (∏ τ, (Nτ τ).det ^ shiftOf (lamT u i) τ) * subP Nτ P), ?_, fun z => ?_⟩
  · rw [hprod, MvPolynomial.C_mul', smul_smul]
    refine bwA_intSpan_subP D w ((D.fm u).lam i) τv Nτ ho _ (fun g hg => ?_) P hP
    have hg' : MvPolynomial.map (Int.castRingHom ℂ) g ∈ bwA_span (bwA_Ow D w) le_rfl ((D.fm u).lam i τv).natW :=
      Submodule.subset_span ⟨g, hg, rfl⟩
    have h1 := bwA_span_closure (bwA_Ow D w) le_rfl _ Mv hME _ hg'
    have e : (tpow D u n * Mv.det ^ shiftOf (lamT u i) τv) • Formalism.GradedWeylDivisibility.rowAct ℂ (Nτ τv) (MvPolynomial.map (Int.castRingHom ℂ) g) =
        (⟨_, hc⟩ : bwA_Ow D w) • Formalism.GradedWeylDivisibility.rowAct ℂ Mv (MvPolynomial.map (Int.castRingHom ℂ) g) := by
      simp only [hNτ, if_pos rfl]; rfl
    rw [e]
    exact Submodule.smul_mem _ _ h1
  · have hval : fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i))
          (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) P =
        fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) Mfun
          (MvPolynomial.C (∏ τ, (Nτ τ).det ^ shiftOf (lamT u i) τ) * subP Nτ P) := by
      rw [← fnOf_mul, hNM]
    rw [emb_tpow_smul, Pi.smul_apply, Pi.smul_apply, hxP z, hval, LinearMap.map_smul]
    rfl

end SpecU

section StepZero

open Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical

variable (D : D7) (u : D.what₂.Word)

theorem weight_shift_level_zero_eq (τ : D.what₂.Tau) : shiftOf (lamT u 0) τ = ((D.fm u).lam 0 τ).detShift := by
  rw [lamT_zero]; rfl

theorem pow_smul_lattice_le_weight_lattice (Tt : FormsTied D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (hs : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) (i : ℕ) (hi : i ≤ D.R.m) (n : ℕ)
    (hn : 0 ≤ (n : ℤ) + shiftOf (lamT u i) ((D.fm u).tauOf w v)) :
    ∀ x ∈ (D.fm u).S i w, ((D.mem u).A.T : D.what₂.LL) ^ n • x ∈ (D.fm u).Bw i w v := by
  intro x hx
  change x ∈ Submodule.span _ _ at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact pow_smul_mem_weight_lattice D u Tt w hw hs v i hi n hn y hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [Subring.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ a hy

theorem lattice_le_weight_lattice_of_shift (Tt : FormsTied D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (hs : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) (h : 0 ≤ ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift) :
    (D.fm u).S 0 w ≤ (D.fm u).Bw 0 w v := fun x hx => by
  have := pow_smul_lattice_le_weight_lattice D u Tt w hw hs v 0 (Nat.zero_le _) 0 (by rw [weight_shift_level_zero_eq]; simpa using h) x hx
  rwa [pow_zero, one_smul] at this

theorem pow_smul_lattice_le_weight_lattice_top (Tt : FormsTied D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (hs : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) (h : 0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v)) :
    tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w) ≤ (D.fm u).Bw 0 w v := by
  intro y hy
  obtain ⟨x, hx, he⟩ := hy
  have hbt : (D.fm u).bTop ((D.fm u).tauOf w v) = -((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift := rfl
  have hb : (D.fm u).bTop ((D.fm u).tauOf w v) = (((D.fm u).bTop ((D.fm u).tauOf w v)).toNat : ℤ) :=
    (Int.toNat_of_nonneg h).symm
  have key := pow_smul_lattice_le_weight_lattice D u Tt w hw hs v 0 (Nat.zero_le _) ((D.fm u).bTop ((D.fm u).tauOf w v)).toNat
    (by rw [weight_shift_level_zero_eq, ← hb, hbt]; omega) x hx
  have hy : y = ((D.mem u).A.T : D.what₂.LL) ^ ((D.fm u).bTop ((D.fm u).tauOf w v)).toNat • x := by
    apply (D.fm u).emb_inj 0
    rw [he, emb_tpow_smul, LinearMap.smul_apply, LinearMap.id_apply]
    conv_lhs => rw [hb]
    rw [zpow_natCast]; rfl
  rw [hy]; exact key

def WeightLatticeInclusions : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    (0 ≤ ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift → (D.fm u).S 0 w ≤ (D.fm u).Bw 0 w v) ∧
    (0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w) ≤ (D.fm u).Bw 0 w v)

theorem weight_lattice_inclusions (Tt : FormsTied D u) : WeightLatticeInclusions D u :=
  fun w hw hs v => ⟨lattice_le_weight_lattice_of_shift D u Tt w hw hs v, pow_smul_lattice_le_weight_lattice_top D u Tt w hw hs v⟩

end StepZero

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
