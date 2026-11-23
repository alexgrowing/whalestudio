import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRecordOverChoices
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TotientDvdCardUnitsQuot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

noncomputable section

namespace GlobalTheory.BigOn.Inhab

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
open GlobalTheory.FieldSize GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 Formalism.L2.Pj Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons GlobalTheory.RunJoin
open GlobalTheory.Mem
open GlobalTheory.EX.OB

def RichRec (D : D7) : Prop :=
  GlobalTheory.Mem.Chr.SplitsC D.host.E D.host.pde ∧ GlobalTheory.Mem.Chr.SplitsC D.host.E D.host.pde' ∧
    (∀ j : Fin D.R.m, UpperTheory.MUQ (fun τ => D.host.emb (D.eTau τ : D.R.GG)) (fun τ => (D.hc τ).e j)) ∧
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (15 * classNumber D.host.E) ∈ FO D

set_option maxHeartbeats 1000000 in

theorem exists_rich_record_over_choices (hR : GlobalTheory.NT.RayField) (eps cD ch : ℝ) (C : FC) (h0 : 0 < eps) (h1 : eps < 1 / 52)
    (hC : Std C) (hcD : 0 ≤ cD) (hch : 402 ≤ ch) : ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ)
      (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (Lv : LevCh P), s.eps = eps → x0 ≤ s.x →
      ChOK s C cD ch P q1 a b c → Lv.GamP = GamS C s P.R →
      ∃ D : D7, (JointQ D ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (15 * classNumber D.host.E) ∈ FO D) ∧ Nonempty (ErrX D) ∧ DV.KapDef D ∧ HostArith D.host ∧
        ∃ L : SizeData₂ D, L.sc = s ∧ Val C cD ch L := by
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC hcD hch
  refine ⟨x0, ?_⟩
  intro s P q1 a b c Lv hs hx hP hG
  obtain ⟨F, hfd, hrich, hsz⟩ := exists_rich_small_of_rayField hR (StdFrameObj.coordPre P Lv)
  obtain ⟨B, hB, hF, -⟩ := exists_base_of_rich _ F hfd hrich ∅ ∅ (by simp) (by simp)
  have hxp : 0 < s.x := by linarith [s.one_lt_alt]
  have hDel : (0 : ℚ) < (Delv s cD : ℚ) := by
    have : 0 < Delv s cD := Nat.ceil_pos.2 (by positivity)
    exact_mod_cast this
  have hlev : ∀ p ∈ Lv.host.levelPrimes, Lv.host.cls p = .splitK := (StdFrameObj.coordPre P Lv).level_split
  have key : ∀ Q : Pre, Q = StdFrameObj.coordPre P Lv → ∃ letter : Q.Word → Fin (Q.R.k - 2) → Bool, Function.Injective letter ∧
      (∀ w τ (l : ℕ) (h : l + 1 < Q.R.k - 1),
        (Q.hcW w τ).v ⟨l, by omega⟩ - (Q.hcW w τ).v ⟨l + 1, h⟩ = 4 * (Delv s cD : ℚ)) ∧
      ∀ w τ (l : ℕ) (h : l < Q.R.k - 2), (Q.hcW w τ).u ⟨l + 1, by omega⟩ =
        (Q.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then (Delv s cD : ℚ) else 0) := by
    rintro Q rfl
    refine ⟨c, hP.inj, fun w τ l h => ?_, fun w τ l h => hP.code w τ l h⟩
    have h' : l + 1 < P.R.k - 1 := h
    have a1 := (hP.hc w).1 τ ⟨l, by omega⟩
    have a2 := (hP.hc w).1 τ ⟨l + 1, h'⟩
    refine (congrArg₂ (· - ·) a1 a2).trans ?_
    have : P.R.k - 2 - l = (P.R.k - 2 - (l + 1)) + 1 := by omega
    simp only [this]
    push_cast
    ring
  obtain ⟨letter, k1, k2, k3⟩ := key B.toPre hB
  obtain ⟨X, rfl, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_stages_with_delta B (Delv s cD : ℚ) letter (6 * s.x ^ (-C.P.CF)) hDel (by positivity) k1 k2 k3
  clear key k1 k2 k3 letter
  have hJ : JointQ X.toD7 := jointQ_of_small_field X F (hB ▸ hrich)
    ((congrArg (fun Q : Pre => ∀ L : ℝ, HostSz Q.host L → Sz F (poR Q.R L) (poR Q.R L)) hB).mpr hsz) hF
  have hZ := (fieldOK0_and_zeta_mem X F (hB ▸ hrich) hF _ (Or.inl rfl)).2
  have hE : Nonempty (ErrX X.toD7) := GlobalTheory.T.error_data_of_norm_generators X
    ((congrArg (fun Q : Pre => ∀ i, ∃ π : 𝓞 Q.host.E, (π : Q.host.E) ∈ Q.host.K ∧
      (π : Q.host.E) * Q.host.conj (π : Q.host.E) = (Q.host.g i : Q.host.E)) hB).mpr hP.arith.1)
  clear hF hrich hsz
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  refine ⟨D, ⟨hJ, hZ⟩, hE, e3, ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩, ?_⟩
  obtain ⟨L, l1, -, -, l4⟩ := hx0 s D (fun t => a t.1) (fun t => b t.1) hs hx hP.rank hP.val (hP.hc P.u₀) hP.dlog e1 hP.ct2
    hP.card e2 (fun u => by
      have e : (D.mem u).A.GamP = Lv.GamP := Cc.A_GamP u
      rw [e, hG, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top P.u₀ τ t h ht) e4
  exact ⟨L, l1, l4⟩

theorem exists_richRec_of_zeroFreeRegion : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → GlobalTheory.NT.RayField → ∀ x : ℝ, ∃ D : D7, RecOK D x ∧ RichRec D := by
  intro p1 p2 p3 p4 p5 p6 p7 p8 p9 hR x
  have hH := DC.hostExQ_of_hostEx (smallPrimeOne_of_tzRat p6) (hostEx_of_zeroFreeRegion p1 p2 p3 p4 p5 p6 p7 p8 p9)
  have hLP := (normPrimes_and_levelPrime p9).2
  have he : (0 : ℝ) < 1 / 53 := by norm_num
  have he52 : (1 / 53 : ℝ) < 1 / 52 := by norm_num
  obtain ⟨CT2, C8, C5, c6, Cb, hC8, -, -, -, hK⟩ := exists_chGood_unb hH _ he he52
  obtain ⟨C, hStd, hCT2, hCp, -⟩ := exists_std_large ⟨0, 0, fun _ => 0, fun _ => 0⟩
    ⟨0, 0, fun _ => 0, fun _ => 0⟩ CT2 C8 hC8
  obtain ⟨c1, hN⟩ := szRow_numAt _ he he52 C hStd
  obtain ⟨c2, hN⟩ := hN (max c1 0) (le_max_left _ _)
  obtain ⟨x1, hN⟩ := hN (max c2 402) (le_max_left _ _)
  have hK := hK C hStd hCT2 hCp (max c1 0) (le_max_right _ _) (max c2 402) (le_max_right _ _)
  obtain ⟨x3, h3⟩ := exists_levCh_of_levelPrime hLP _ 1 C he he52 one_pos hStd
  obtain ⟨x4, h4⟩ := exists_rich_record_over_choices hR _ (max c1 0) (max c2 402) C he he52 hStd (le_max_right _ _) (le_max_right _ _)
  obtain ⟨s, hs, hy, hK⟩ := hK (max (10 ^ 60) (max x1 (max x3 (max x4 (max x (C.T.CP ^ 20))))))
  simp only [max_le_iff] at hy
  obtain ⟨hy60, hy1, hy3, hy4, hyx, hyP⟩ := hy
  obtain ⟨P, a, b, c, hP, -⟩ := hK 0
  have hfk : (0 : ℝ) < (P.R.f : ℝ) * P.R.k := by
    have h1 := P.R.m_add_three_le_k
    have h2 : 0 < P.R.f := by have := P.R.ord_pos; show 0 < 2 * P.R.ord; omega
    have h3 : 0 < P.R.k := by omega
    positivity
  obtain ⟨Ds, hDs, hlog⟩ := exists_window_start _ (1 * P.R.m * s.L) (GamS C s P.R) hfk (Real.exp_pos _)
  obtain ⟨Lv, -, -, l3⟩ := h3 _ _ s P _ a b c (fun _ => 1) Ds hs hy3 hP.ok (fun _ => one_pos) hDs (fun _ => hlog)
  obtain ⟨D, ⟨⟨h1, h2, h3, h4, h5⟩, hZ⟩, hE, hkap, hA, L, hsc, hV⟩ := h4 s P _ a b c Lv hs hy4 hP.ok l3
  have hsx : L.sc.x = s.x := by rw [hsc]
  have hse : L.sc.eps = 1 / 53 := by rw [hsc, hs]
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (hy1.trans hsx.ge) hV hA
  have hCP : N.parT.CP = C.T.CP := (List.cons.inj N.parT_K).1
  have hg : ∀ j, Real.log (D.host.g j) ≤ 9 * L.sc.L + 1 := fun j => by
    have hL : 0 ≤ L.sc.L := by
      unfold Scale.L; exact Real.rpow_nonneg (zero_le_one.trans L.sc.one_lt_alt.le) _
    have hlo : 0 < ((D.host.g j : ℕ) : ℝ) := by exact_mod_cast (D.host.g_prime j).pos
    have := (Real.log_le_iff_le_exp hlo).2 (N.g_le j)
    linarith
  obtain ⟨hHS, hFS⟩ := hostSz_of_sizes D L N.params N.parT N.sizes hg (hy60.trans hsx.ge)
  refine ⟨D, ⟨h1, h2, h3, h4, hE, L, N.params, N.parT, hkap, N.sizes,
    N.CnW_eq.trans hStd.1.2.2.2.2.2.2.2.1, hg, ?_, ?_, hyx.trans hsx.ge, hFS (h5 _ hHS)⟩,
    (GlobalTheory.Mem.Chr.ncard_places_eq_primesOver D.host.pde_prime).trans hA.2.2.1.1,
    (GlobalTheory.Mem.Chr.ncard_places_eq_primesOver D.host.pde'_prime).trans hA.2.2.1.2, hV.hc.2.2.2, hZ⟩
  · rw [hCP]; exact hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hCP]
    exact hyP.trans (hsx.ge.trans (x_le_zBase_of_pow_le_n L N.win.1.1))

end GlobalTheory.BigOn.Inhab

end
