import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.IsFDiagIffDiagonal
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSpacesOfOver

noncomputable section

namespace GlobalTheory.Mem.HostFrames

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem log_add_rpow_le (eps : ℝ) (he : 0 < eps) :
    ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → 24 * Real.log x + x ^ (eps / 3) ≤ x ^ eps := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ (1 / 48) * ‖x ^ eps‖ :=
    (isLittleO_log_rpow_atTop he).bound (by norm_num)
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ^ (2 * eps / 3) :=
    (tendsto_rpow_atTop (by positivity : 0 < 2 * eps / 3)).eventually_ge_atTop 2
  obtain ⟨x0, h⟩ := Filter.eventually_atTop.1 (h1.and (h2.and (Filter.eventually_gt_atTop 1)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨a1, a2, a3⟩ := h x hx
  have hx0 : 0 < x := by linarith
  have p1 : 0 < x ^ eps := Real.rpow_pos_of_pos hx0 _
  have p3 : 0 < x ^ (eps / 3) := Real.rpow_pos_of_pos hx0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos p1] at a1
  have e : x ^ eps = x ^ (eps / 3) * x ^ (2 * eps / 3) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have b1 : 2 * x ^ (eps / 3) ≤ x ^ eps := by
    rw [e]; nlinarith
  have b2 := (le_abs_self _).trans a1
  linarith

theorem thin_size (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks),
    s.eps = eps → x0 ≤ s.x → RankVal s R → 100 * (R.r : ℝ) ^ 4 + 1 ≤ s.w'' R.n := by
  obtain ⟨x1, h1⟩ := rank_basic_bounds eps he he'
  obtain ⟨x2, h2⟩ := log_add_rpow_le eps he
  refine ⟨max (max x1 x2) 202, fun s R hs hx hR => ?_⟩
  have hx1 : x1 ≤ s.x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx2 : x2 ≤ s.x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx3 : 202 ≤ s.x := (le_max_right _ _).trans hx
  obtain ⟨-, -, hr, -⟩ := h1 s R hs hx1 hR
  have hl := h2 s.x hx2
  have hx0 : 0 < s.x := by linarith
  have hxone : 1 ≤ s.x := by linarith
  obtain ⟨⟨n1, n2⟩, -⟩ := hR
  have hn1 : 1 ≤ (R.n : ℝ) := (Real.one_le_rpow hxone (by rw [hs]; positivity)).trans n1
  have hn3 : (R.n : ℝ) ≤ 2 * s.x ^ 3 := by
    refine n2.trans ?_
    have : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hxone (by rw [hs]; linarith)
    rw [Real.rpow_ofNat] at this
    linarith
  have hr4 : (R.r : ℝ) ^ 4 ≤ s.x ^ 20 := by
    have := pow_le_pow_left₀ (by positivity) hr 4
    calc (R.r : ℝ) ^ 4 ≤ (s.x ^ 5) ^ 4 := by exact_mod_cast this
      _ = s.x ^ 20 := by ring
  have hw : s.w'' R.n = Real.exp (s.L - s.x ^ (s.eps / 3)) / R.n := by
    simp only [Scale.w'', Scale.b', Scale.a, Scale.b, Scale.X', Real.exp_sub]
    field_simp
  have hexp : s.x ^ 24 ≤ Real.exp (s.L - s.x ^ (s.eps / 3)) := by
    have : Real.log (s.x ^ 24) ≤ s.L - s.x ^ (s.eps / 3) := by
      rw [Real.log_pow, Scale.L, hs]; push_cast; linarith
    calc s.x ^ 24 = Real.exp (Real.log (s.x ^ 24)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.2 this
  rw [hw, le_div_iff₀ (by linarith)]
  have a1 : 1 ≤ s.x ^ 20 := one_le_pow₀ hxone
  have a2 : 100 * (R.r : ℝ) ^ 4 + 1 ≤ 101 * s.x ^ 20 := by linarith
  calc (100 * (R.r : ℝ) ^ 4 + 1) * R.n ≤ (101 * s.x ^ 20) * (2 * s.x ^ 3) :=
        mul_le_mul a2 hn3 (by linarith) (by positivity)
    _ = 202 * s.x ^ 23 := by ring
    _ ≤ s.x * s.x ^ 23 := by gcongr
    _ = s.x ^ 24 := by ring
    _ ≤ _ := hexp

theorem thin_le (s : Scale) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ s.b' ∧ s.w'' n ≤ s.b' / s.x ∧ s.w'' n ≤ s.b := by
  have hx0 : 0 < s.x := by linarith [s.one_lt_alt]
  have hb0 : 0 < s.b := Real.exp_pos _
  have hX0 : 1 ≤ s.X' := Real.one_le_exp (by have := Real.rpow_nonneg hx0.le (s.eps / 3); linarith)
  have hb' : 0 ≤ s.b' := by
    simp only [Scale.b', Scale.a]; positivity
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : s.w'' n ≤ s.b' / s.x := by
    simp only [Scale.w'']
    rw [← div_div]
    exact div_le_self (by positivity) hn'
  refine ⟨hb', h1, h1.trans ?_⟩
  have : s.b' / s.x = s.b / s.X' := by
    simp only [Scale.b', Scale.a]; field_simp
  rw [this]
  exact div_le_self hb0.le hX0

theorem first_node (s : Scale) {C : FC} {cD ch : ℝ} {P : PreCh} {q1 : ℕ} {a b : P.R.A → ℤ}
    {c : P.Word → Fin (P.R.k - 2) → Bool} (ok : ChOK s C cD ch P q1 a b c)
    (hs : 100 * (P.R.r : ℝ) ^ 4 + 1 ≤ s.w'' P.R.n) (u : P.Word) (τ : Tau P.R) (hm : 0 < P.R.m) :
    100 * (P.R.r : ℝ) ^ 4 ≤ (((P.hcW u τ).b ⟨0, hm⟩ : ℚ) : ℝ) := by
  obtain ⟨b1, hb, hT, hTh, hTn⟩ := (ok.hc u).2.2.1
  have e0 : (((P.hcW u τ).b ⟨0, hm⟩ : ℚ) : ℝ) = (b1 τ : ℝ) := by
    rw [(hb τ ⟨0, hm⟩).1]; simp
  rw [e0]
  have hn : 1 ≤ P.R.n := Formalism.HC.Frame.ord_pos _
  obtain ⟨hb0, hw1, hw2⟩ := thin_le s hn
  by_cases h1 : (τ : P.R.GG) ∈ P.H.topPlaces
  · obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h1
    have e1 := hT τ ⟨t, ht⟩ hte.symm
    have w := (ok.win t ht).2.1
    rw [e1]
    push_cast
    have f := Int.sub_one_lt_floor (s.b' / s.x)
    have f' : s.b' / s.x - 1 < (⌊s.b' / s.x⌋ : ℝ) := by exact_mod_cast f
    linarith
  · by_cases h2 : (τ : P.R.GG) ∈ P.H.thickPlaces
    · have c1 : s.b ≤ (⌈s.b⌉ : ℝ) := Int.le_ceil _
      have e1 : ((⌈s.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (hTh τ h2).1
      linarith
    · have e1 := hTn τ ⟨τ.2, h1, h2⟩
      have c1 : s.w'' P.R.n ≤ (⌈s.w'' P.R.n⌉ : ℝ) := Int.le_ceil _
      rw [e1]
      linarith

theorem ev_of_large (p : Ctx → Prop) (H : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ y x0 : ℝ, ∀ K : Ctx,
    K.s.eps = eps → y ≤ K.cD → y ≤ K.ch → x0 ≤ K.s.x → p K) : Ev p := by
  refine ⟨1, one_pos, fun eps C8 he _ he' _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ?_⟩⟩
  obtain ⟨y, x0, h⟩ := H eps he he'
  exact ⟨y, fun cD hcD => ⟨y, fun ch hch => ⟨x0, fun K _ k1 k2 k3 k4 => h K k3 (k1 ▸ hcD) (k2 ▸ hch) k4⟩⟩⟩

theorem first_node_over {K : Ctx} {B : Pre} (h : K.Over B)
    (hs : 100 * (K.P.R.r : ℝ) ^ 4 + 1 ≤ K.s.w'' K.P.R.n) (u : B.Word) (τ : Tau B.R) (hm : 0 < B.R.m) :
    100 * (B.R.r : ℝ) ^ 4 ≤ (((B.hcW u τ).b ⟨0, hm⟩ : ℚ) : ℝ) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, hd⟩ := h
  exact first_node K.s K.ok hs u τ hm

theorem hostHyp_of_gaps (D : D7) (h Δ : ℕ)
    (hh : 256 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 4 ≤ h) (hΔ : 256 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 4 ≤ Δ)
    (hg : ∀ u τ, (∀ j, (D.hcW u τ).e j - (D.hcW u τ).b j = h) ∧
      (∀ (j : Fin D.R.m) (hj : j.1 + 1 < D.R.m), (D.hcW u τ).b ⟨j.1 + 1, hj⟩ - (D.hcW u τ).e j = h) ∧
      ∀ i : Fin (D.R.k - 1), (D.hcW u τ).v i = ((D.R.k - 2 - i.1 : ℕ) : ℚ) * (4 * Δ))
    (hb : ∀ u τ (hm : 0 < D.R.m), 100 * (D.R.r : ℝ) ^ 4 ≤ (((D.hcW u τ).b ⟨0, hm⟩ : ℚ) : ℝ)) : HostHyp D := by
  have hm2 := D.R.two_le_m
  have hk3 := D.R.m_add_three_le_k
  have hrN : D.R.r ≤ D.R.N D.R.m := by
    have : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (by omega)
    simp only [Ranks.r, Ranks.N]; omega
  have hhN : 256 * D.R.N D.R.m ^ 4 ≤ h := by exact_mod_cast hh
  have hΔN : 256 * D.R.N D.R.m ^ 4 ≤ Δ := by exact_mod_cast hΔ
  have prN : D.R.r ^ 4 ≤ D.R.N D.R.m ^ 4 := Nat.pow_le_pow_left hrN 4
  have htN : D.R.t ≤ D.R.N D.R.m := by
    have : 1 * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_right _ (by omega)
    simp only [Ranks.N]; omega
  have hN1 : 1 ≤ D.R.N D.R.m := by
    simp only [Ranks.N]; omega
  set N : ℝ := ((D.R.N D.R.m : ℕ) : ℝ) with hN
  have n1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hN1
  have nt : (D.R.t : ℝ) ≤ N := by rw [hN]; exact_mod_cast htN
  have nr : (D.R.r : ℝ) ≤ N := by rw [hN]; exact_mod_cast hrN
  have p3 : N ^ 3 ≤ N ^ 4 := pow_le_pow_right₀ n1 (by norm_num)
  have p1 : N ≤ N ^ 4 := le_self_pow₀ n1 (by norm_num)
  have p0 : 1 ≤ N ^ 4 := one_le_pow₀ n1
  have pr : (D.R.r : ℝ) ^ 4 ≤ N ^ 4 := pow_le_pow_left₀ (by positivity) nr 4
  have eh : ∀ τ, D.hc τ = D.hcW D.u₀ τ := fun τ => (congrFun D.hcW_base τ).symm
  have two : ∀ u τ (j : Fin D.R.m) (hj : j.1 + 1 < D.R.m),
      (D.hcW u τ).b ⟨j.1 + 1, hj⟩ - (D.hcW u τ).b j = 2 * (h : ℚ) := by
    intro u τ j hj
    have e1 := (hg u τ).1 j
    have e2 := (hg u τ).2.1 j hj
    linarith
  have nodeAll : ∀ c : ℝ, c ≤ 2 * h → D.NodeGap c := by
    intro c hc u τ j hj
    have := two u τ ⟨j, by omega⟩ hj
    rw [this]
    push_cast
    exact hc
  have cloud : ∀ τ, 100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k - 2) -
      Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k - 1) := by
    intro τ
    have a1 : D.R.k - 2 < D.R.k - 1 := by omega
    have a2 : ¬ D.R.k - 1 < D.R.k - 1 := lt_irrefl _
    have a3 : D.R.k - 1 - (D.R.k - 1) < D.R.m := by omega
    have hm : 0 < D.R.m := by omega
    have l1 : Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k - 2) = 0 := by
      rw [Formalism.L2.NTheta.lamAt, dif_pos a1, eh, (hg _ τ).2.2 ⟨D.R.k - 2, a1⟩]
      simp
    have l2 : Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k - 1) = -(D.hc τ).b ⟨0, hm⟩ := by
      rw [Formalism.L2.NTheta.lamAt, dif_neg a2, dif_pos a3]
      congr 2
      exact Fin.ext (by simp)
    rw [l1, l2, eh]
    have := hb D.u₀ τ hm
    have q : (100 * (D.R.r : ℚ) ^ 4 : ℚ) ≤ (D.hcW D.u₀ τ).b ⟨0, hm⟩ := by exact_mod_cast this
    linarith
  refine ⟨fun τ => ⟨fun i => ⟨(D.hc τ).u_gt_v i, (D.hc τ).v_gt_u i⟩, (D.hc τ).u_last_gt, fun j => ?_, fun j hj => ?_⟩,
    fun τ j => ⟨(D.hc τ).gap_be j, fun hj => (D.hc τ).gap_eb j hj⟩, fun τ n hn => ?_, cloud, nodeAll _ ?_, nodeAll _ ?_⟩
  · have := (D.hc τ).gap_be j
    have t0 : (0 : ℚ) < ((D.R.t : ℚ) + 3) / 2 := by positivity
    show (D.hc τ).b j < (D.hc τ).e j
    linarith
  · have := (D.hc τ).gap_eb j hj
    have t0 : (0 : ℚ) < ((D.R.t : ℚ) + 3) / 2 := by positivity
    show (D.hc τ).e j < (D.hc τ).b ⟨j.1 + 1, hj⟩
    linarith
  · rcases lt_trichotomy (n + 1) (D.R.k - 1) with c | c | c
    · have a1 : n < D.R.k - 1 := by omega
      rw [Formalism.L2.NTheta.lamAt, Formalism.L2.NTheta.lamAt, dif_pos a1, dif_pos c, eh, (hg _ τ).2.2 ⟨n, a1⟩, (hg _ τ).2.2 ⟨n + 1, c⟩]
      have e : ((D.R.k - 2 - n : ℕ) : ℚ) = ((D.R.k - 2 - (n + 1) : ℕ) : ℚ) + 1 := by
        have : D.R.k - 2 - n = D.R.k - 2 - (n + 1) + 1 := by omega
        rw [this]; push_cast; ring
      simp only [e]
      have q : (256 * (D.R.N D.R.m : ℚ) ^ 4 : ℚ) ≤ Δ := by exact_mod_cast hΔN
      have qr : (D.R.r : ℚ) ^ 4 ≤ (D.R.N D.R.m : ℚ) ^ 4 := by exact_mod_cast prN
      nlinarith
    · have e : n = D.R.k - 2 := by omega
      have e' : n + 1 = D.R.k - 1 := c
      rw [e', e]
      exact cloud τ
    · have a1 : ¬ n < D.R.k - 1 ∨ n = D.R.k - 1 := by omega
      have a2 : ¬ n < D.R.k - 1 := by omega
      have a3 : ¬ n + 1 < D.R.k - 1 := by omega
      have a4 : n - (D.R.k - 1) < D.R.m := by simp only [Ranks.r] at hn; omega
      have a5 : n + 1 - (D.R.k - 1) < D.R.m := by simp only [Ranks.r] at hn; omega
      have a6 : (n - (D.R.k - 1)) + 1 < D.R.m := by omega
      rw [Formalism.L2.NTheta.lamAt, Formalism.L2.NTheta.lamAt, dif_neg a2, dif_neg a3, dif_pos a4, dif_pos a5, eh]
      have := two D.u₀ τ ⟨n - (D.R.k - 1), a4⟩ a6
      have f : (⟨n + 1 - (D.R.k - 1), a5⟩ : Fin D.R.m) = ⟨n - (D.R.k - 1) + 1, a6⟩ := Fin.ext (by simp; omega)
      rw [f]
      have q : (256 * (D.R.N D.R.m : ℚ) ^ 4 : ℚ) ≤ h := by exact_mod_cast hhN
      have qr : (D.R.r : ℚ) ^ 4 ≤ (D.R.N D.R.m : ℚ) ^ 4 := by exact_mod_cast prN
      nlinarith
  · nlinarith
  · nlinarith

theorem stdLat_of_eq {D : D7} (V : HSp D) (hstar : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (neg : Fin N → Bool) (p q : ℕ) (h : V = Examples₂.stdSpace hstar N neg p q) : Formalism.IndefR.Seed.FrmC.StdLat V := by
  subst h
  intro x
  exact Formalism.IndefR.Seed.FrmC.stdLat_std hstar N neg p q x

theorem stdLat_diag {D : D7} (hd : DiagSpaces D.sp) :
    (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (D.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (D.sp.V j) ∧
      (1 ≤ j → j ≤ D.R.m → Formalism.IndefR.Seed.FrmC.StdLat (D.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat D.sp.X' := by
  obtain ⟨hs, -, hX, hY, hW, hV⟩ := hd
  exact ⟨fun j => ⟨stdLat_of_eq _ hs _ _ _ _ (hY j), stdLat_of_eq _ hs _ _ _ _ (hV j),
    fun a b => stdLat_of_eq _ hs _ _ _ _ (hW j a b)⟩, stdLat_of_eq _ hs _ _ _ _ hX⟩

theorem hostHyp_frames_ev : Ev fun K => ∀ X : Stages, K.Over X.B.toPre →
    HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧
    (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧
    (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧
      (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧
    Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧
    (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧
      (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧
    ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧
      X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame)) := by
  refine ev_of_large _ fun eps he he' => ?_
  obtain ⟨x0, h0⟩ := size_le eps 256 4 he he'
  obtain ⟨x1, h1⟩ := thin_size eps he he'
  refine ⟨402 * (4 : ℕ) + 2, max x0 x1, fun K k3 kD kh kx X hX => ?_⟩
  have kx0 : x0 ≤ K.s.x := (le_max_left _ _).trans kx
  have kx1 : x1 ≤ K.s.x := (le_max_right _ _).trans kx
  obtain ⟨hR, bT, hH⟩ := val_of_over hX
  have hL : 1 ≤ K.s.L := Real.one_le_rpow K.s.one_lt_alt.le K.s.eps_pos.le
  have big : ∀ y : ℝ, 402 * ((4 : ℕ) : ℝ) + 2 ≤ y →
      256 * ((X.toD7.R.N X.toD7.R.m : ℕ) : ℝ) ^ 4 ≤ (⌈K.s.x ^ y⌉₊ : ℝ) := by
    intro y hy
    have := h0 K.s X.B.R y k3 kx0 hR hy
    have pN : (0 : ℝ) ≤ ((X.toD7.R.N X.toD7.R.m : ℕ) : ℝ) ^ 4 := by positivity
    refine le_trans ?_ this
    show 256 * ((X.B.R.N X.B.R.m : ℕ) : ℝ) ^ 4 ≤ _
    have pN' : (0 : ℝ) ≤ ((X.B.R.N X.B.R.m : ℕ) : ℝ) ^ 4 := pN
    nlinarith
  have hthin := h1 K.s K.P.R k3 kx1 K.ok.rank
  have hyp : HostHyp X.toD7 := by
    refine hostHyp_of_gaps X.toD7 ⌈K.s.x ^ K.ch⌉₊ (Delv K.s K.cD) (big _ kh) (big _ kD) (fun u τ => ?_)
      (fun u τ hm => first_node_over hX hthin u τ hm)
    obtain ⟨hv, -, ⟨b1, hb, -⟩, -⟩ := hH u
    refine ⟨fun j => ?_, fun j hj => ?_, hv τ⟩
    · have := (hb τ j).2
      show (X.B.hcW u τ).e j - (X.B.hcW u τ).b j = _
      rw [this]
      simp only [h0v]; push_cast; ring
    · have e1 := (hb τ j).2
      have e2 := (hb τ j).1
      have e3 := (hb τ ⟨j.1 + 1, hj⟩).1
      refine (congrArg₂ (· - ·) e3 (e1.trans (congrArg (· + _) e2))).trans ?_
      simp only [h0v]; push_cast; ring
  have hd : DiagSpaces X.toD7.sp := diagSpaces_of_over hX
  obtain ⟨hF, hWV, hP, -, -, hVf, hXf⟩ := frames_of_over K X hX
  obtain ⟨hst, hstX⟩ := stdLat_diag hd
  have fd : ∀ V : HSp X.toD7, SignFrame V → IsFDiag V := fun V hV => by
    obtain ⟨d, -, h⟩ := hV.gram_eq X.toD7.host.F
    exact ⟨d, h⟩
  exact ⟨hyp, hF, fun i => ⟨fd _ (hWV i).1, fd _ (hWV i).2⟩, hP, hst, hstX, hVf, hXf⟩

theorem frames_by_cases_stdW {D : D7} (hY : ∀ j, Formalism.IndefR.Seed.FrmC.StdLat (D.sp.Y j))
    (hX : Formalism.IndefR.Seed.FrmC.StdLat D.sp.X') (hV : ∀ j, Formalism.IndefR.Seed.FrmC.StdLat (D.sp.V j))
    (hW : ∀ i : Fin D.R.m, Formalism.IndefR.Seed.FrmC.StdLat (Wc D i)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    ∃ ΛY ΛW βY βW,
      Formalism.IndefR.Seed.Frm.SDFrames ΛY (Formalism.IndefR.Seed.FrmP.coordL D.sp.X') (fun i => Formalism.IndefR.Seed.FrmP.coordL (Vc D i)) ΛW βY 1
        (fun _ => 1) βW ∧
        (Formalism.IndefR.Seed.Frm.FramesExistDiagonal D Pg → Formalism.IndefR.Seed.Frm.NormalFrameConditionsDiagonal Pg βY βW) := by
  by_cases h : Formalism.IndefR.Seed.Frm.FramesExistDiagonal D Pg
  · obtain ⟨ΛY, -, -, ΛW, βY, -, -, βW, ⟨h1, -, -, h4⟩, h2⟩ := h
    exact ⟨ΛY, ΛW, βY, βW, ⟨h1, Formalism.IndefR.Seed.FrmP.isSDFrame_std _ hX 1,
      fun i => Formalism.IndefR.Seed.FrmP.isSDFrame_std _ (hV _) 1, h4⟩, fun _ => h2⟩
  · exact ⟨fun j => Formalism.IndefR.Seed.FrmP.coordL _, fun i => Formalism.IndefR.Seed.FrmP.coordL (Wc D i),
      fun _ => 1, fun _ => 1,
      ⟨fun j _ => Formalism.IndefR.Seed.FrmP.isSDFrame_std _ (hY _) _, Formalism.IndefR.Seed.FrmP.isSDFrame_std _ hX 1,
        fun i => Formalism.IndefR.Seed.FrmP.isSDFrame_std _ (hV _) 1, fun i => Formalism.IndefR.Seed.FrmP.isSDFrame_std _ (hW i) 1⟩,
      fun h' => absurd h' h⟩

end GlobalTheory.Mem.HostFrames

end
