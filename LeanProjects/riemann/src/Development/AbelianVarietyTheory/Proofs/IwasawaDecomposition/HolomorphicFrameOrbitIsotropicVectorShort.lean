import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajorantHarnackHolomorphicHalfPlaneStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.OrbitShort

theorem quad_bound {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℂ → V → ℝ) (T : ℝ) (M : ℕ) (hM : 0 < M) (b ξ : V)
    (h0 : ∀ w : ℂ, T < w.im → ∀ v, 0 ≤ m w v)
    (hsm : ∀ (w : ℂ) (k : ℕ) (v : V), m w ((k : ℂ) • v) = (k : ℝ) ^ 2 * m w v)
    (hpar : ∀ (w : ℂ) (u v : V), m w (u + v) + m w (u - v) = 2 * m w u + 2 * m w v)
    (hH : ∀ w w' : ℂ, T < w.im → T < w'.im → ∀ v,
      m w' v ≤ (2 + ‖w - w'‖ ^ 2 / ((w.im - T) * (w'.im - T))) * m w v)
    (hξ : ∀ w : ℂ, T < w.im → m (w + M) ξ = m w ξ)
    (hb : ∀ w : ℂ, T < w.im → ∀ k : ℕ, m (w + M) (b + ((k + 1 : ℕ) : ℂ) • ξ) = m w (b + (k : ℂ) • ξ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, T + 1 < w.im → m w ξ * (w.im - T) ≤ A := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hξk : ∀ (k : ℕ) (w : ℂ), T < w.im → m (w + k * M) ξ = m w ξ := by
    intro k w hw
    induction k with
    | zero => simp
    | succ k ih =>
      have e : w + ((k + 1 : ℕ) : ℂ) * M = (w + k * M) + M := by push_cast; ring
      rw [e, hξ _ (by simpa using hw), ih]
  have hbk : ∀ (k : ℕ) (w : ℂ), T < w.im → m (w + k * M) (b + (k : ℂ) • ξ) = m w b := by
    intro k w hw
    induction k with
    | zero => simp
    | succ k ih =>
      have e : w + ((k + 1 : ℕ) : ℂ) * M = (w + k * M) + M := by push_cast; ring
      rw [e, hb _ (by simpa using hw), ih]
  set w0 : ℂ := ((T + 1 : ℝ) : ℂ) * Complex.I with hw0
  have hw0im : w0.im = T + 1 := by simp [hw0]
  have hw0re : w0.re = 0 := by simp [hw0]
  have hm0 : 0 ≤ m w0 b := h0 _ (by rw [hw0im]; linarith) _
  refine ⟨(M : ℝ) ^ 2 * ((6 + 2 * (1 + (M : ℝ)) ^ 2) * ((3 + (M : ℝ) ^ 2) * m w0 b)), by positivity, ?_⟩
  have strip : ∀ w : ℂ, T + 1 < w.im → 0 ≤ w.re → w.re < M → m w ξ * (w.im - T) ≤
      (M : ℝ) ^ 2 * ((6 + 2 * (1 + (M : ℝ)) ^ 2) * ((3 + (M : ℝ) ^ 2) * m w0 b)) := by
    intro w hw hr0 hr1
    have hw' : T < w.im := by linarith
    obtain ⟨y, hy⟩ : ∃ y, y = w.im - T := ⟨_, rfl⟩
    have hy1 : 1 < y := by linarith
    have hy0 : 0 < y := by linarith
    rw [← hy]

    have g1 : m w b ≤ (3 + (M : ℝ) ^ 2) * y * m w0 b := by
      refine (hH w0 w (by rw [hw0im]; linarith) hw' b).trans (mul_le_mul_of_nonneg_right ?_ hm0)
      have e1 : ‖w0 - w‖ ^ 2 = w.re ^ 2 + (y - 1) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hw0im, hw0re, hy]; ring
      rw [e1, hw0im, ← hy, show (T + 1 - T) * y = y by ring]
      have : (w.re ^ 2 + (y - 1) ^ 2) / y ≤ (1 + (M : ℝ) ^ 2) * y := by
        rw [div_le_iff₀ hy0]
        have a1 : w.re ^ 2 ≤ (M : ℝ) ^ 2 := by nlinarith
        have a2 : (M : ℝ) ^ 2 * 1 ≤ (M : ℝ) ^ 2 * (y * y) := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
        nlinarith
      nlinarith
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, y ≤ k * M ∧ (k : ℝ) * M ≤ y + M := by
      refine ⟨⌈y / M⌉₊, ?_, ?_⟩
      · rw [← div_le_iff₀ hMr]; exact Nat.le_ceil _
      · have := (Nat.ceil_lt_add_one (a := y / M) (by positivity)).le
        have h2 := mul_le_mul_of_nonneg_right this hMr.le
        rwa [add_mul, div_mul_cancel₀ _ hMr.ne', one_mul] at h2
    have hwk : T < (w + k * M).im := by simpa using hw'
    have hmb : 0 ≤ m w b := h0 _ hw' _
    have g2 : m (w + k * M) b ≤ (2 + (1 + (M : ℝ)) ^ 2) * m w b := by
      refine (hH w (w + k * M) hw' hwk b).trans (mul_le_mul_of_nonneg_right ?_ hmb)
      have e1 : ‖w - (w + k * M)‖ ^ 2 = ((k : ℝ) * M) ^ 2 := by
        rw [show w - (w + k * M) = -(k * M) by ring, norm_neg, norm_mul]; simp
      have e2 : (w + k * M).im = w.im := by simp
      rw [e1, e2, ← hy]
      have : ((k : ℝ) * M) ^ 2 / (y * y) ≤ (1 + (M : ℝ)) ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have a1 : (k : ℝ) * M ≤ (1 + M) * y := by nlinarith
        have a2 := pow_le_pow_left₀ (by positivity) a1 2
        nlinarith
      linarith
    have g3 : (k : ℝ) ^ 2 * m w ξ ≤ (6 + 2 * (1 + (M : ℝ)) ^ 2) * m w b := by
      have p := hpar (w + k * M) (b + (k : ℂ) • ξ) b
      rw [show b + (k : ℂ) • ξ - b = (k : ℂ) • ξ by abel, hsm, hξk k w hw', hbk k w hw'] at p
      have := h0 _ hwk (b + (k : ℂ) • ξ + b)
      linarith
    have hmξ : 0 ≤ m w ξ := h0 _ hw' _
    have g4 : y ^ 2 * m w ξ ≤ ((k : ℝ) * M) ^ 2 * m w ξ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy0.le hk1 2) hmξ
    have g5 : (M : ℝ) ^ 2 * ((k : ℝ) ^ 2 * m w ξ) ≤
        (M : ℝ) ^ 2 * ((6 + 2 * (1 + (M : ℝ)) ^ 2) * ((3 + (M : ℝ) ^ 2) * y * m w0 b)) :=
      mul_le_mul_of_nonneg_left (g3.trans (mul_le_mul_of_nonneg_left g1 (by positivity))) (by positivity)
    refine le_of_mul_le_mul_left ?_ hy0
    nlinarith
  intro w hw
  have hper : Function.Periodic (fun s : ℝ => m ((s : ℂ) + (w.im : ℂ) * Complex.I) ξ) (M : ℝ) := by
    intro s
    have e : ((s + (M : ℝ) : ℝ) : ℂ) + (w.im : ℂ) * Complex.I = ((s : ℂ) + (w.im : ℂ) * Complex.I) + M := by
      push_cast; ring
    show m _ ξ = m _ ξ
    rw [e, hξ _ (by simp; linarith)]
  obtain ⟨s, hs, hse⟩ := hper.exists_mem_Ico₀ hMr w.re
  simp only [Complex.re_add_im] at hse
  have := strip ((s : ℂ) + (w.im : ℂ) * Complex.I) (by simpa using hw) (by simpa using hs.1) (by simpa using hs.2)
  rw [hse]
  simpa using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (X : Data E N)

open ReciprocityTheory.ChartRestriction.G.FD in

theorem maj_natCast_smul (x : Frame X.Ψ N) (τ : X.Ψ) (k : ℕ) (v : Fin N → ℂ) :
    X.maj x τ ((k : ℂ) • v) = (k : ℝ) ^ 2 * X.maj x τ v := by
  unfold Data.maj Data.posPart
  have e : ∀ a b c : ℂ, (k : ℂ) * a * b * ((k : ℂ) * c) = (((k : ℝ) ^ 2 : ℝ) : ℂ) * (a * b * c) := by
    intro a b c; push_cast; ring
  have e' : ∀ a : ℂ, (k : ℂ) * ((k : ℂ) * a) = (((k : ℝ) ^ 2 : ℝ) : ℂ) * a := by
    intro a; push_cast; ring
  simp only [hermC_smul_left, hermC_smul_right, map_mul, map_natCast, e, e', ← Finset.mul_sum,
    Complex.re_ofReal_mul]
  ring

open ReciprocityTheory.ChartRestriction.G.FD in

theorem maj_parallelogram (x : Frame X.Ψ N) (τ : X.Ψ) (u v : Fin N → ℂ) :
    X.maj x τ (u + v) + X.maj x τ (u - v) = 2 * X.maj x τ u + 2 * X.maj x τ v := by
  have hs : u - v = u + (-1 : ℂ) • v := by simp [sub_eq_add_neg]
  have hp : X.posPart x τ (u + v) + X.posPart x τ (u - v) = 2 * X.posPart x τ u + 2 * X.posPart x τ v := by
    unfold Data.posPart
    rw [two_mul, two_mul]
    simp only [← Complex.add_re, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hs, hermC_add_left, hermC_smul_left, map_add, map_mul, map_neg, map_one]
    ring
  have hh : hermC τ.1 X.Gm (u + v) (u + v) + hermC τ.1 X.Gm (u - v) (u - v) =
      hermC τ.1 X.Gm u u + hermC τ.1 X.Gm u u + (hermC τ.1 X.Gm v v + hermC τ.1 X.Gm v v) := by
    simp only [hs, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, map_neg, map_one]
    ring
  have hh' := congrArg Complex.re hh
  simp only [Complex.add_re] at hh'
  unfold Data.maj
  linarith

end GlobalTheory.OrbitShort

open GlobalTheory.OrbitShort in

theorem GlobalTheory.orbit_unipotent_short : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ((γ : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → γ ≠ 1 → ∃ (ξ : Fin N → E) (c : ℝ), X.IsIso ξ ∧ 0 < c ∧ ∀ w : ℂ, T + 1 < w.im → ∀ τ, c * (w.im - T) ≤ X.tt ξ (x w) τ := by
  intro E _ _ _ N X T M γ x ⟨hM, hγ, hd, hdom, hsh⟩ hsq hne
  have hst := X.Γ_stab γ hγ
  obtain ⟨b, hbΛ, hb⟩ : ∃ b ∈ X.Λ, Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E) - 1) b ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hne
    have hz : Matrix.toLin' ((γ : Matrix (Fin N) (Fin N) E) - 1) = 0 := by
      refine LinearMap.ext_on X.Λ_span fun v hv => ?_
      rw [Matrix.toLin'_apply, hc v hv]; rfl
    have hz' : (γ : Matrix (Fin N) (Fin N) E) - 1 = 0 := Matrix.toLin'.map_eq_zero_iff.1 hz
    exact Units.ext (sub_eq_zero.1 hz')
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E) - 1) b := ⟨_, rfl⟩
  rw [← hξ] at hb
  have hγb : Matrix.mulVec (γ : Matrix (Fin N) (Fin N) E) b = b + ξ := by
    rw [hξ, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have hγξ : Matrix.mulVec (γ : Matrix (Fin N) (Fin N) E) ξ = ξ := by
    have : Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E) - 1) ξ = 0 := by
      rw [hξ, Matrix.mulVec_mulVec, ← sq, hsq, Matrix.zero_mulVec]
    rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  have hξΛ : ξ ∈ X.Λ := by
    have h1 := (hst.2 b).1 hbΛ
    rw [hγb] at h1
    simpa using X.Λ.sub_mem h1 hbΛ
  have hiso : ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ ξ = 0 := by
    have h1 := hst.1 ξ b
    rw [hγb, hγξ] at h1
    have h2 : ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ (b + ξ) =
        ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ b + ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ ξ := by
      simp [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, mul_add, Finset.sum_add_distrib]
    rw [h2] at h1
    simpa using h1
  have hemb : ∀ (τ : X.Ψ) (v : Fin N → E),
      Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) (Data.emb τ.1 v) =
        Data.emb τ.1 (Matrix.mulVec (γ : Matrix (Fin N) (Fin N) E) v) := by
    intro τ v
    funext i
    simp [Data.emb, Matrix.mulVec, dotProduct]
  have hshift : ∀ w : ℂ, T < w.im → ∀ (τ : X.Ψ) (v : Fin N → ℂ),
      X.maj (x (w + M)) τ (Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) v) = X.maj (x w) τ v := by
    intro w hw τ v
    obtain ⟨β, hβ, -, he⟩ := hsh w hw
    rw [he, GlobalTheory.MajInv.maj_rmul X (GlobalTheory.MajInv.lact_mem_dom X hst (hdom w hw)) hβ, GlobalTheory.MajInv.maj_lact X hst]
  have hA : ∀ τ : X.Ψ, ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, T + 1 < w.im →
      X.maj (x w) τ (Data.emb τ.1 ξ) * (w.im - T) ≤ A := by
    intro τ
    have eξ : Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) (Data.emb τ.1 ξ) = Data.emb τ.1 ξ := by
      rw [hemb, hγξ]
    have eb : Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) (Data.emb τ.1 b) =
        Data.emb τ.1 b + Data.emb τ.1 ξ := by
      rw [hemb, hγb]; funext i; simp [Data.emb]
    refine quad_bound (fun w v => X.maj (x w) τ v) T M hM (Data.emb τ.1 b) (Data.emb τ.1 ξ) ?_
      (fun w k v => maj_natCast_smul X _ τ k v) (fun w u v => maj_parallelogram X _ τ u v)
      (fun w w' hw hw' v => GlobalTheory.T.majorant_harnack_holomorphic_half_plane E N X T x hd hdom w w' hw hw' τ v) ?_ ?_
    · intro w hw v
      by_cases hv : v = 0
      · have := maj_natCast_smul X (x w) τ 0 v
        subst hv
        rw [smul_zero, Nat.cast_zero, sq, zero_mul, zero_mul] at this
        exact this.ge
      · exact (X.maj_pos (hdom w hw) τ hv).le
    · intro w hw
      have := hshift w hw τ (Data.emb τ.1 ξ)
      rwa [eξ] at this
    · intro w hw k
      have := hshift w hw τ (Data.emb τ.1 b + (k : ℂ) • Data.emb τ.1 ξ)
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, eξ, eb] at this
      rw [← this]
      congr 1
      push_cast
      rw [add_smul, one_smul]; abel
  choose A hA0 hA using hA
  have hc : ∀ τ : X.Ψ, 0 < X.c τ := fun τ => by
    have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero_iff τ.1 τ.1.injective).2 X.ξ0_ne
    unfold Data.c
    positivity
  have hK0 : 0 ≤ ∑ τ, X.c τ * A τ := Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ).le (hA0 τ)
  refine ⟨ξ, 1 / (1 + ∑ τ, X.c τ * A τ), ⟨hξΛ, hiso, hb⟩, by positivity, fun w hw τ => ?_⟩
  have hv : Data.emb τ.1 ξ ≠ 0 := fun h => hb (funext fun a =>
    (map_eq_zero_iff τ.1 τ.1.injective).1 (congrFun h a))
  have hp := X.maj_pos (hdom w (by linarith)) τ hv
  have hle : X.c τ * A τ ≤ ∑ τ, X.c τ * A τ :=
    Finset.single_le_sum (f := fun τ => X.c τ * A τ) (fun τ _ => mul_nonneg (hc τ).le (hA0 τ)) (Finset.mem_univ τ)
  have h1 := mul_le_mul_of_nonneg_left (hA τ w hw) (hc τ).le
  unfold Data.tt
  rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (mul_pos (hc τ) hp)]
  nlinarith
