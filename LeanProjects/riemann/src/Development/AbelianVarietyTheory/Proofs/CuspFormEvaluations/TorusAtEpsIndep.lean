import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.SemicharIndep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem cc_cc (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

theorem cc_mul (a b : E) : cc (a * b) = cc a * cc b := map_mul (IsCMField.complexConj E) a b

theorem cc_sub (a b : E) : cc (a - b) = cc a - cc b := map_sub (IsCMField.complexConj E) a b

theorem trace_conj (a : E) : Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (a : E) (u v : Fin r → E) :
    herm G (a • u) v = a * herm G u v := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (a : E) (u v : Fin r → E) :
    herm G u (a • v) = cc a * herm G u v := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, cc_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → E) :
    herm G (u + u') v = herm G u v + herm G u' v := by
  simp [herm, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → E) :
    herm G u (v + v') = herm G u v + herm G u v' := by
  simp [herm, cc, mul_add, Finset.sum_add_distrib]

theorem cc_herm {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → E) :
    cc (herm G u v) = herm G v u := by
  have h : cc (herm G u v) = ∑ a, ∑ b, cc (u a * G a b * cc (v b)) := by
    simp only [herm, cc, map_sum]
  rw [h, herm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [cc_mul, cc_mul, cc_cc, hG]; ring

noncomputable def B (X : Data E r) (u v : Fin r → E) : ℚ :=
  Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v)

theorem B_skew (X : Data E r) (u v : Fin r → E) : B X u v = -B X v u := by
  unfold B
  rw [← trace_conj, ← map_neg, cc_mul, cc_herm X.Gm_herm, X.ξ0_im, neg_mul]

theorem B_adj (X : Data E r) (a : E) (u v : Fin r → E) : B X (a • u) v = B X u (cc a • v) := by
  unfold B
  rw [herm_smul_left, herm_smul_right, cc_cc]

theorem B_add_left (X : Data E r) (u u' v : Fin r → E) : B X (u + u') v = B X u v + B X u' v := by
  unfold B
  rw [herm_add_left, mul_add, map_add]

theorem B_add_right (X : Data E r) (u v v' : Fin r → E) : B X u (v + v') = B X u v + B X u v' := by
  unfold B
  rw [herm_add_right, mul_add, map_add]

theorem B_sub_smul (X : Data E r) (a b : E) (u v : Fin r → E) :
    B X u ((a - b) • v) = B X u (a • v) - B X u (b • v) := by
  unfold B
  rw [herm_smul_right, herm_smul_right, herm_smul_right, cc_sub, sub_mul, mul_sub, map_sub]

theorem B_swap (X : Data E r) (a : E) (u v : Fin r → E) : B X v (a • u) = -B X u (cc a • v) := by
  rw [B_skew, B_adj]

theorem EFf_eq (X : Data E r) (u v : Fin r → E) : EFf X.ξ0 X.Gm u v = -B X u v := by
  rw [EFf, neg_mul, map_neg, B]

theorem B_int (X : DataX E r) {u v : Fin r → E} (hu : u ∈ X.Λ) (hv : v ∈ X.Λ) :
    ∃ k : ℤ, B X.toData u v = k := by
  obtain ⟨k, hk⟩ := X.EF_int u hu v hv
  rw [EFf_eq] at hk
  exact ⟨-k, by push_cast; linarith⟩

theorem exists_half (X : DataX E r) (y : Fin r → E)
    (hy : ∀ u ∈ X.Λ, ∃ k : ℤ, B X.toData u y = 2 * k) :
    ∃ x ∈ X.Λ, ∀ u ∈ X.Λ, B X.toData u y = 2 * B X.toData u x := by
  choose! f hf using hy
  let φ : X.Λ →+ ℤ := AddMonoidHom.mk' (fun u => f u) (fun u v => by
    have h1 := hf _ (u + v).2
    have h2 := hf _ u.2
    have h3 := hf _ v.2
    rw [Submodule.coe_add, B_add_left, h2, h3] at h1
    have : ((f ((u : Fin r → E) + v) : ℤ) : ℚ) = f u + f v := by linarith
    exact_mod_cast this)
  obtain ⟨x, hx, h⟩ := X.EF_perf φ
  refine ⟨x, hx, fun u hu => ?_⟩
  have h1 := h ⟨u, hu⟩
  rw [EFf_eq, ← B_skew] at h1
  rw [hf u hu, ← h1]
  rfl

def Par (X : Data E r) (w : 𝓞 E) : Prop :=
  ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, B X u (((w : E) - cc (w : E)) • v) - B X u v = 2 * k

theorem smul_mem (X : Data E r) (w : 𝓞 E) {v : Fin r → E} (hv : v ∈ X.Λ) : (w : E) • v ∈ X.Λ :=
  X.Λ.smul_mem w hv

theorem cc_smul_mem (X : Data E r) (w : 𝓞 E) {v : Fin r → E} (hv : v ∈ X.Λ) :
    cc (w : E) • v ∈ X.Λ :=
  X.Λ.smul_mem (IsCMField.ringOfIntegersComplexConj E w) hv

theorem parity_eq (X : DataX E r) {w w' : 𝓞 E} (hw : Par X.toData w) (hw' : Par X.toData w')
    {v : Fin r → E} (hv : v ∈ X.Λ) :
    ∃ k : ℤ, B X.toData v ((w : E) • v) - B X.toData v ((w' : E) • v) = 2 * k := by
  obtain ⟨x, hx, h⟩ := exists_half X ((((w : E) - cc (w : E)) - ((w' : E) - cc (w' : E))) • v)
    (fun u hu => by
      obtain ⟨k, hk⟩ := hw u hu v hv
      obtain ⟨l, hl⟩ := hw' u hu v hv
      refine ⟨k - l, ?_⟩
      rw [B_sub_smul]; push_cast; linarith)
  have h1 := h v hv
  rw [B_sub_smul, B_sub_smul, B_sub_smul] at h1
  have h2 := B_swap X.toData (w : E) v v
  have h3 := B_swap X.toData (w' : E) v v
  obtain ⟨k, hk⟩ := hw v hv x hx
  have hm : (cc (w : E) - (w : E)) • v ∈ X.Λ := by
    rw [sub_smul]; exact sub_mem (cc_smul_mem X.toData w hv) (smul_mem X.toData w hv)
  have h4 := h _ hm
  rw [B_adj, B_adj, cc_sub, cc_cc, smul_smul] at h4
  have h5 := B_swap X.toData
    (((w : E) - cc (w : E)) * (((w : E) - cc (w : E)) - ((w' : E) - cc (w' : E)))) v v
  have h6 : cc (((w : E) - cc (w : E)) * (((w : E) - cc (w : E)) - ((w' : E) - cc (w' : E)))) =
      ((w : E) - cc (w : E)) * (((w : E) - cc (w : E)) - ((w' : E) - cc (w' : E))) := by
    simp only [cc_mul, cc_sub, cc_cc]; ring
  rw [h6] at h5
  refine ⟨-k, ?_⟩
  push_cast
  linarith

theorem cos_sign {s : ℝ} (hs : s = 1 ∨ s = -1) (k : ℤ) :
    Real.cos (Real.pi * (s * (((k : ℚ)) : ℝ))) = ((k.negOnePow : ℤ) : ℝ) := by
  have h := Real.cos_int_mul_pi k
  rw [← Int.cast_negOnePow] at h
  rcases hs with rfl | rfl
  · rw [← h]; congr 1; push_cast; ring
  · rw [← h, ← Real.cos_neg]; congr 1; push_cast; ring

theorem eps_val {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) {v : Fin r → E} (hv : v ∈ X.Λ)
    {k : ℤ} (hk : B X v ((A.w0 : E) • v) = k) : A.T.eps (A.φ v) = (k.negOnePow : ℤ) := by
  have h := A.eps_eq v hv
  rw [A.im_eq v hv _ (smul_mem X A.w0 hv)] at h
  unfold B at hk
  rw [hk, cos_sign A.sg_pm] at h
  exact_mod_cast h

theorem par_of_torusAt (X : DataX E r) {x : Frame X.Ψ r} (A : TorusAt X.toData x) :
    Par X.toData A.w0 := by
  intro u hu v hv
  have huv := add_mem hu hv
  obtain ⟨a, ha⟩ := B_int X hu (smul_mem X.toData A.w0 hu)
  obtain ⟨b, hb⟩ := B_int X hv (smul_mem X.toData A.w0 hv)
  obtain ⟨c, hc⟩ := B_int X huv (smul_mem X.toData A.w0 huv)
  obtain ⟨d, hd⟩ := B_int X hu hv
  have h := A.T.eps_add (A.φ u) ((A.lat _).2 ⟨u, hu, rfl⟩) (A.φ v) ((A.lat _).2 ⟨v, hv, rfl⟩)
  have hd' := hd
  unfold B at hd'
  rw [← map_add, eps_val A hu ha, eps_val A hv hb, eps_val A huv hc, A.im_eq u hu v hv, hd',
    cos_sign A.sg_pm] at h
  have h1 : c.negOnePow = (a + b + d).negOnePow := by
    rw [Int.negOnePow_add, Int.negOnePow_add]
    ext
    push_cast
    exact_mod_cast h
  obtain ⟨k, hk⟩ := (Int.negOnePow_eq_iff _ _).1 h1
  refine ⟨k, ?_⟩
  rw [smul_add, B_add_left, B_add_right, B_add_right, ha, hb, B_swap X.toData _ u v] at hc
  have hk' : (c : ℚ) - (a + b + d) = k + k := by exact_mod_cast hk
  rw [B_sub_smul]
  linarith

end GlobalTheory.SemicharIndep

namespace GlobalTheory

open SemicharIndep in

theorem torusAt_eps_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ (x x' : Frame X.Ψ r) (A : TorusAt X.toData x) (A' : TorusAt X.toData x') (γ : GL (Fin r) E), IsUStab X.Gm X.Λ γ → ∀ v ∈ X.Λ, A'.T.eps (A'.φ ((γ : Matrix (Fin r) (Fin r) E).mulVec v)) = A.T.eps (A.φ v) := by
  intro E _ _ _ r X _ x x' A A' γ hγ v hv
  obtain ⟨a, ha⟩ := B_int X hv (smul_mem X.toData A.w0 hv)
  obtain ⟨b, hb⟩ := B_int X hv (smul_mem X.toData A'.w0 hv)
  have hb' : B X.toData ((γ : Matrix (Fin r) (Fin r) E).mulVec v)
      ((A'.w0 : E) • (γ : Matrix (Fin r) (Fin r) E).mulVec v) = b := by
    rw [← hb, B, B, ← Matrix.mulVec_smul, hγ.1]
  rw [eps_val A hv ha, eps_val A' ((hγ.2 v).1 hv) hb']
  obtain ⟨k, hk⟩ := parity_eq X (par_of_torusAt X A') (par_of_torusAt X A) hv
  rw [ha, hb] at hk
  have hk' : b - a = 2 * k := by exact_mod_cast hk
  rw [(Int.negOnePow_eq_iff b a).2 ⟨k, by omega⟩]

end GlobalTheory
