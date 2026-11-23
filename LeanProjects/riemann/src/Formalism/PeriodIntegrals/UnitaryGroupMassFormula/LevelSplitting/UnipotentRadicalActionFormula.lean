import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ReflectionFixesNormal

noncomputable section

namespace PI.LevelKSplit.W.NCH

open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

def Xp (D : Dat A n r) (v : n → A) : Prop := ∀ a, D.h (D.e a) v = 0

def IsWp (D : Dat A n r) (w : n → A) : Prop :=
  (∀ a, D.h (D.e a) w = 0) ∧ ∀ a, D.h (D.f a) w = 0

def pWp (D : Dat A n r) : (n → A) →ₗ[A] (n → A) := LinearMap.id - D.pX - D.pXv

structure Half (D : Dat A n r) (half : A) : Prop where
  two : half + half = 1
  sig : D.σA half = half

def cf (D : Dat A n r) (half : A) (y : Fin r → n → A) (a b : Fin r) : A :=
  -(half * D.h (y b) (y a))

def uv (D : Dat A n r) (half : A) (y : Fin r → n → A) (a : Fin r) : n → A :=
  y a + ∑ b, cf D half y a b • D.e b

def sL (D : Dat A n r) (half : A) (y : Fin r → n → A) : (n → A) →ₗ[A] (n → A) :=
  LinearMap.id + ∑ a, (D.hL (D.e a)).smulRight (uv D half y a) -
    ∑ b, (D.hL (y b)).smulRight (D.e b)

def tV (D : Dat A n r) (half : A) (y : Fin r → n → A) (v : n → A) : n → A :=
  ∑ a, D.h (D.e a) v • uv D half y a - ∑ b, D.h (y b) v • D.e b

private theorem hLap_lemma (D : Dat A n r) (x v : n → A) : D.hL x v = D.h x v := rfl

theorem sL_apply (D : Dat A n r) (half : A) (y : Fin r → n → A) (v : n → A) :
    sL D half y v = v + ∑ a, D.h (D.e a) v • uv D half y a - ∑ b, D.h (y b) v • D.e b := by
  simp only [sL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, hLap_lemma]

theorem sL_eq (D : Dat A n r) (half : A) (y : Fin r → n → A) (v : n → A) :
    sL D half y v = v + tV D half y v := by
  simp only [sL_apply, tV, add_sub_assoc]

theorem pWp_apply (D : Dat A n r) (v : n → A) : pWp D v = v - D.pX v - D.pXv v := rfl

variable {D : Dat A n r}

private theorem hRadd_lemma_2 (x y y' : n → A) : D.h x (y + y') = D.h x y + D.h x y' := by
  show (D.hL x) (y + y') = (D.hL x) y + (D.hL x) y'
  exact map_add _ _ _

private theorem hRsub_lemma_3 (x y y' : n → A) : D.h x (y - y') = D.h x y - D.h x y' := by
  show (D.hL x) (y - y') = (D.hL x) y - (D.hL x) y'
  exact map_sub _ _ _

private theorem hRsmul_lemma_4 (x y : n → A) (c : A) : D.h x (c • y) = c * D.h x y := by
  show (D.hL x) (c • y) = c * (D.hL x) y
  rw [map_smul, smul_eq_mul]

private theorem hRsum_lemma_5 (x : n → A) (g : Fin r → n → A) :
    D.h x (∑ i, g i) = ∑ i, D.h x (g i) := by
  show (D.hL x) (∑ i, g i) = ∑ i, (D.hL x) (g i)
  exact map_sum _ _ _

private theorem hswap_lemma_6 (H : D.Hyp) (x y : n → A) : D.h y x = D.σA (D.h x y) := by
  simp only [Dat.h, Formalism.UG.hform, map_sum, map_mul, H.σσ, H.herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem hfe_lemma_7 (H : D.Hyp) (a b : Fin r) :
    D.h (D.f a) (D.e b) = if a = b then 1 else 0 := by
  rw [hswap_lemma_6 H (D.e b) (D.f a), H.ef b a]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

private theorem hLsum_lemma_8 (H : D.Hyp) (g : Fin r → n → A) (y : n → A) :
    D.h (∑ i, g i) y = ∑ i, D.h (g i) y := by
  rw [hswap_lemma_6 H, hRsum_lemma_5, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hswap_lemma_6 H _ _).symm

private theorem hLsub_lemma_9 (H : D.Hyp) (x x' y : n → A) :
    D.h (x - x') y = D.h x y - D.h x' y := by
  rw [hswap_lemma_6 H y (x - x'), hRsub_lemma_3, map_sub, ← hswap_lemma_6 H, ← hswap_lemma_6 H]

private theorem pXap_lemma_10 (v : n → A) : D.pX v = ∑ a, D.h (D.f a) v • D.e a := by
  simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, hLap_lemma]

private theorem pXvap_lemma_11 (v : n → A) : D.pXv v = ∑ a, D.h (D.e a) v • D.f a := by
  simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hLap_lemma]

theorem h_W_e' (H : D.Hyp) {w : n → A} (hw : IsWp D w) (b : Fin r) : D.h w (D.e b) = 0 := by
  unfold IsWp at hw
  rw [hswap_lemma_6 H, hw.1 b, map_zero]

theorem h_W_f' (H : D.Hyp) {w : n → A} (hw : IsWp D w) (b : Fin r) : D.h w (D.f b) = 0 := by
  unfold IsWp at hw
  rw [hswap_lemma_6 H, hw.2 b, map_zero]

theorem xp_of_span (H : D.Hyp) {x : n → A} (hx : x ∈ Submodule.span A (Set.range D.e)) : Xp D x := by
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  intro a
  simp [hRsum_lemma_5, hRsmul_lemma_4, H.ee]

theorem h_W_span' (H : D.Hyp) {w : n → A} (hw : IsWp D w) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : D.h w x = 0 := by
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  simp [hRsum_lemma_5, hRsmul_lemma_4, h_W_e' H hw]

theorem xp_add {v w : n → A} (hv : Xp D v) (hw : Xp D w) : Xp D (v + w) := by
  intro a
  rw [hRadd_lemma_2, hv a, hw a, add_zero]

theorem xp_sub {v w : n → A} (hv : Xp D v) (hw : Xp D w) : Xp D (v - w) := by
  intro a
  rw [hRsub_lemma_3, hv a, hw a, sub_zero]

theorem xp_sub_pXv (H : D.Hyp) (v : n → A) : Xp D (v - D.pXv v) := by
  intro a
  rw [hRsub_lemma_3, pXvap_lemma_11, hRsum_lemma_5]
  simp [hRsmul_lemma_4, H.ef]

theorem xp_e (H : D.Hyp) (c : Fin r) : Xp D (D.e c) := by
  intro a
  exact H.ee a c

theorem pWp_isWp (H : D.Hyp) (v : n → A) : IsWp D (pWp D v) := by
  unfold IsWp
  refine ⟨fun a => ?_, fun a => ?_⟩ <;>
    simp [pWp_apply, pXap_lemma_10, pXvap_lemma_11, hRsub_lemma_3, hRsum_lemma_5, hRsmul_lemma_4, H.ee, H.ff, H.ef,
      hfe_lemma_7 H]

theorem pWp_of_isWp {w : n → A} (hw : IsWp D w) : pWp D w = w := by
  unfold IsWp at hw
  obtain ⟨h1, h2⟩ := hw
  simp [pWp_apply, pXap_lemma_10, pXvap_lemma_11, h1, h2]

theorem pWp_span (H : D.Hyp) {x : n → A} (hx : x ∈ Submodule.span A (Set.range D.e)) :
    pWp D x = 0 := by
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  simp [pWp_apply, pXap_lemma_10, pXvap_lemma_11, hRsum_lemma_5, hRsmul_lemma_4, H.ee, hfe_lemma_7 H]

theorem pWp_e (H : D.Hyp) (c : Fin r) : pWp D (D.e c) = 0 := pWp_span H (Submodule.subset_span ⟨c, rfl⟩)

theorem pWp_f (H : D.Hyp) (c : Fin r) : pWp D (D.f c) = 0 := by
  simp [pWp_apply, pXap_lemma_10, pXvap_lemma_11, H.ff, H.ef]

private theorem hy1_lemma_12 {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a)) (a b : Fin r) :
    D.h (D.e b) (y a) = 0 := by
  have h1 := hy a
  unfold IsWp at h1
  exact h1.1 b

private theorem hy2_lemma_13 (H : D.Hyp) {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a)) (a b : Fin r) :
    D.h (y a) (D.e b) = 0 :=
  h_W_e' H (hy a) b

private theorem hy3_lemma_14 (H : D.Hyp) {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a)) (a b : Fin r) :
    D.h (y a) (D.f b) = 0 :=
  h_W_f' H (hy a) b

theorem ext_Xp_f (H : D.Hyp) {Φ Ψ : (n → A) →ₗ[A] (n → A)} (h1 : ∀ v, Xp D v → Φ v = Ψ v)
    (h2 : ∀ a, Φ (D.f a) = Ψ (D.f a)) (v : n → A) : Φ v = Ψ v := by
  have e1 : v = (v - D.pXv v) + D.pXv v := (sub_add_cancel v _).symm
  rw [e1, map_add, map_add, h1 _ (xp_sub_pXv H v)]
  congr 1
  simp only [pXvap_lemma_11, map_sum, map_smul, h2]

section Sec

variable (H : D.Hyp) {half : A} {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a))
include H hy

theorem h_e_uv (a c : Fin r) : D.h (D.e c) (uv D half y a) = 0 := by
  simp [uv, hRadd_lemma_2, hRsum_lemma_5, hRsmul_lemma_4, H.ee, hy1_lemma_12 hy]

theorem h_uv_e (a c : Fin r) : D.h (uv D half y a) (D.e c) = 0 := by
  rw [hswap_lemma_6 H, h_e_uv H hy, map_zero]

theorem h_uv_uv (a a' : Fin r) : D.h (uv D half y a) (uv D half y a') = D.h (y a) (y a') := by
  simp [uv, hRadd_lemma_2, hRsum_lemma_5, hRsmul_lemma_4, h_add_left, hLsum_lemma_8 H, h_smul_left, H.ee,
    hy1_lemma_12 hy, hy2_lemma_13 H hy]

theorem sL_e (c : Fin r) : sL D half y (D.e c) = D.e c := by
  simp [sL_apply, H.ee, hy2_lemma_13 H hy]

theorem sL_f (c : Fin r) : sL D half y (D.f c) = D.f c + uv D half y c := by
  simp [sL_apply, H.ef, hy3_lemma_14 H hy]

theorem sL_Xp {v : n → A} (hv : Xp D v) : sL D half y v = v - ∑ b, D.h (y b) v • D.e b := by
  have hv' : ∀ a, D.h (D.e a) v = 0 := hv
  simp [sL_apply, hv']

theorem sL_span {x : n → A} (hx : x ∈ Submodule.span A (Set.range D.e)) : sL D half y x = x := by
  rw [sL_Xp H hy (xp_of_span H hx)]
  have hz : ∀ b, D.h (y b) x = 0 := fun b => h_W_span' H (hy b) hx
  simp [hz]

theorem pWp_sL_f (c : Fin r) : pWp D (sL D half y (D.f c)) = y c := by
  rw [sL_f H hy, map_add, pWp_f H, zero_add, uv, map_add, pWp_of_isWp (hy c), map_sum]
  simp [pWp_e H]

theorem h_tV_right (x x' : n → A) :
    D.h x (tV D half y x') = ∑ a, D.h (D.e a) x' * D.σA (D.h (y a) x) +
      ∑ a, ∑ b, D.h (D.e a) x' * (cf D half y a b * D.σA (D.h (D.e b) x)) -
      ∑ b, D.h (y b) x' * D.σA (D.h (D.e b) x) := by
  have sw : ∀ z, D.h x z = D.σA (D.h z x) := fun z => hswap_lemma_6 H z x
  simp only [tV, uv, hRsub_lemma_3, hRsum_lemma_5, hRsmul_lemma_4, hRadd_lemma_2]
  simp only [sw, mul_add, Finset.mul_sum, Finset.sum_add_distrib]

theorem h_tV_left (x x' : n → A) :
    D.h (tV D half y x) x' = ∑ a, D.σA (D.h (D.e a) x) * D.h (y a) x' +
      ∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.σA (cf D half y a b) * D.h (D.e b) x') -
      ∑ b, D.σA (D.h (y b) x) * D.h (D.e b) x' := by
  simp only [tV, uv, hLsub_lemma_9 H, hLsum_lemma_8 H, h_smul_left, h_add_left, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]

theorem h_tV_tV (x x' : n → A) :
    D.h (tV D half y x) (tV D half y x') =
      ∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.h (D.e b) x' * D.h (y a) (y b)) := by
  have k1 : ∀ b, D.h (D.e b) (tV D half y x') = 0 := fun b => by
    simp only [tV, hRsub_lemma_3, hRsum_lemma_5, hRsmul_lemma_4, h_e_uv H hy, H.ee, mul_zero,
      Finset.sum_const_zero, sub_self]
  have k2 : ∀ a, D.h (uv D half y a) (tV D half y x') =
      ∑ b, D.h (D.e b) x' * D.h (y a) (y b) := fun a => by
    simp only [tV, hRsub_lemma_3, hRsum_lemma_5, hRsmul_lemma_4, h_uv_uv H hy, h_uv_e H hy, mul_zero,
      Finset.sum_const_zero, sub_zero]
  rw [show tV D half y x = ∑ a, D.h (D.e a) x • uv D half y a - ∑ b, D.h (y b) x • D.e b from rfl]
  simp only [hLsub_lemma_9 H, hLsum_lemma_8 H, h_smul_left, k1, k2, mul_zero, Finset.sum_const_zero,
    sub_zero, Finset.mul_sum]

theorem sL_uni (hh : Half D half) (x x' : n → A) : D.h (sL D half y x) (sL D half y x') = D.h x x' := by
  have e1 := h_tV_right H hy (half := half) x x'
  have e2 := h_tV_left H hy (half := half) x x'
  have e3 := h_tV_tV H hy (half := half) x x'
  rw [sL_eq, sL_eq, h_add_left, hRadd_lemma_2, hRadd_lemma_2, e1, e2, e3]
  have c1 : ∑ a, D.h (D.e a) x' * D.σA (D.h (y a) x) =
      ∑ b, D.σA (D.h (y b) x) * D.h (D.e b) x' :=
    Finset.sum_congr rfl fun a _ => mul_comm _ _
  have c2 : ∑ b, D.h (y b) x' * D.σA (D.h (D.e b) x) =
      ∑ a, D.σA (D.h (D.e a) x) * D.h (y a) x' :=
    Finset.sum_congr rfl fun a _ => mul_comm _ _
  have c3 : (∑ a, ∑ b, D.h (D.e a) x' * (cf D half y a b * D.σA (D.h (D.e b) x))) +
      (∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.σA (cf D half y a b) * D.h (D.e b) x')) +
      (∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.h (D.e b) x' * D.h (y a) (y b))) = 0 := by
    rw [Finset.sum_comm (f := fun a b => D.h (D.e a) x' * (cf D half y a b * D.σA (D.h (D.e b) x)))]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    simp only [cf, map_neg, map_mul, hh.sig]
    rw [← hswap_lemma_6 H (y b) (y a)]
    linear_combination (-(D.σA (D.h (D.e a) x) * D.h (D.e b) x' * D.h (y a) (y b))) * hh.two
  linear_combination c1 - c2 + c3

end Sec

theorem unipotent_radical_action_formula (H : D.Hyp) {Φ : (n → A) →ₗ[A] (n → A)} (hU : D.Uni Φ) (he : ∀ a, Φ (D.e a) = D.e a)
    (hP : ∀ v, Xp D v → Φ v - v ∈ Submodule.span A (Set.range D.e)) {v : n → A} (hv : Xp D v) :
    Φ v = v - ∑ a, D.h (pWp D (Φ (D.f a))) v • D.e a := by
  have hv' : ∀ a, D.h (D.e a) v = 0 := hv
  have hm := hP v hv
  rw [Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  have hΦv : Φ v = v + ∑ a, c a • D.e a := by rw [hc]; abel
  have key : ∀ b, c b = -D.h (pWp D (Φ (D.f b))) v := by
    intro b
    have hwe : ∀ a, D.h (Φ (D.f b)) (D.e a) = if b = a then 1 else 0 := by
      intro a
      rw [← he a, hU (D.f b) (D.e a), hfe_lemma_7 H]
    have hew : ∀ a, D.h (D.e a) (Φ (D.f b)) = if a = b then 1 else 0 := by
      intro a
      rw [← he a, hU (D.e a) (D.f b), H.ef]
    have hpXv : D.pXv (Φ (D.f b)) = D.f b := by
      rw [pXvap_lemma_11]
      simp [hew]
    have hpX0 : D.h (D.pX (Φ (D.f b))) v = 0 := by
      rw [pXap_lemma_10, hLsum_lemma_8 H]
      simp [h_smul_left, hv']
    have hw_v : D.h (Φ (D.f b)) v = D.h (D.f b) v + D.h (pWp D (Φ (D.f b))) v := by
      have hdec : Φ (D.f b) = D.pX (Φ (D.f b)) + D.pXv (Φ (D.f b)) + pWp D (Φ (D.f b)) := by
        rw [pWp_apply]; abel
      conv_lhs => rw [hdec]
      rw [h_add_left, h_add_left, hpX0, hpXv, zero_add]
    have hUv := hU (D.f b) v
    rw [hΦv, hRadd_lemma_2, hRsum_lemma_5, hw_v] at hUv
    simp [hRsmul_lemma_4, hwe] at hUv
    linear_combination hUv
  rw [hΦv, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [key a, neg_smul]

def ND (D : Dat A n r) : Prop := ∀ x : n → A, (∀ v, D.h v x = 0) → x = 0

theorem fix_f_mem (H : D.Hyp) (hND : ND D) {Φ : (n → A) →ₗ[A] (n → A)} (hU : D.Uni Φ)
    (hfix : ∀ v, Xp D v → Φ v = v) (a : Fin r) :
    Φ (D.f a) - D.f a ∈ Submodule.span A (Set.range D.e) := by
  obtain ⟨w, hw⟩ : ∃ w, w = Φ (D.f a) - D.f a := ⟨_, rfl⟩
  rw [← hw]
  have hv_w : ∀ v, Xp D v → D.h w v = 0 := by
    intro v hv
    have h1 := hU (D.f a) v
    rw [hfix v hv] at h1
    rw [hw, hLsub_lemma_9 H, h1, sub_self]
  have hew : ∀ b, D.h (D.e b) w = 0 := by
    intro b
    have h1 := hU (D.e b) (D.f a)
    rw [hfix (D.e b) (xp_e H b)] at h1
    rw [hw, hRsub_lemma_3, h1, sub_self]
  have hpXv : D.pXv w = 0 := by
    rw [pXvap_lemma_11]
    simp [hew]
  have hdec : w = D.pX w + pWp D w := by
    rw [pWp_apply, hpXv]; abel
  have hpX0 : ∀ v, Xp D v → D.h (D.pX w) v = 0 := by
    intro v hv
    have hv' : ∀ b, D.h (D.e b) v = 0 := hv
    rw [pXap_lemma_10, hLsum_lemma_8 H]
    simp [h_smul_left, hv']
  have hP0 : pWp D w = 0 := by
    apply hND
    intro u
    have hW := pWp_isWp H w
    unfold IsWp at hW
    obtain ⟨-, hWf⟩ := hW
    have hu : u = (u - D.pXv u) + D.pXv u := (sub_add_cancel u _).symm
    rw [hu, h_add_left]
    have hvX := xp_sub_pXv H u
    have hA : D.h (pWp D w) (u - D.pXv u) = 0 := by
      have := hv_w _ hvX
      rw [hdec, h_add_left, hpX0 _ hvX, zero_add] at this
      exact this
    have hB : D.h (u - D.pXv u) (pWp D w) = 0 := by
      rw [hswap_lemma_6 H, hA, map_zero]
    have hC : D.h (D.pXv u) (pWp D w) = 0 := by
      rw [pXvap_lemma_11, hLsum_lemma_8 H]
      simp [h_smul_left, hWf]
    rw [hB, hC, add_zero]
  rw [hdec, hP0, add_zero, pXap_lemma_10]
  exact sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

end PI.LevelKSplit.W.NCH
