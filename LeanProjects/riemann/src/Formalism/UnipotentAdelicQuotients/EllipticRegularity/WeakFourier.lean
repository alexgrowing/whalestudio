import Formalism.UnipotentAdelicQuotients.EllRegCut

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

namespace WF

variable {d : ℕ}

def ev (L : List (List (Fin d) × (E d → ℂ))) (g : E d → ℂ) (y : E d) : ℂ :=
  (L.map fun p => p.2 y * dw p.1 g y).sum

def Good (k : ℕ) (K : Set (E d)) (L : List (List (Fin d) × (E d → ℂ))) : Prop :=
  ∀ p ∈ L, p.1.length < k ∧ ContDiff ℝ ∞ p.2 ∧ ∀ y ∉ K, p.2 y = 0

def Dk (k : Fin d) (f : E d → ℂ) : E d → ℂ := fun y => fderiv ℝ f y (ZetaZeros.D.EllReg.ev k)

theorem dw_cons (k : Fin d) (w : List (Fin d)) (f : E d → ℂ) : dw (k :: w) f = Dk k (dw w f) := rfl

private theorem contDiff_fderiv'_lemma_2 {f : ZetaZeros.D.EllReg.E d → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fderiv ℝ f) := by
  exact (contDiff_infty_iff_fderiv.mp hf).2

theorem contDiff_Dk {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) (k : Fin d) : ContDiff ℝ ∞ (Dk k f) := by
  exact (contDiff_fderiv'_lemma_2 hf).clm_apply contDiff_const

theorem contDiff_dw {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : ∀ w : List (Fin d), ContDiff ℝ ∞ (dw w f)
  | [] => hf
  | k :: w => contDiff_Dk (contDiff_dw hf w) k

theorem Dk_zero_off {f : E d → ℂ} {K : Set (E d)} (hK : IsClosed K) (hf : ∀ y ∉ K, f y = 0) (k : Fin d) :
    ∀ y ∉ K, Dk k f y = 0 := by
  intro y hy
  have h : f =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hy] with z hz
    exact hf z hz
  show fderiv ℝ f y (ZetaZeros.D.EllReg.ev k) = 0
  rw [h.fderiv_eq]
  simp

private theorem differentiable_of_contDiff'_lemma {f : ZetaZeros.D.EllReg.E d → ℂ} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  exact (contDiff_infty_iff_fderiv.mp hf).1

theorem Dk_add {f g : E d → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : Fin d) (y : E d) :
    Dk k (fun z => f z + g z) y = Dk k f y + Dk k g y := by
  have H := ((differentiable_of_contDiff'_lemma hf y).hasFDerivAt.add (differentiable_of_contDiff'_lemma hg y).hasFDerivAt).fderiv
  show fderiv ℝ (f + g) y (ZetaZeros.D.EllReg.ev k) = fderiv ℝ f y (ZetaZeros.D.EllReg.ev k) + fderiv ℝ g y (ZetaZeros.D.EllReg.ev k)
  rw [H]
  rfl

theorem Dk_mul {f g : E d → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : Fin d) (y : E d) :
    Dk k (fun z => f z * g z) y = Dk k f y * g y + f y * Dk k g y := by
  have H := ((differentiable_of_contDiff'_lemma hf y).hasFDerivAt.mul (differentiable_of_contDiff'_lemma hg y).hasFDerivAt).fderiv
  show fderiv ℝ (f * g) y (ZetaZeros.D.EllReg.ev k) = fderiv ℝ f y (ZetaZeros.D.EllReg.ev k) * g y + f y * fderiv ℝ g y (ZetaZeros.D.EllReg.ev k)
  rw [H]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem contDiff_ev {L : List (List (Fin d) × (E d → ℂ))} (hL : ∀ p ∈ L, ContDiff ℝ ∞ p.2)
    {g : E d → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (ev L g) := by
  revert hL
  induction L with
  | nil =>
    intro _
    have h0 : ev ([] : List (List (Fin d) × (ZetaZeros.D.EllReg.E d → ℂ))) g = fun _ => 0 := by
      funext y; simp only [ev, List.map_nil, List.sum_nil]
    rw [h0]; exact contDiff_const
  | cons p L ih =>
    intro hL
    have h1 : ev (p :: L) g = fun y => p.2 y * ZetaZeros.D.EllReg.dw p.1 g y + ev L g y := by
      funext y; simp only [ev, List.map_cons, List.sum_cons]
    rw [h1]
    exact ((hL p (by simp)).mul (contDiff_dw hg p.1)).add (ih fun q hq => hL q (by simp [hq]))

theorem ev_cons (p : List (Fin d) × (E d → ℂ)) (L : List (List (Fin d) × (E d → ℂ))) (g : E d → ℂ) (y : E d) :
    ev (p :: L) g y = p.2 y * dw p.1 g y + ev L g y := by
  simp only [ev, List.map_cons, List.sum_cons]

theorem ev_nil (g : E d → ℂ) (y : E d) : ev ([] : List (List (Fin d) × (E d → ℂ))) g y = 0 := by
  simp only [ev, List.map_nil, List.sum_nil]

theorem ev_append (L1 L2 : List (List (Fin d) × (E d → ℂ))) (g : E d → ℂ) (y : E d) :
    ev (L1 ++ L2) g y = ev L1 g y + ev L2 g y := by
  simp only [ev, List.map_append, List.sum_append]

def sc (C : E d → ℂ) (L : List (List (Fin d) × (E d → ℂ))) : List (List (Fin d) × (E d → ℂ)) :=
  L.map fun p => (p.1, fun y => C y * p.2 y)

theorem ev_sc (C : E d → ℂ) (L : List (List (Fin d) × (E d → ℂ))) (g : E d → ℂ) (y : E d) :
    ev (sc C L) g y = C y * ev L g y := by
  induction L with
  | nil => simp only [sc, List.map_nil, ev_nil, mul_zero]
  | cons p L ih =>
    have h1 : sc C (p :: L) = (p.1, fun z => C z * p.2 z) :: sc C L := rfl
    rw [h1]
    simp only [ev_cons, ih]
    ring

theorem Dk_ev {L : List (List (Fin d) × (E d → ℂ))} (hL : ∀ p ∈ L, ContDiff ℝ ∞ p.2)
    {g : E d → ℂ} (hg : ContDiff ℝ ∞ g) (k : Fin d) (y : E d) :
    Dk k (ev L g) y = ev (L.map fun p => (p.1, Dk k p.2)) g y + ev (L.map fun p => (k :: p.1, p.2)) g y := by
  revert hL
  induction L with
  | nil =>
    intro _
    have h0 : ev ([] : List (List (Fin d) × (ZetaZeros.D.EllReg.E d → ℂ))) g = fun _ => 0 := by
      funext z; simp only [ev, List.map_nil, List.sum_nil]
    rw [h0]
    simp [Dk, ev]
  | cons p L ih =>
    intro hL
    have hp : ContDiff ℝ ∞ p.2 := hL p (by simp)
    have hL' : ∀ q ∈ L, ContDiff ℝ ∞ q.2 := fun q hq => hL q (by simp [hq])
    have h1 : ev (p :: L) g = fun z => p.2 z * ZetaZeros.D.EllReg.dw p.1 g z + ev L g z := by
      funext z; exact ev_cons p L g z
    rw [h1, Dk_add (hp.mul (contDiff_dw hg p.1)) (contDiff_ev hL' hg) k y,
      Dk_mul hp (contDiff_dw hg p.1) k y, ih hL']
    simp only [List.map_cons, ev_cons, dw_cons]
    ring

def lb : List (Fin d) → (E d → ℂ) → List (List (Fin d) × (E d → ℂ))
  | [], _ => []
  | k :: w, f => (w, Dk k f) :: ((lb w f).map (fun p => (p.1, Dk k p.2)) ++ (lb w f).map (fun p => (k :: p.1, p.2)))

theorem lb_good {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) {K : Set (E d)} (hK : IsClosed K)
    (hfK : ∀ y ∉ K, f y = 0) : ∀ w : List (Fin d), Good w.length K (lb w f)
  | [] => by intro p hp; simp [lb] at hp
  | k :: w => by
    have ih := lb_good hf hK hfK w
    intro p hp
    simp only [lb, List.mem_cons, List.mem_append, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨by simp, contDiff_Dk hf k, Dk_zero_off hK hfK k⟩
    · obtain ⟨h1, h2, h3⟩ := ih q hq
      exact ⟨by simp; omega, contDiff_Dk h2 k, Dk_zero_off hK h3 k⟩
    · obtain ⟨h1, h2, h3⟩ := ih q hq
      exact ⟨by simp; omega, h2, h3⟩

theorem leib {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : ∀ (w : List (Fin d)) (g : E d → ℂ), ContDiff ℝ ∞ g →
    dw w (fun z => f z * g z) = fun y => f y * dw w g y + ev (lb w f) g y
  | [], g, hg => by funext y; simp [dw, lb, ev]
  | k :: w, g, hg => by
    have hgood := lb_good hf isClosed_univ (by simp) w
    have hc : ∀ p ∈ lb w f, ContDiff ℝ ∞ p.2 := fun p hp => (hgood p hp).2.1
    funext y
    rw [dw_cons, leib hf w g hg, Dk_add (hf.mul (contDiff_dw hg w)) (contDiff_ev hc hg),
      Dk_mul hf (contDiff_dw hg w), Dk_ev hc hg]
    simp only [lb, ev_cons, ev_append, dw_cons]
    ring

def sb (a : E d → ℂ) : List (List (Fin d) × (E d → ℂ)) → List (List (Fin d) × (E d → ℂ))
  | [] => []
  | p :: L => (p.1, fun y => p.2 y * a y) :: (sc p.2 (lb p.1 a) ++ sb a L)

theorem ev_sb {a : E d → ℂ} (ha : ContDiff ℝ ∞ a) {e : E d → ℂ} (he : ContDiff ℝ ∞ e) (y : E d) :
    ∀ L : List (List (Fin d) × (E d → ℂ)), ev L (fun z => a z * e z) y = ev (sb a L) e y
  | [] => by simp [ev, sb]
  | p :: L => by
    rw [ev_cons, ev_sb ha he y L, leib ha p.1 e he]
    simp only [sb, ev_cons, ev_append, ev_sc]
    ring

theorem sb_good {a : E d → ℂ} (ha : ContDiff ℝ ∞ a) {k : ℕ} {K : Set (E d)} :
    ∀ L : List (List (Fin d) × (E d → ℂ)), Good k K L → Good k K (sb a L)
  | [], _ => by intro p hp; simp [sb] at hp
  | p :: L, hL => by
    have hp := hL p (by simp)
    have ih := sb_good ha L (fun q hq => hL q (by simp [hq]))
    have hlb := lb_good ha isClosed_univ (by simp) p.1
    intro q hq
    simp only [sb, sc, List.mem_cons, List.mem_append, List.mem_map] at hq
    rcases hq with rfl | ⟨r, hr, rfl⟩ | hq
    · exact ⟨hp.1, hp.2.1.mul ha, fun y hy => by simp [hp.2.2 y hy]⟩
    · obtain ⟨h1, h2, -⟩ := hlb r hr
      exact ⟨lt_trans h1 hp.1, hp.2.1.mul h2, fun y hy => by simp [hp.2.2 y hy]⟩
    · exact ih q hq

theorem good_mono {k k' : ℕ} {K : Set (E d)} {L : List (List (Fin d) × (E d → ℂ))} (hL : Good k K L)
    (hk : k ≤ k') : Good k' K L := by
  intro p hp
  obtain ⟨h1, h2⟩ := hL p hp
  exact ⟨lt_of_lt_of_le h1 hk, h2⟩

def cf (L : List (List (Fin d) × (E d → ℂ))) (n : ℕ) (w : Fin n → Fin d) (y : E d) : ℂ :=
  (L.map fun p => if p.1 = List.ofFn w then p.2 y else 0).sum

theorem cf_good {k : ℕ} {K : Set (E d)} {L : List (List (Fin d) × (E d → ℂ))} (hL : Good k K L)
    (n : ℕ) (w : Fin n → Fin d) : ContDiff ℝ ∞ (cf L n w) ∧ ∀ y ∉ K, cf L n w y = 0 := by
  revert hL
  induction L with
  | nil =>
    intro _
    have h0 : cf ([] : List (List (Fin d) × (ZetaZeros.D.EllReg.E d → ℂ))) n w = fun _ => 0 := by
      funext y; simp only [cf, List.map_nil, List.sum_nil]
    rw [h0]; exact ⟨contDiff_const, fun _ _ => rfl⟩
  | cons p L ih =>
    intro hL
    have hp := hL p (by simp)
    have hL' : Good k K L := by
      intro r hr; exact hL r (by simp [hr])
    obtain ⟨ih1, ih2⟩ := ih hL'
    have h1 : cf (p :: L) n w = fun y => (if p.1 = List.ofFn w then p.2 y else 0) + cf L n w y := by
      funext y; simp only [cf, List.map_cons, List.sum_cons]
    rw [h1]
    constructor
    · refine ContDiff.add ?_ ih1
      by_cases hc : p.1 = List.ofFn w
      · simp only [if_pos hc]; exact hp.2.1
      · simp only [if_neg hc]; exact contDiff_const
    · intro y hy
      show (if p.1 = List.ofFn w then p.2 y else 0) + cf L n w y = 0
      rw [ih2 y hy]
      by_cases hc : p.1 = List.ofFn w
      · simp [if_pos hc, hp.2.2 y hy]
      · simp [if_neg hc]

theorem single_term {m : ℕ} (p : List (Fin d) × (E d → ℂ)) (hp : p.1.length < m) (g : E d → ℂ) (y : E d) :
    ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d,
      (if p.1 = List.ofFn w then p.2 y else 0) * dw (List.ofFn w) g y = p.2 y * dw p.1 g y := by
  obtain ⟨v, c⟩ := p
  dsimp only at hp ⊢
  have key : ∀ (n : ℕ) (w : Fin n → Fin d), (if v = List.ofFn w then c y else 0) * ZetaZeros.D.EllReg.dw (List.ofFn w) g y
      = if v = List.ofFn w then c y * ZetaZeros.D.EllReg.dw v g y else 0 := by
    intro n w
    by_cases h : v = List.ofFn w
    · rw [if_pos h, if_pos h, h]
    · rw [if_neg h, if_neg h, zero_mul]
  simp only [key]
  rw [Finset.sum_eq_single v.length]
  · rw [Finset.sum_eq_single v.get]
    · rw [if_pos (List.ofFn_get v).symm]
    · intro w _ hw
      rw [if_neg]
      intro h
      apply hw
      have h' : List.ofFn w = List.ofFn v.get := by rw [← h, List.ofFn_get]
      exact List.ofFn_injective h'
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro n _ hn
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg]
    intro h
    apply hn
    rw [h, List.length_ofFn]
  · intro h
    exact absurd (Finset.mem_range.mpr hp) h

theorem ev_eq_cf {m : ℕ} (g : E d → ℂ) (y : E d) : ∀ L : List (List (Fin d) × (E d → ℂ)),
    (∀ p ∈ L, p.1.length < m) →
    ev L g y = ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, cf L n w y * dw (List.ofFn w) g y
  | [], _ => by simp [ev, cf]
  | p :: L, hL => by
    rw [ev_cons, ev_eq_cf g y L (fun q hq => hL q (by simp [hq])), ← single_term p (hL p (by simp)) g y,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w _
    simp only [cf, List.map_cons, List.sum_cons]
    ring

theorem dw_congr {F G : E d → ℂ} : ∀ (v : List (Fin d)) (y : E d), F =ᶠ[𝓝 y] G → dw v F =ᶠ[𝓝 y] dw v G
  | [], _, h => h
  | k :: v, y, h => by
    have ih := dw_congr v y h
    filter_upwards [ih.eventuallyEq_nhds] with x hx
    simp only [dw_cons, Dk, hx.fderiv_eq]

theorem contDiff_ofReal' {χ : E d → ℝ} (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (fun y => (χ y : ℂ)) := by
  have h := Complex.ofRealCLM.contDiff.comp hχ
  have e : (Complex.ofRealCLM ∘ χ) = fun y => (χ y : ℂ) := by
    funext y; simp
  rw [e] at h
  exact h

theorem smooth_cut {U : Set (E d)} (hU : IsOpen U) {a : E d → ℂ} (ha : ContDiffOn ℝ ∞ a U)
    {χ : E d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun y => (χ y : ℂ) * a y) := by
  have hz0 : ∀ z, z ∉ tsupport χ → χ z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport χ (Function.mem_support.mpr h))
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (contDiff_ofReal' hχ).contDiffAt.mul (ha.contDiffAt (hU.mem_nhds hx))
  · have hxs : x ∉ tsupport χ := fun h => hx (hχU h)
    have hev : (fun y => (χ y : ℂ) * a y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxs] with z hz
      simp [hz0 z hz]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem intg {U K : Set (E d)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {u F : E d → ℂ}
    (hu : ContinuousOn u U) (hF : Continuous F) (hFK : ∀ y ∉ K, F y = 0) :
    Integrable (fun y => u y * F y) := by
  have hKc : IsClosed K := hK.isClosed
  have hcont : Continuous (fun y => u y * F y) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hu.continuousAt (hU.mem_nhds hx)).mul hF.continuousAt
    · have hxK : x ∉ K := fun h => hx (hKU h)
      have hev : (fun _ => (0 : ℂ)) =ᶠ[𝓝 x] fun y => u y * F y := by
        filter_upwards [hKc.isOpen_compl.mem_nhds hxK] with z hz
        simp [hFK z hz]
      exact continuousAt_const.congr hev
  have hcs : HasCompactSupport (fun y => u y * F y) := by
    apply HasCompactSupport.intro hK
    intro y hy
    simp [hFK y hy]
  exact hcont.integrable_of_hasCompactSupport hcs

theorem swap4 {α : Type*} [AddCommMonoid α] (s t : Finset ℕ)
    (f : (n : ℕ) → (Fin n → Fin d) → (n' : ℕ) → (Fin n' → Fin d) → α) :
    ∑ n ∈ s, ∑ w : Fin n → Fin d, ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, f n w n' w' =
      ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, ∑ n ∈ s, ∑ w : Fin n → Fin d, f n w n' w' := by
  calc ∑ n ∈ s, ∑ w : Fin n → Fin d, ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, f n w n' w'
      = ∑ n ∈ s, ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, ∑ w : Fin n → Fin d, f n w n' w' := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun n' _ => Finset.sum_comm)
    _ = ∑ n' ∈ t, ∑ n ∈ s, ∑ w' : Fin n' → Fin d, ∑ w : Fin n → Fin d, f n w n' w' := Finset.sum_comm
    _ = ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, ∑ n ∈ s, ∑ w : Fin n → Fin d, f n w n' w' :=
        Finset.sum_congr rfl (fun n' _ => Finset.sum_comm)

private theorem formalAdjoint_mul_expand_lemma_3 {m : ℕ} {B : (n : ℕ) → (Fin n → Fin d) → ZetaZeros.D.EllReg.E d → ℂ}
    (hB : ∀ n w, ContDiff ℝ ∞ (B n w)) {a φ : ZetaZeros.D.EllReg.E d → ℂ} (ha : ContDiff ℝ ∞ a) (hφ : ContDiff ℝ ∞ φ) (y : ZetaZeros.D.EllReg.E d) :
    ZetaZeros.D.EllReg.trOp m B (fun z => a z * φ z) y = a y * ZetaZeros.D.EllReg.trOp m B φ y +
      ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
        (-1 : ℂ) ^ n * ev (sb (B n w) (lb (List.ofFn w) a)) φ y := by
  have key : ∀ (n : ℕ) (w : Fin n → Fin d), ZetaZeros.D.EllReg.dw (List.ofFn w) (fun z => B n w z * (a z * φ z)) y =
      a y * ZetaZeros.D.EllReg.dw (List.ofFn w) (fun z => B n w z * φ z) y +
        ev (sb (B n w) (lb (List.ofFn w) a)) φ y := by
    intro n w
    have e1 : (fun z => B n w z * (a z * φ z)) = fun z => a z * (B n w z * φ z) := by
      funext z; ring
    rw [e1, leib ha (List.ofFn w) _ ((hB n w).mul hφ)]
    simp only [ev_sb (hB n w) hφ y]
  simp only [ZetaZeros.D.EllReg.trOp, key, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro w _
  ring

private theorem continuous_formalAdjoint_lemma_4 {m : ℕ} {B : (n : ℕ) → (Fin n → Fin d) → ZetaZeros.D.EllReg.E d → ℂ}
    (hB : ∀ n w, ContDiff ℝ ∞ (B n w)) {φ : ZetaZeros.D.EllReg.E d → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (ZetaZeros.D.EllReg.trOp m B φ) := by
  have e : ZetaZeros.D.EllReg.trOp m B φ = fun x => ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
      (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.dw (List.ofFn w) (fun y => B n w y * φ y) x := by
    funext x; rfl
  rw [e]
  refine continuous_finsetSum _ (fun n _ => continuous_finsetSum _ (fun w _ => ?_))
  exact continuous_const.mul (contDiff_dw ((hB n w).mul hφ) _).continuous

private theorem formalAdjoint_congr_at_lemma_5 {m : ℕ} {b b' : (n : ℕ) → (Fin n → Fin d) → ZetaZeros.D.EllReg.E d → ℂ} {φ : ZetaZeros.D.EllReg.E d → ℂ}
    {y : ZetaZeros.D.EllReg.E d} (h : ∀ n w, b n w =ᶠ[𝓝 y] b' n w) : ZetaZeros.D.EllReg.trOp m b φ y = ZetaZeros.D.EllReg.trOp m b' φ y := by
  unfold ZetaZeros.D.EllReg.trOp
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro w _
  congr 1
  apply Filter.EventuallyEq.eq_of_nhds
  apply dw_congr
  filter_upwards [h n w] with z hz
  rw [hz]

theorem contDiff_eF (ξ : E d) : ContDiff ℝ ∞ (eF ξ) := by
  have h1 : ContDiff ℝ ∞ (fun y : ZetaZeros.D.EllReg.E d => (inner ℝ y ξ : ℝ)) := by
    exact contDiff_id.inner ℝ contDiff_const
  have h2 := contDiff_ofReal' h1
  have h3 : ContDiff ℝ ∞ (fun y : ZetaZeros.D.EllReg.E d => -(2 * Real.pi * Complex.I * ((inner ℝ y ξ : ℝ) : ℂ))) :=
    (contDiff_const.mul h2).neg
  exact h3.cexp

end WF

open WF in
theorem weakEquationFourier : WeakFourier := by
  intro d ι _ P U u hE i χ χ' hχ hχc hχU hχ' hχ'c hχ'U hχχ'
  obtain ⟨hU, hcoef, -, hu, hweak⟩ := hE
  have hKcl : IsClosed (tsupport χ) := isClosed_tsupport χ
  have hKc : IsCompact (tsupport χ) := hχc.isCompact
  have hz0 : ∀ z, z ∉ tsupport χ → χ z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport χ (Function.mem_support.mpr h))
  have hone : ∀ z ∈ tsupport χ, χ' z = 1 := fun z hz => (hχχ' z hz).eq_of_nhds
  obtain ⟨a, ha_def⟩ : ∃ a : E d → ℂ, a = fun z => (χ z : ℂ) := ⟨_, rfl⟩
  have ha : ContDiff ℝ ∞ a := by rw [ha_def]; exact ZetaZeros.D.EllReg.WF.contDiff_ofReal' hχ
  have haK : ∀ z ∉ tsupport χ, a z = 0 := fun z hz => by rw [ha_def]; simp [hz0 z hz]
  obtain ⟨B, hB_def⟩ : ∃ B : (n : ℕ) → (Fin n → Fin d) → E d → ℂ,
      B = fun n w z => (χ' z : ℂ) * P.a i n w z := ⟨_, rfl⟩
  have hB : ∀ n w, ContDiff ℝ ∞ (B n w) := by
    intro n w; rw [hB_def]; exact ZetaZeros.D.EllReg.WF.smooth_cut hU (hcoef i n w) hχ' hχ'U
  have hBev : ∀ y ∈ tsupport χ, ∀ n w, P.a i n w =ᶠ[𝓝 y] B n w := by
    intro y hy n w
    filter_upwards [hχχ' y hy] with z hz
    rw [hB_def]; simp [hz]
  have hMadm : ∀ n ∈ Finset.range (P.ord i + 1), ∀ w : Fin n → Fin d,
      ZetaZeros.D.EllReg.WF.Good (P.ord i) (tsupport χ) (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) := by
    intro n hn w
    have h1 := ZetaZeros.D.EllReg.WF.sb_good (hB n w) _ (ZetaZeros.D.EllReg.WF.lb_good ha hKcl haK (List.ofFn w))
    rw [List.length_ofFn] at h1
    have hn' : n ≤ P.ord i := by have := Finset.mem_range.mp hn; omega
    exact (ZetaZeros.D.EllReg.WF.good_mono h1) hn'
  obtain ⟨c, hc_def⟩ : ∃ c : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, c = fun n' w' y =>
      -∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
        (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.WF.cf (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) n' w' y := ⟨_, rfl⟩
  have hc : ∀ n' (w' : Fin n' → Fin d), ContDiff ℝ ∞ (c n' w') := by
    intro n' w'
    rw [hc_def]
    apply ContDiff.neg
    apply ContDiff.sum; intro n hn
    apply ContDiff.sum; intro w _
    exact contDiff_const.mul (ZetaZeros.D.EllReg.WF.cf_good (hMadm n hn w) n' w').1
  have hc0 : ∀ n' (w' : Fin n' → Fin d), ∀ y ∉ tsupport χ, c n' w' y = 0 := by
    intro n' w' y hy
    simp only [hc_def, neg_eq_zero]
    apply Finset.sum_eq_zero; intro n hn
    apply Finset.sum_eq_zero; intro w _
    rw [(ZetaZeros.D.EllReg.WF.cf_good (hMadm n hn w) n' w').2 y hy, mul_zero]
  refine ⟨c, fun n' w' => ⟨hc n' w', HasCompactSupport.intro hKc (hc0 n' w')⟩, fun ξ => ?_⟩
  have hφ := ZetaZeros.D.EllReg.WF.contDiff_eF ξ
  obtain ⟨ψ, hψ_def⟩ : ∃ ψ : E d → ℂ, ψ = fun z => a z * eF ξ z := ⟨_, rfl⟩
  have hψs : ContDiff ℝ ∞ ψ := by rw [hψ_def]; exact ha.mul hφ
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.intro hKc (fun z hz => by rw [hψ_def]; simp [haK z hz])
  have hψU : tsupport ψ ⊆ U := by
    refine subset_trans ?_ hχU
    refine closure_minimal ?_ hKcl
    intro z hz
    by_contra hzK
    exact (Function.mem_support.mp hz) (by rw [hψ_def]; simp [haK z hzK])
  have hint_r : ∫ x, u x * P.tr i ψ x = 0 := hweak i ψ hψs hψc hψU
  have hψB : ∀ y, P.tr i ψ y = trOp (P.ord i) B ψ y := by
    intro y
    show trOp (P.ord i) (P.a i) ψ y = _
    unfold trOp
    apply Finset.sum_congr rfl; intro n _
    apply Finset.sum_congr rfl; intro w _
    have e : (fun z => P.a i n w z * ψ z) = fun z => B n w z * ψ z := by
      funext z
      by_cases hz : z ∈ tsupport χ
      · rw [hB_def]; simp [hone z hz]
      · rw [hψ_def]; simp [haK z hz]
    rw [e]
  have hL : ∀ y, cut χ u y * P.tr i (eF ξ) y =
      u y * (a y * trOp (P.ord i) B (eF ξ) y) := by
    intro y
    by_cases hy : y ∈ tsupport χ
    · have e : P.tr i (eF ξ) y = trOp (P.ord i) B (eF ξ) y := by
        show trOp (P.ord i) (P.a i) (eF ξ) y = _
        exact _root_.ZetaZeros.D.EllReg.WF.formalAdjoint_congr_at_lemma_5 (hBev y hy)
      rw [e, ha_def]
      simp only [cut]
      ring
    · have h0 : χ y = 0 := hz0 y hy
      rw [ha_def]
      simp [cut, h0]
  have hR : ∀ y, ∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
      (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.WF.ev (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) (eF ξ) y =
      -∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
        c n' w' y * dw (List.ofFn w') (eF ξ) y := by
    intro y
    have h1 : ∀ n ∈ Finset.range (P.ord i + 1), ∀ w : Fin n → Fin d,
        (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.WF.ev (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) (eF ξ) y =
        ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
          (-1 : ℂ) ^ n * (ZetaZeros.D.EllReg.WF.cf (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) n' w' y *
            dw (List.ofFn w') (eF ξ) y) := by
      intro n hn w
      rw [ZetaZeros.D.EllReg.WF.ev_eq_cf (eF ξ) y _ (fun p hp => (hMadm n hn w p hp).1), Finset.mul_sum]
      apply Finset.sum_congr rfl; intro n' _
      rw [Finset.mul_sum]
    calc ∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
          (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.WF.ev (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) (eF ξ) y
        = ∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
            ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
              (-1 : ℂ) ^ n * (ZetaZeros.D.EllReg.WF.cf (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) n' w' y *
                dw (List.ofFn w') (eF ξ) y) := by
          apply Finset.sum_congr rfl; intro n hn
          apply Finset.sum_congr rfl; intro w _
          exact h1 n hn w
      _ = ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
            ∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
              (-1 : ℂ) ^ n * (ZetaZeros.D.EllReg.WF.cf (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) n' w' y *
                dw (List.ofFn w') (eF ξ) y) := ZetaZeros.D.EllReg.WF.swap4 _ _ _
      _ = -∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
            c n' w' y * dw (List.ofFn w') (eF ξ) y := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro n' _
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro w' _
          rw [hc_def]
          simp only [Finset.sum_mul, neg_mul, neg_neg, mul_assoc]
  have hpt : ∀ y, u y * P.tr i ψ y = u y * (a y * trOp (P.ord i) B (eF ξ) y) -
      ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
        u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) := by
    intro y
    rw [hψB y, hψ_def, _root_.ZetaZeros.D.EllReg.WF.formalAdjoint_mul_expand_lemma_3 hB ha hφ y, hR y, mul_add, mul_neg, sub_eq_add_neg,
      Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl; intro n' _
    rw [Finset.mul_sum]
  have hG : Integrable (fun y => u y * (a y * trOp (P.ord i) B (eF ξ) y)) :=
    ZetaZeros.D.EllReg.WF.intg hU hKc hχU hu
      (ha.continuous.mul (_root_.ZetaZeros.D.EllReg.WF.continuous_formalAdjoint_lemma_4 hB hφ)) (fun y hy => by simp [haK y hy])
  have hH : ∀ n' (w' : Fin n' → Fin d),
      Integrable (fun y => u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y)) :=
    fun n' w' => ZetaZeros.D.EllReg.WF.intg hU hKc hχU hu
      ((hc n' w').continuous.mul (ZetaZeros.D.EllReg.WF.contDiff_dw hφ _).continuous) (fun y hy => by simp [hc0 n' w' y hy])
  have hmain : ∫ y, u y * (a y * trOp (P.ord i) B (eF ξ) y) =
      ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
        ∫ y, u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) := by
    have e := hint_r
    rw [show (fun x => u x * P.tr i ψ x) = fun y =>
        u y * (a y * trOp (P.ord i) B (eF ξ) y) -
          ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
            u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) from funext hpt] at e
    rw [integral_sub hG (integrable_finsetSum _ fun n' _ => integrable_finsetSum _ fun w' _ => hH n' w'),
      integral_finsetSum _ (fun n' _ => integrable_finsetSum _ fun w' _ => hH n' w')] at e
    have e2 : ∀ n' ∈ Finset.range (P.ord i), ∫ y, ∑ w' : Fin n' → Fin d,
        u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) =
        ∑ w' : Fin n' → Fin d, ∫ y, u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) :=
      fun n' _ => integral_finsetSum _ (fun w' _ => hH n' w')
    rw [Finset.sum_congr rfl e2] at e
    exact sub_eq_zero.mp e
  calc ∫ y, cut χ u y * P.tr i (eF ξ) y
      = ∫ y, u y * (a y * trOp (P.ord i) B (eF ξ) y) := by
        congr 1; funext y; exact hL y
    _ = ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
          ∫ y, u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) := hmain
    _ = ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
          ∫ y, cut χ' u y * c n' w' y * dw (List.ofFn w') (eF ξ) y := by
        apply Finset.sum_congr rfl; intro n' _
        apply Finset.sum_congr rfl; intro w' _
        congr 1; funext y
        by_cases hy : y ∈ tsupport χ
        · simp only [cut, hone y hy, Complex.ofReal_one]
          ring
        · rw [hc0 n' w' y hy]
          simp

end

end ZetaZeros.D.EllReg
