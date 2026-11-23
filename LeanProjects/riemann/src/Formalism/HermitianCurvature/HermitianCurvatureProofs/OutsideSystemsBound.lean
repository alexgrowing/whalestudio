import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.Jx8

section psd
variable {α : Type} {F : Finset α}

theorem psd_congr {k k' : α → α → ℂ} (h : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) (hk : TB.PSDOn F k) :
    TB.PSDOn F k' := by
  unfold TB.PSDOn at *
  have : (Matrix.of fun x y : F => k' x y) = Matrix.of fun x y : F => k x y := by
    ext x y; exact (h x x.2 y y.2).symm
  rw [this]; exact hk

end psd

theorem ones_psd {α : Type} (F : Finset α) : TB.PSDOn F (fun _ _ : α => (1 : ℂ)) := by
  unfold TB.PSDOn
  have := Matrix.posSemidef_vecMulVec_self_star (fun _ : F => (1 : ℂ))
  convert this using 1
  ext x y; simp [Matrix.vecMulVec]

theorem zero_psd {α : Type} (F : Finset α) : TB.PSDOn F (fun _ _ : α => (0 : ℂ)) := by
  unfold TB.PSDOn; exact Matrix.PosSemidef.zero

theorem t_OutsideOk : OutsideOk := by
  intro E α _ L F
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro t t' h
    have : t ∈ L ↔ t' ∈ L := by
      constructor
      · intro ht; have := L.sub_mem ht h; simpa using this
      · intro ht; have := L.add_mem h ht; simpa using this
    simp [this]
  · intro t
    by_cases h : t ∈ L
    · simpa [h] using ones_psd F
    · simpa [h] using zero_psd F
  · intro R hR
    have hcard : (R.filter (fun t => t ∈ L)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      exact hR a ha.1 b hb.1 (L.sub_mem ha.2 hb.2)
    have hsum : (∑ t ∈ R, if t ∈ L then (1 : ℂ) else 0) = ((R.filter (fun t => t ∈ L)).card : ℂ) := by
      rw [Finset.sum_ite]; simp
    rw [hsum]
    interval_cases hc : (R.filter (fun t => t ∈ L)).card
    · simpa using ones_psd F
    · simpa using zero_psd F

theorem t_ScaleOk (hD : DiagScale) : ScaleOk := by
  intro E α _ a S F h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t t' ht ht' x hx y hy hne
    apply h1 t t' ht ht' x hx y hy
    intro h0; apply hne; simp [scaleSys, h0]
  · intro t ht; exact hD _ _ _ a (h2 t ht)
  · intro t t' htt x hx y hy
    simp only [scaleSys]; rw [h3 t t' htt x hx y hy]
  · intro t; exact hD _ _ _ a (h4 t)
  · intro t ht
    have := hD _ _ _ a (h5 t ht)
    convert this using 3
    simp only [scaleSys]; ring
  · intro R hR
    have := hD _ _ _ a (h6 R hR)
    convert this using 3
    simp only [scaleSys]; rw [mul_sub, Finset.mul_sum]

theorem t_DiagScale : DiagScale := by
  intro α F k a h
  classical
  unfold TB.PSDOn at h ⊢
  have := h.conjTranspose_mul_mul_same (Matrix.diagonal (fun x : F => ((a x : ℝ) : ℂ)))
  convert this using 1
  ext x y
  simp [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

section agree
variable {α : Type}

theorem quadM (F : Finset α) (k : α → α → ℂ) (a : α → ℂ) :
    star (fun x : F => a x) ⬝ᵥ (Matrix.of fun x y : F => k x y) *ᵥ (fun x : F => a x) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  rw [← Finset.sum_coe_sort F (fun x => ∑ y ∈ F, conj (a x) * k x y * a y)]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.sum_coe_sort F (fun y => conj (a x) * k x y * a y)]
  apply Finset.sum_congr rfl; intro y _
  simp only [RCLike.star_def]; ring

theorem conj_quad (F : Finset α) (k : α → α → ℂ) (hh : ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y)) (a : α → ℂ) :
    conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) = ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
  rw [map_sum, Finset.sum_comm]
  simp only [map_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x hx
  apply Finset.sum_congr rfl; intro y hy
  rw [map_mul, map_mul, Complex.conj_conj, ← hh y hy x hx]; ring

theorem tb_iff_ta (F : Finset α) (k : α → α → ℂ) : TB.PSDOn F k ↔ TA.PSDOn F k := by
  classical
  unfold TB.PSDOn TA.PSDOn
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨hH, hp⟩
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      have := congrFun (congrFun hH ⟨y, hy⟩) ⟨x, hx⟩
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def] at this
      exact this.symm
    · intro a
      have := hp (fun x : F => a x)
      rw [quadM] at this
      exact (Complex.le_def.1 this).1
  · rintro ⟨hh, hp⟩
    refine ⟨?_, ?_⟩
    · ext x y
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
      exact (hh y y.2 x x.2).symm
    · intro x
      let a : α → ℂ := fun z => if h : z ∈ F then x ⟨z, h⟩ else 0
      have hx : x = fun z : F => a z := by
        ext z; simp [a]
      rw [hx, quadM]
      rw [Complex.le_def]
      refine ⟨hp a, ?_⟩
      have := conj_quad F k hh a
      rw [Complex.conj_eq_iff_im] at this
      simpa using this.symm

theorem quad1 [DecidableEq α] (F : Finset α) (k : α → α → ℂ) (x : α) (hx : x ∈ F) :
    ∑ u ∈ F, ∑ v ∈ F, (if u = x then (1 : ℂ) else 0) * conj (if v = x then (1 : ℂ) else 0) * k u v = k x x := by
  rw [Finset.sum_eq_single x (fun u _ hu => by simp [hu]) (fun h => absurd hx h)]
  rw [Finset.sum_eq_single x (fun v _ hv => by simp [hv]) (fun h => absurd hx h)]
  simp

theorem quad2 [DecidableEq α] (F : Finset α) (k : α → α → ℂ) (x y : α) (hx : x ∈ F) (hy : y ∈ F)
    (hxy : x ≠ y) (c : ℂ) :
    ∑ u ∈ F, ∑ v ∈ F, (if u = x then (1 : ℂ) else if u = y then c else 0) *
        conj (if v = x then (1 : ℂ) else if v = y then c else 0) * k u v =
      k x x + conj c * k x y + c * k y x + c * conj c * k y y := by
  have hsub : ({x, y} : Finset α) ⊆ F := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have h0 : ∀ u, u ∉ ({x, y} : Finset α) → (if u = x then (1 : ℂ) else if u = y then c else 0) = 0 := by
    intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
    simp [hu.1, hu.2]
  rw [← Finset.sum_subset hsub (fun u _ hu => by simp [h0 u hu])]
  have inner : ∀ u, ∑ v ∈ F, (if u = x then (1 : ℂ) else if u = y then c else 0) *
        conj (if v = x then (1 : ℂ) else if v = y then c else 0) * k u v =
      ∑ v ∈ ({x, y} : Finset α), (if u = x then (1 : ℂ) else if u = y then c else 0) *
        conj (if v = x then (1 : ℂ) else if v = y then c else 0) * k u v := fun u =>
    (Finset.sum_subset hsub (fun v _ hv => by simp [h0 v hv])).symm
  simp only [inner]
  rw [Finset.sum_pair hxy, Finset.sum_pair hxy, Finset.sum_pair hxy]
  simp [hxy.symm]
  ring

theorem isPSD_iff_psdOn (F : Finset α) (k : α → α → ℂ) : A5.IsPSD F k ↔ TA.PSDOn F k := by
  classical
  unfold A5.IsPSD TA.PSDOn
  constructor
  · intro h
    have hd : ∀ x ∈ F, (k x x).im = 0 := by
      intro x hx
      have := (h (fun u => if u = x then (1 : ℂ) else 0)).1
      rwa [quad1 F k x hx] at this
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      by_cases hxy : x = y
      · subst hxy
        exact ((Complex.conj_eq_iff_im).2 (hd x hx)).symm
      · have h1 := (h (fun u => if u = x then (1 : ℂ) else if u = y then 1 else 0)).1
        rw [quad2 F k x y hx hy hxy 1] at h1
        have h2 := (h (fun u => if u = x then (1 : ℂ) else if u = y then Complex.I else 0)).1
        rw [quad2 F k x y hx hy hxy Complex.I] at h2
        simp [hd x hx, hd y hy] at h1 h2
        apply Complex.ext
        · simp; linarith
        · simp; linarith
    · intro a
      have := (h (fun u => conj (a u))).2
      have e : ∑ x ∈ F, ∑ y ∈ F, conj (a x) * conj (conj (a y)) * k x y =
          ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro y _
        rw [Complex.conj_conj]; ring
      rwa [e] at this
  · rintro ⟨hh, hp⟩ a
    have e : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y =
        ∑ x ∈ F, ∑ y ∈ F, conj (conj (a x)) * k x y * conj (a y) := by
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      rw [Complex.conj_conj]; ring
    rw [e]
    refine ⟨?_, hp (fun u => conj (a u))⟩
    have := conj_quad F k hh (fun u => conj (a u))
    rwa [Complex.conj_eq_iff_im] at this
end agree

section
variable {α : Type}

theorem psdOn_iff_isPSD (F : Finset α) (k : α → α → ℂ) : TB.PSDOn F k ↔ A5.IsPSD F k :=
  (tb_iff_ta F k).trans (isPSD_iff_psdOn F k).symm

theorem psd_mono {F G : Finset α} (h : F ⊆ G) {k : α → α → ℂ} (hk : TB.PSDOn G k) : TB.PSDOn F k := by
  unfold TB.PSDOn at *
  exact hk.submatrix (fun x : F => (⟨x.1, h x.2⟩ : G))

theorem psd_diag {F : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn F k) {x : α} (hx : x ∈ F) :
    (k x x).im = 0 ∧ 0 ≤ (k x x).re := by
  classical
  have h2 := (psdOn_iff_isPSD F k).1 hk (fun u => if u = x then 1 else 0)
  have h1 := quad1 F k x hx
  beta_reduce at h2
  rw [h1] at h2
  exact h2

theorem psd_off {F : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn F k) {x y : α} (hx : x ∈ F) (hy : y ∈ F) :
    ‖k x y‖ ≤ (k x x).re + (k y y).re := by
  classical
  obtain ⟨ix, rx⟩ := psd_diag hk hx
  obtain ⟨iy, ry⟩ := psd_diag hk hy
  have hn := Complex.norm_le_abs_re_add_abs_im (k x y)
  by_cases hxy : x = y
  · subst hxy
    rw [ix, abs_zero, add_zero, abs_of_nonneg rx] at hn
    linarith
  · have hherm : k y x = conj (k x y) := ((tb_iff_ta F k).1 hk).1 x hx y hy
    have q := fun c : ℂ => ((psdOn_iff_isPSD F k).1 hk (fun u => if u = x then 1 else if u = y then c else 0)).2
    have e := fun c : ℂ => quad2 F k x y hx hy hxy c
    have q1 := q 1
    have q2 := q (-1)
    have q3 := q Complex.I
    have q4 := q (-Complex.I)
    beta_reduce at q1 q2 q3 q4
    rw [e, hherm] at q1 q2 q3 q4
    simp at q1 q2 q3 q4
    have a1 : |(k x y).re| ≤ ((k x x).re + (k y y).re) / 2 := by
      rw [abs_le]; constructor <;> linarith
    have a2 : |(k x y).im| ≤ ((k x x).re + (k y y).re) / 2 := by
      rw [abs_le]; constructor <;> linarith
    linarith

theorem closed_and {X : Type} [TopologicalSpace X] {p q : X → Prop} (hp : IsClosed {x | p x})
    (hq : IsClosed {x | q x}) : IsClosed {x | p x ∧ q x} := hp.inter hq

theorem closed_psd {X : Type} [TopologicalSpace X] (F : Finset α) (g : X → α → α → ℂ)
    (hg : ∀ x y, Continuous fun T => g T x y) : IsClosed {T | TB.PSDOn F (g T)} := by
  simp only [psdOn_iff_isPSD, A5.IsPSD, Set.ofPred_forall]
  refine isClosed_iInter fun a => ?_
  have hc : Continuous fun T => ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * g T x y :=
    continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ => continuous_const.mul (hg x y)
  exact closed_and (isClosed_eq (Complex.continuous_im.comp hc) continuous_const)
    (isClosed_le continuous_const (Complex.continuous_re.comp hc))

end

theorem ok_mono {E α : Type} [Field E] {S : LocSys E α} {F G : Finset α} (h : F ⊆ G) (hS : S.Ok G) :
    S.Ok F := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  exact ⟨fun t t' ht ht' x hx y hy => h1 t t' ht ht' x (h hx) y (h hy), fun t ht => psd_mono h (h2 t ht),
    fun t t' htt x hx y hy => h3 t t' htt x (h hx) y (h hy), fun t => psd_mono h (h4 t),
    fun t ht => psd_mono h (h5 t ht), fun R hR => psd_mono h (h6 R hR)⟩

theorem ok_congr {E α : Type} [Field E] {N : E → E → α → α → ℂ} {B : α → α → ℂ} {L L' : AddSubgroup E}
    {Th Th' : E → α → α → ℂ} {F : Finset α}
    (h : ∀ t, ∀ x ∈ F, ∀ y ∈ F, Th t x y = Th' t x y) (hS : (LocSys.mk N Th B L L').Ok F) :
    (LocSys.mk N Th' B L L').Ok F := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  refine ⟨h1, h2, fun t t' htt x hx y hy => ?_, fun t => psd_congr (h t) (h4 t),
    fun t ht => psd_congr (fun x hx y hy => ?_) (h5 t ht),
    fun R hR => psd_congr (fun x hx y hy => ?_) (h6 R hR)⟩
  · show Th' t x y = Th' t' x y
    rw [← h t x hx y hy, ← h t' x hx y hy]; exact h3 t t' htt x hx y hy
  · show Th t x y - N t t x y = Th' t x y - N t t x y
    rw [h t x hx y hy]
  · show B x y - ∑ t ∈ R, Th t x y = B x y - ∑ t ∈ R, Th' t x y
    rw [Finset.sum_congr rfl fun t _ => h t x hx y hy]

theorem t_UniformMajorant : UniformMajorant := by
  classical
  intro E α _ N B L L' hyp
  have hS : IsCompact (Set.pi Set.univ fun _ : E => Set.pi Set.univ fun h : α => Set.pi Set.univ fun h' : α =>
      Metric.closedBall (0 : ℂ) ((B h h).re + (B h' h').re)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun h => isCompact_univ_pi fun h' => isCompact_closedBall _ _
  have hcl : ∀ F : Finset α, IsClosed {Th : E → α → α → ℂ | (LocSys.mk N Th B L L').Ok F} := by
    intro F
    simp only [LocSys.Ok]
    refine closed_and isClosed_const (closed_and isClosed_const (closed_and ?_ (closed_and ?_
      (closed_and ?_ ?_))))
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun t => isClosed_iInter fun t' => isClosed_iInter fun _ =>
        isClosed_iInter fun h => isClosed_iInter fun _ => isClosed_iInter fun h' =>
        isClosed_iInter fun _ => isClosed_eq (by fun_prop) (by fun_prop)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun t => closed_psd F _ (fun x y => by fun_prop)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun t => isClosed_iInter fun _ => closed_psd F _ (fun x y => by fun_prop)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun R => isClosed_iInter fun _ => closed_psd F _ (fun x y => by fun_prop)
  have hdiag : ∀ (G : Finset α) (Th : E → α → α → ℂ), (LocSys.mk N Th B L L').Ok G → ∀ t, ∀ h ∈ G,
      0 ≤ (Th t h h).re ∧ (Th t h h).re ≤ (B h h).re := by
    intro G Th hOk t h hh
    simp only [LocSys.Ok] at hOk
    obtain ⟨_, _, _, h4, _, h6⟩ := hOk
    refine ⟨(psd_diag (h4 t) hh).2, ?_⟩
    have := (psd_diag (h6 {t} (by
      intro a ha b hb _; rw [mem_singleton.1 ha, mem_singleton.1 hb])) hh).2
    simp only [sum_singleton, Complex.sub_re] at this
    linarith
  have hB : ∀ h, 0 ≤ (B h h).re := by
    intro h
    obtain ⟨Th, hOk⟩ := hyp {h}
    have := hdiag {h} Th hOk 0 h (mem_singleton_self h)
    linarith [this.1, this.2]
  have key := hS.inter_iInter_nonempty
    (fun F : Finset α => {Th : E → α → α → ℂ | (LocSys.mk N Th B L L').Ok F}) hcl ?_
  · obtain ⟨Th, _, hTh⟩ := key
    exact ⟨Th, fun F => Set.mem_iInter.1 hTh F⟩
  · intro u
    obtain ⟨Th, hOk⟩ := hyp (u.biUnion id)
    have hOk' : (LocSys.mk N (fun t h h' => if h ∈ u.biUnion id ∧ h' ∈ u.biUnion id then Th t h h' else 0)
        B L L').Ok (u.biUnion id) :=
      ok_congr (fun t x hx y hy => by rw [if_pos ⟨hx, hy⟩]) hOk
    refine ⟨_, ?_, Set.mem_iInter₂.2 fun F hF => ok_mono (subset_biUnion_of_mem id hF) hOk'⟩
    intro t _ h _ h' _
    rw [mem_closedBall_zero_iff]
    beta_reduce
    by_cases hc : h ∈ u.biUnion id ∧ h' ∈ u.biUnion id
    · rw [if_pos hc]
      have hOk2 := hOk
      simp only [LocSys.Ok] at hOk2
      have a0 := psd_off (hOk2.2.2.2.1 t) hc.1 hc.2
      have a1 := (hdiag _ Th hOk t h hc.1).2
      have a2 := (hdiag _ Th hOk t h' hc.2).2
      linarith
    · rw [if_neg hc, norm_zero]; exact add_nonneg (hB h) (hB h')

theorem psd_pull {α β : Type} {G : Finset β} {F : Finset α} (f : G → F) {k : α → α → ℂ}
    {k' : β → β → ℂ} (h : ∀ x y : G, k' x y = k (f x) (f y)) (hk : TB.PSDOn F k) : TB.PSDOn G k' := by
  unfold TB.PSDOn at *
  have e : (Matrix.of fun x y : G => k' x y) = (Matrix.of fun x y : F => k x y).submatrix f f := by
    ext x y; exact h x y
  rw [e]; exact hk.submatrix f

theorem t_UniformMajorantOn : UniformMajorantOn := by
  classical
  intro E α _ A N B L L' hyp
  obtain ⟨Th', hTh'⟩ := t_UniformMajorant E {h // h ∈ A} (fun t t' h h' => N t t' h.1 h'.1)
    (fun h h' => B h.1 h'.1) L L' (by
    intro F'
    obtain ⟨Th, h1, h2, h3, h4, h5, h6⟩ := hyp (F'.image Subtype.val) (by
      intro h hh; obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hh; exact x.2)
    have hm : ∀ x ∈ F', (x : α) ∈ F'.image Subtype.val := fun x hx => Finset.mem_image_of_mem _ hx
    let f : F' → (F'.image Subtype.val : Finset α) := fun x => ⟨x.1.1, hm x.1 x.2⟩
    refine ⟨fun t h h' => Th t h.1 h'.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t t' ht ht' h hh h' hh' hne
      exact h1 t t' ht ht' h.1 (hm h hh) h'.1 (hm h' hh') hne
    · intro t ht; exact psd_pull f (fun _ _ => rfl) (h2 t ht)
    · intro t t' htt h hh h' hh'; exact h3 t t' htt h.1 (hm _ hh) h'.1 (hm _ hh')
    · intro t; exact psd_pull f (fun _ _ => rfl) (h4 t)
    · intro t ht; exact psd_pull f (fun _ _ => rfl) (h5 t ht)
    · intro R hR; exact psd_pull f (fun _ _ => rfl) (h6 R hR))
  let Th : E → α → α → ℂ := fun t h h' =>
    if hh : h ∈ A ∧ h' ∈ A then Th' t ⟨h, hh.1⟩ ⟨h', hh.2⟩ else 0
  have hT : ∀ t x y (hx : x ∈ A) (hy : y ∈ A), Th t x y = Th' t ⟨x, hx⟩ ⟨y, hy⟩ :=
    fun t x y hx hy => dif_pos ⟨hx, hy⟩
  have hz : ∀ t x y, ¬ (x ∈ A ∧ y ∈ A) → Th t x y = 0 := fun t x y h => dif_neg h
  have part1 : ∀ F : Finset α, (∀ h ∈ F, h ∈ A) → (LocSys.mk N Th B L L').Ok F := by
    intro F hF
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hTh' (F.subtype (· ∈ A))
    let f : F → (F.subtype (· ∈ A) : Finset {h // h ∈ A}) :=
      fun x => ⟨⟨x.1, hF x.1 x.2⟩, Finset.mem_subtype.2 x.2⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t t' ht ht' h hh h' hh' hne
      exact g1 t t' ht ht' ⟨h, hF h hh⟩ (Finset.mem_subtype.2 hh) ⟨h', hF h' hh'⟩
        (Finset.mem_subtype.2 hh') hne
    · intro t ht; exact psd_pull f (fun _ _ => rfl) (g2 t ht)
    · intro t t' htt h hh h' hh'
      show Th t h h' = Th t' h h'
      rw [hT t h h' (hF h hh) (hF h' hh'), hT t' h h' (hF h hh) (hF h' hh')]
      exact g3 t t' htt ⟨h, hF h hh⟩ (Finset.mem_subtype.2 hh) ⟨h', hF h' hh'⟩
        (Finset.mem_subtype.2 hh')
    · intro t
      exact psd_pull f (fun x y => hT t x.1 y.1 (hF x.1 x.2) (hF y.1 y.2)) (g4 t)
    · intro t ht
      refine psd_pull f (fun x y => ?_) (g5 t ht)
      show Th t x.1 y.1 - N t t x.1 y.1 = _
      rw [hT t x.1 y.1 (hF x.1 x.2) (hF y.1 y.2)]
    · intro R hR
      refine psd_pull f (fun x y => ?_) (g6 R hR)
      show B x.1 y.1 - ∑ t ∈ R, Th t x.1 y.1 = _
      rw [Finset.sum_congr rfl fun t _ => hT t x.1 y.1 (hF x.1 x.2) (hF y.1 y.2)]
  refine ⟨Th, part1, hz, ?_⟩
  intro t F
  have hA : ∀ h ∈ F.filter (· ∈ A), h ∈ A := fun h hh => (Finset.mem_filter.1 hh).2
  have hd : TB.PSDOn (F.filter (· ∈ A)) (Th t) := (part1 _ hA).2.2.2.1 t
  obtain ⟨q1, q2⟩ := (tb_iff_ta _ _).1 hd
  rw [tb_iff_ta]
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    by_cases h : x ∈ A ∧ y ∈ A
    · exact q1 x (Finset.mem_filter.2 ⟨hx, h.1⟩) y (Finset.mem_filter.2 ⟨hy, h.2⟩)
    · rw [hz t x y h, hz t y x (fun h' => h ⟨h'.2, h'.1⟩), map_zero]
  · intro a
    have inner : ∀ x, ∑ y ∈ F.filter (· ∈ A), conj (a x) * Th t x y * a y =
        ∑ y ∈ F, conj (a x) * Th t x y * a y := fun x =>
      Finset.sum_filter_of_ne (fun y _ hne => by
        by_contra hy
        exact hne (by rw [hz t x y (fun h => hy h.2)]; simp))
    have outer : ∑ x ∈ F.filter (· ∈ A), ∑ y ∈ F, conj (a x) * Th t x y * a y =
        ∑ x ∈ F, ∑ y ∈ F, conj (a x) * Th t x y * a y :=
      Finset.sum_filter_of_ne (fun x _ hne => by
        by_contra hx
        exact hne (Finset.sum_eq_zero fun y _ => by rw [hz t x y (fun h => hx h.1)]; simp))
    have := q2 a
    simp only [inner] at this
    rw [outer] at this
    exact this

theorem t_OutsideSysOk : OutsideSysOk := by
  intro E α _ N L L' F h1 h2 h3
  obtain ⟨o1, o2, o3⟩ := t_OutsideOk E α L F
  exact ⟨h1, h2, fun t t' htt h _ h' _ => o1 t t' htt, o2, h3, o3⟩

theorem t_OutsideDomination : OutsideDomination := by
  classical
  intro hPD E α P _ _ k L t F hk hd
  have := hPD α P F k (fun p _ _ => if t ∈ L p then (1 : ℂ) else 0) hk hd
  refine psd_congr (fun x _ y _ => ?_) this
  congr 1
  by_cases h : t ∈ ⨅ p, L p
  · rw [if_pos h]
    have h' : ∀ p, t ∈ L p := AddSubgroup.mem_iInf.1 h
    exact Finset.prod_eq_one fun p _ => if_pos (h' p)
  · rw [if_neg h]
    have : ∃ p, t ∉ L p := by
      by_contra hc
      exact h (AddSubgroup.mem_iInf.2 fun p => by_contra fun hp => hc ⟨p, hp⟩)
    obtain ⟨p, hp⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)

theorem t_PhaseOk : PhaseOk := by
  intro E α _ d S F hd hS
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  have hdd : ∀ t, d t * conj (d t) = 1 := by
    intro t
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hd]; simp
  refine ⟨?_, ?_, h3, h4, ?_, h6⟩
  · intro t t' ht ht' h hh h' hh' hne
    refine h1 t t' ht ht' h hh h' hh' (fun h0 => hne ?_)
    show d t * conj (d t') * S.N t t' h h' = 0
    rw [h0, mul_zero]
  · intro t ht
    refine psd_congr (fun x _ y _ => ?_) (h2 t ht)
    show S.N t t x y = d t * conj (d t) * S.N t t x y
    rw [hdd, one_mul]
  · intro t ht
    refine psd_congr (fun x _ y _ => ?_) (h5 t ht)
    show S.Th t x y - S.N t t x y = S.Th t x y - d t * conj (d t) * S.N t t x y
    rw [hdd, one_mul]

end Formalism.FourierDecayAlt.P.Jx8

namespace Formalism.FourierDecayAlt.P

theorem scaling_bound : Formalism.FourierDecayAlt.J.ScaleOk := Jx8.t_ScaleOk Jx8.t_DiagScale

theorem phaseOk_statement : Formalism.FourierDecayAlt.J.PhaseOk := Jx8.t_PhaseOk

theorem outside_bound : Formalism.FourierDecayAlt.J.OutsideOk := Jx8.t_OutsideOk

theorem outside_systems_bound : Formalism.FourierDecayAlt.J.OutsideSysOk := Jx8.t_OutsideSysOk

theorem outside_domination : Formalism.FourierDecayAlt.J.OutsideDomination := Jx8.t_OutsideDomination

theorem uniformMajorant_statement : Formalism.FourierDecayAlt.J.UniformMajorant := Jx8.t_UniformMajorant

theorem uniform_majorant_on : Formalism.FourierDecayAlt.J.UniformMajorantOn := Jx8.t_UniformMajorantOn

end Formalism.FourierDecayAlt.P
