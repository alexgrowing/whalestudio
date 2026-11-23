import Formalism.HermitianCurvature.StatementTC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelInequality
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelInequalitySplitBySize
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AntidiagMulDiagonal

namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical

section gen
variable {α : Type}

lemma psd_congr {P : Finset α} {k k' : α → α → ℂ} (h : ∀ x ∈ P, ∀ y ∈ P, k x y = k' x y)
    (hk : PSDOn P k) : PSDOn P k' := by
  unfold TA.PSDOn at hk ⊢
  refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
  · rw [← h x hx y hy, ← h y hy x hx]
    exact hk.1 x hx y hy
  · have e : ∑ x ∈ P, ∑ y ∈ P, conj (a x) * k' x y * a y =
        ∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y :=
      Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [h x hx y hy]
    rw [e]
    exact hk.2 a

lemma psd_mono {P Q : Finset α} {k : α → α → ℂ} (hQ : Q ⊆ P) (hk : PSDOn P k) : PSDOn Q k := by
  unfold TA.PSDOn at hk ⊢
  refine ⟨fun x hx y hy => hk.1 x (hQ hx) y (hQ hy), fun a => ?_⟩
  obtain ⟨b, hbQ, hb0⟩ : ∃ b : α → ℂ, (∀ x ∈ Q, b x = a x) ∧ ∀ x, x ∉ Q → b x = 0 :=
    ⟨fun x => if x ∈ Q then a x else 0, fun x hx => by simp [hx], fun x hx => by simp [hx]⟩
  have h := hk.2 b
  have e1 : ∀ x ∈ P, ∑ y ∈ P, conj (b x) * k x y * b y = ∑ y ∈ Q, conj (b x) * k x y * b y :=
    fun x _ => (Finset.sum_subset (f := fun y => conj (b x) * k x y * b y) hQ
      (fun y _ hy => by simp [hb0 y hy])).symm
  rw [Finset.sum_congr rfl e1] at h
  rw [← Finset.sum_subset (f := fun x => ∑ y ∈ Q, conj (b x) * k x y * b y) hQ
    (fun x _ hx => by simp [hb0 x hx])] at h
  have e2 : ∑ x ∈ Q, ∑ y ∈ Q, conj (b x) * k x y * b y =
      ∑ x ∈ Q, ∑ y ∈ Q, conj (a x) * k x y * a y :=
    Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [hbQ x hx, hbQ y hy]
  rw [e2] at h
  exact h

noncomputable def restr (X : Finset α) (k : α → α → ℂ) : α → α → ℂ :=
  fun x y => if x ∈ X ∧ y ∈ X then k x y else 0

lemma psd_restr (X Y : Finset α) {k : α → α → ℂ} (hk : PSDOn X k) : PSDOn Y (restr X k) := by
  have hU : PSDOn (X ∪ Y) (restr X k) := by
    unfold TA.PSDOn at hk ⊢
    refine ⟨fun x _ y _ => ?_, fun a => ?_⟩
    · unfold restr
      by_cases hx : x ∈ X
      · by_cases hy : y ∈ X
        · simp [hx, hy, hk.1 x hx y hy]
        · simp [hx, hy]
      · simp [hx]
    · have e : ∑ x ∈ X ∪ Y, ∑ y ∈ X ∪ Y, conj (a x) * restr X k x y * a y =
          ∑ x ∈ X, ∑ y ∈ X, conj (a x) * k x y * a y := by
        rw [← Finset.sum_subset (f := fun x => ∑ y ∈ X ∪ Y, conj (a x) * restr X k x y * a y)
          (fun z hz => Finset.mem_union_left _ hz) (fun x _ hx => by simp [restr, hx])]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [← Finset.sum_subset (f := fun y => conj (a x) * restr X k x y * a y)
          (fun z hz => Finset.mem_union_left _ hz) (fun y _ hy => by simp [restr, hy])]
        refine Finset.sum_congr rfl fun y hy => ?_
        simp [restr, hx, hy]
      rw [e]
      exact hk.2 a
  exact psd_mono (P := X ∪ Y) (fun z hz => Finset.mem_union_right _ hz) hU

lemma psd_zero (P : Finset α) : PSDOn P (fun _ _ => (0 : ℂ)) := by
  unfold TA.PSDOn
  exact ⟨fun _ _ _ _ => by simp, fun a => by simp⟩

lemma psd_add {P : Finset α} {k k' : α → α → ℂ} (hk : PSDOn P k) (hk' : PSDOn P k') :
    PSDOn P (fun x y => k x y + k' x y) := by
  unfold TA.PSDOn at hk hk' ⊢
  refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
  · simp only [hk.1 x hx y hy, hk'.1 x hx y hy, map_add]
  · have e : ∑ x ∈ P, ∑ y ∈ P, conj (a x) * (k x y + k' x y) * a y =
        (∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y) +
          ∑ x ∈ P, ∑ y ∈ P, conj (a x) * k' x y * a y := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [e, Complex.add_re]
    exact add_nonneg (hk.2 a) (hk'.2 a)

variable {E : Type} [AddCommGroup E]

lemma mk_eq_iff (L : AddSubgroup E) (x y : E) : ((x : E ⧸ L) = (y : E ⧸ L)) ↔ x - y ∈ L := by
  exact QuotientAddGroup.eq_iff_sub_mem

noncomputable def G (L : AddSubgroup E) (S : Finset E) (Th : E → α → α → ℂ) (c : E ⧸ L) : α → α → ℂ :=
  if hc : ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c then Th hc.choose else fun _ _ => 0

lemma G_cases (L : AddSubgroup E) (S : Finset E) (Th : E → α → α → ℂ) (c : E ⧸ L) :
    ((¬ ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c) ∧ G L S Th c = fun _ _ => 0) ∨
      ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c ∧ G L S Th c = Th t₁ := by
  by_cases hc : ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c
  · right
    refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, ?_⟩
    unfold G
    rw [dif_pos hc]
  · left
    refine ⟨hc, ?_⟩
    unfold G
    rw [dif_neg hc]

lemma G_sum (L : AddSubgroup E) (S : Finset E) (Th : E → α → α → ℂ) (R : Finset E)
    (hR : ∀ x ∈ R, ∀ y ∈ R, x - y ∈ L → x = y) :
    ∃ S' : Finset E, S' ⊆ S ∧ (∀ x ∈ S', ∃ t ∈ R, x - t ∈ L) ∧
      (∀ x ∈ S', ∀ y ∈ S', x - y ∈ L → x = y) ∧
      ∀ h h', ∑ t ∈ R, G L S Th (t : E ⧸ L) h h' = ∑ t₁ ∈ S', Th t₁ h h' := by
  let f : E → E := fun t => if hc : ∃ t₁ ∈ S, (t₁ : E ⧸ L) = (t : E ⧸ L) then hc.choose else t
  have hf : ∀ t : E, (∃ t₁ ∈ S, (t₁ : E ⧸ L) = (t : E ⧸ L)) → f t ∈ S ∧ (f t : E ⧸ L) = (t : E ⧸ L) := by
    intro t hc
    simp only [f, dif_pos hc]
    exact hc.choose_spec
  have hG : ∀ (t : E) (h h' : α), G L S Th (t : E ⧸ L) h h' =
      if (∃ t₁ ∈ S, (t₁ : E ⧸ L) = (t : E ⧸ L)) then Th (f t) h h' else 0 := by
    intro t h h'
    by_cases hc : ∃ t₁ ∈ S, (t₁ : E ⧸ L) = (t : E ⧸ L)
    · rw [if_pos hc]
      unfold G
      simp only [f, dif_pos hc]
    · rw [if_neg hc]
      unfold G
      simp only [dif_neg hc]
  let R' := R.filter fun t : E => ∃ t₁ ∈ S, (t₁ : E ⧸ L) = (t : E ⧸ L)
  have hinj : Set.InjOn f R' := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have e1 := (hf x hx'.2).2
    have e2 := (hf y hy'.2).2
    have : (x : E ⧸ L) = (y : E ⧸ L) := by rw [← e1, ← e2, hxy]
    exact hR x hx'.1 y hy'.1 ((mk_eq_iff L x y).mp this)
  refine ⟨R'.image f, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact (hf t (Finset.mem_filter.mp ht).2).1
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨t, (Finset.mem_filter.mp ht).1, (mk_eq_iff L _ _).mp (hf t (Finset.mem_filter.mp ht).2).2⟩
  · intro x hx y hy hxy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hy
    have e1 := (hf t (Finset.mem_filter.mp ht).2).2
    have e2 := (hf t' (Finset.mem_filter.mp ht').2).2
    have hc : (f t : E ⧸ L) = (f t' : E ⧸ L) := (mk_eq_iff L _ _).mpr hxy
    rw [e1, e2] at hc
    rw [hR t (Finset.mem_filter.mp ht).1 t' (Finset.mem_filter.mp ht').1 ((mk_eq_iff L t t').mp hc)]
  · intro h h'
    rw [Finset.sum_image hinj]
    simp only [hG]
    rw [Finset.sum_filter]

end gen

section ta
variable {E : Type} [Field E] [DecidableEq E]

lemma ext_inj {h h' : Pt E} {s : ℕ} {t t' : E} (e : TA.ext h s t = TA.ext h' s t') :
    h = h' ∧ t = t' := by
  unfold TA.ext at e
  obtain ⟨h1, h2⟩ := List.append_inj' e rfl
  exact ⟨h1, by simpa using h2⟩

lemma mem_ext (Sg : ℕ → ℕ → Finset E) (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) (h : Pt E) (t : E) :
    TA.ext h s t ∈ PT Sg i ↔ h ∈ PT Sg (i - s) ∧ t ∈ Sg i s := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  simp only [PT, Finset.mem_biUnion, Finset.mem_attach, true_and, Finset.mem_image]
  constructor
  · rintro ⟨a, h', hh', t', ht', he⟩
    have hlt := Finset.mem_range.mp a.2
    unfold TA.ext at he
    obtain ⟨h1, h2⟩ := List.append_inj' he rfl
    have h3 : n + 1 - a.1 = s ∧ t' = t := by simpa using h2
    have ha : a.1 = n + 1 - s := by omega
    rw [← h1, ← h3.2, ← ha, ← h3.1]
    exact ⟨hh', ht'⟩
  · rintro ⟨hh, ht⟩
    have ha : n + 1 - s ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have e : n + 1 - (n + 1 - s) = s := by omega
    refine ⟨⟨n + 1 - s, ha⟩, h, hh, t, ?_, ?_⟩
    · simp only [e]
      exact ht
    · simp only [e]

private theorem isPt_of_mem_pt (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n, ∀ h ∈ PT Sg n, IsPt n h := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hh
    cases n with
    | zero =>
      simp only [PT, Finset.mem_singleton] at hh
      subst hh
      simp [TA.IsPt, TA.lvl]
    | succ n =>
      simp only [PT, Finset.mem_biUnion, Finset.mem_attach, true_and, Finset.mem_image] at hh
      obtain ⟨a, h0, hh0, t, ht, he⟩ := hh
      subst he
      have hm := Finset.mem_range.mp a.2
      obtain ⟨hl, hb⟩ := ih a.1 hm h0 hh0
      unfold TA.IsPt
      refine ⟨?_, ?_⟩
      · simp [TA.ext, TA.lvl] at hl ⊢
        omega
      · intro b hbm
        simp only [TA.ext, List.mem_append, List.mem_singleton] at hbm
        rcases hbm with hbm | rfl
        · exact hb b hbm
        · refine ⟨?_, hNZ _ _ t ht⟩
          show 1 ≤ n + 1 - a.1
          omega

lemma blk_psd (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) (hK : AxK D) (i s : ℕ)
    (hs : 1 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.r + 1) (t : E) (ht : t ≠ 0) :
    PSDOn (PT Sg (i - s)) (fun h h' => D.K i (TA.ext h s t) (TA.ext h' s t)) := by
  obtain ⟨_, hK2⟩ := hK
  have hP : ∀ p ∈ (PT Sg (i - s)).image (fun h => TA.ext h s t), IsPt i p := by
    intro p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hl, hb⟩ := isPt_of_mem_pt Sg hNZ (i - s) h hh
    unfold TA.IsPt
    refine ⟨?_, ?_⟩
    · simp [TA.ext, TA.lvl] at hl ⊢
      omega
    · intro b hbm
      simp only [TA.ext, List.mem_append, List.mem_singleton] at hbm
      rcases hbm with hbm | rfl
      · exact hb b hbm
      · exact ⟨hs, ht⟩
  have hk := hK2 i hi _ hP
  have hinj : Set.InjOn (fun h => TA.ext h s t) (PT Sg (i - s)) := fun x _ y _ e => (ext_inj e).1
  unfold TA.PSDOn at hk ⊢
  refine ⟨fun x hx y hy => hk.1 _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy),
    fun a => ?_⟩
  have h := hk.2 (fun p => a p.dropLast)
  simp only [Finset.sum_image hinj] at h
  simpa [TA.ext] using h

theorem domMinOfTextA : TC.DomMinOfTextA := by
  intro E _ _ D Sg Th hNZ hT i s hs hsi hi
  obtain ⟨_, h2, h3, h4⟩ := hT i s hs hsi hi
  refine ⟨fun t ht => h3 t (hNZ i s t ht), fun t _ t' _ hl h hh h' hh' => ?_,
    fun R _ hR => h4 R hR⟩
  have := h2 t' (t - t') hl h hh h' hh'
  simpa using this

theorem afterOfOldA : TC.AfterOfOldA := by
  intro E _ _ D hA
  have hT : ∀ Sg : ℕ → ℕ → Finset E, NZSg Sg → TC.DomTextA D Sg D.Th := by
    intro Sg hNZ i s hs hsi hi
    obtain ⟨h1, h2, h3, h4⟩ := hA i s hs hsi hi
    have hP : ∀ h ∈ PT Sg (i - s), IsPt (i - s) h := isPt_of_mem_pt Sg hNZ (i - s)
    exact ⟨fun t => h1 t _ hP, fun t l hl h _ h' _ => by rw [h2 t l hl],
      fun t ht => h3 t _ ht hP, fun R hR => h4 R _ hR hP⟩
  exact ⟨hT, fun Sg hNZ => ⟨D.Th, domMinOfTextA E D Sg D.Th hNZ (hT Sg hNZ)⟩⟩

theorem majorantPSDA : TC.MajorantPSDA := by
  intro E _ _ D Sg Th hNZ hK hD i s hs hsi hi t ht
  have h1 := (hD i s hs hsi hi).1 t ht
  have h2 := blk_psd D Sg hNZ hK i s hs hsi hi t (hNZ i s t ht)
  refine psd_congr ?_ (psd_add h1 h2)
  intro x _ y _
  exact sub_add_cancel _ _

end ta

section main
variable {E : Type} [Field E] [DecidableEq E]

noncomputable def D' (D : TA.Data E) (Sg : ℕ → ℕ → Finset E)
    (Th : ℕ → ℕ → E → TA.Pt E → TA.Pt E → ℂ) : TA.Data E :=
  { D with
    K := fun i => restr (PT Sg i) (D.K i)
    Th := fun i s t => restr (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s)) }

lemma slev_eq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {W : Type}
    (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (Φ : W → Pt E → H) (w : W) (j : ℕ) :
    Slev (D' D Sg Th) Sg Φ w j = Slev D Sg Φ w j := by
  unfold TA.Slev TA.gram
  congr 1
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  show restr (PT Sg j) (D.K j) x y * _ = _
  unfold restr
  rw [if_pos ⟨hx, hy⟩]

lemma lsup_eq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {W : Type} [Fintype W]
    (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (len : W → ℕ) (Kl : ℕ) (Φ : W → Pt E → H) (j : ℕ) :
    lsup (D' D Sg Th) len Kl Sg Φ j = lsup D len Kl Sg Φ j := by
  unfold TA.lsup
  simp only [slev_eq]
  try rfl

lemma G_psd (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (hNZ : NZSg Sg) (hK : AxK D)
    (hD : TC.DomMinA D Sg Th) (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.r + 1)
    (c : E ⧸ D.La i s) : PSDOn (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) c) := by
  rcases G_cases (D.La i s) (Sg i s) (Th i s) c with ⟨_, h0⟩ | ⟨t₁, ht₁, _, h1⟩
  · rw [h0]
    exact psd_zero _
  · rw [h1]
    exact majorantPSDA E D Sg Th hNZ hK hD i s hs hsi hi t₁ ht₁

theorem axK' (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (hNZ : NZSg Sg) (hK : AxK D) :
    AxK (D' D Sg Th) := by
  obtain ⟨hK1, hK2⟩ := hK
  unfold TA.AxK
  refine ⟨?_, fun i hi P hP => ?_⟩
  · show restr (PT Sg 0) (D.K 0) [] [] = 1
    have h0 : ([] : Pt E) ∈ PT Sg 0 := by simp [PT]
    unfold restr
    rw [if_pos ⟨h0, h0⟩]
    exact hK1
  · show PSDOn P (restr (PT Sg i) (D.K i))
    exact psd_restr (PT Sg i) P (hK2 i hi _ (isPt_of_mem_pt Sg hNZ i))

theorem axA2' (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (hA : KernelSupport D) : KernelSupport (D' D Sg Th) := by
  intro i s hs hsi hi h h' t t' hh hh' ht ht' hc
  have := hA i s hs hsi hi h h' t t' hh hh' ht ht' hc
  show restr (PT Sg i) (D.K i) (TA.ext h s t) (TA.ext h' s t') = 0
  unfold restr
  split_ifs <;> simp [this]

theorem thetaDomination_d_of_axK_of_domMinA (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (hNZ : NZSg Sg) (hK : AxK D)
    (hD : TC.DomMinA D Sg Th) : ThetaDomination (D' D Sg Th) := by
  intro i s hs hsi hi
  have hG := G_psd D Sg Th hNZ hK hD i s hs hsi hi
  obtain ⟨h1, h2, h3⟩ := hD i s hs hsi hi
  refine ⟨fun t Hd _ => psd_restr (PT Sg (i - s)) Hd (hG (t : E ⧸ D.La i s)),
    fun t l hl => ?_, fun t Hd ht _ => ?_, fun R Hd hR _ => ?_⟩
  · show restr (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) ((t + l : E) : E ⧸ D.La i s)) =
      restr (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s))
    rw [(mk_eq_iff (D.La i s) (t + l) t).mpr (by have hl' : l ∈ D.La i s := hl; simpa using hl')]
  · by_cases htS : t ∈ Sg i s
    · obtain ⟨t₁, ht₁, hc₁, hG₁⟩ : ∃ t₁ ∈ Sg i s, ((t₁ : E ⧸ D.La i s) = (t : E ⧸ D.La i s)) ∧
          G (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s) = Th i s t₁ := by
        rcases G_cases (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s) with ⟨hn, _⟩ | h
        · exact absurd ⟨t, htS, rfl⟩ hn
        · exact h
      have hl : t₁ - t ∈ D.La i s := (mk_eq_iff _ _ _).mp hc₁
      refine psd_congr (fun h _ h' _ => ?_) (psd_restr (PT Sg (i - s)) Hd (h1 t htS))
      show restr _ _ h h' =
        restr (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s)) h h' -
          restr (PT Sg i) (D.K i) (TA.ext h s t) (TA.ext h' s t)
      unfold restr
      by_cases hm : h ∈ PT Sg (i - s) ∧ h' ∈ PT Sg (i - s)
      · have he : TA.ext h s t ∈ PT Sg i ∧ TA.ext h' s t ∈ PT Sg i :=
          ⟨(mem_ext Sg i s hs hsi h t).mpr ⟨hm.1, htS⟩, (mem_ext Sg i s hs hsi h' t).mpr ⟨hm.2, htS⟩⟩
        rw [if_pos hm, if_pos hm, if_pos he, hG₁, h2 t₁ ht₁ t htS hl h hm.1 h' hm.2]
      · have he : ¬ (TA.ext h s t ∈ PT Sg i ∧ TA.ext h' s t ∈ PT Sg i) := fun he =>
          hm ⟨((mem_ext Sg i s hs hsi h t).mp he.1).1, ((mem_ext Sg i s hs hsi h' t).mp he.2).1⟩
        rw [if_neg hm, if_neg hm, if_neg he, sub_zero]
    · refine psd_congr (fun h _ h' _ => ?_)
        (psd_restr (PT Sg (i - s)) Hd (hG (t : E ⧸ D.La i s)))
      have he : ¬ (TA.ext h s t ∈ PT Sg i ∧ TA.ext h' s t ∈ PT Sg i) := fun he =>
        htS ((mem_ext Sg i s hs hsi h t).mp he.1).2
      show _ = restr (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s)) h h' -
        restr (PT Sg i) (D.K i) (TA.ext h s t) (TA.ext h' s t)
      unfold restr
      rw [if_neg he, sub_zero]
  · obtain ⟨S', hS', -, hSd, hsum⟩ := G_sum (D.La i s) (Sg i s) (Th i s) R hR
    refine psd_congr (fun h _ h' _ => ?_) (psd_restr (PT Sg (i - s)) Hd (h3 S' hS' hSd))
    show _ = ((1 + (D' D Sg Th).e i : ℝ) : ℂ) * restr (PT Sg (i - s)) (D.K (i - s)) h h' -
      ∑ t ∈ R, restr (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s)) h h'
    unfold restr
    by_cases hm : h ∈ PT Sg (i - s) ∧ h' ∈ PT Sg (i - s)
    · simp only [if_pos hm]
      rw [hsum h h']
      try rfl
    · simp only [if_neg hm, mul_zero, Finset.sum_const_zero, sub_zero]

theorem oneLevelAfterOfOldA : TC.OneLevelAfterOfOldA := by
  intro hO E _ _ H _ _ W _ len Kl D Sg Φ tr Pat1 Pat3 _ pat1 pat3 c1 c3 ep1 ep3 bd4 ep a i hNZ hi1 hi hep ha
    hK hA2 hTh hE hLE hLS
  obtain ⟨Th, hD⟩ := hTh
  have h := hO E H W len Kl (D' D Sg Th) Sg Φ tr Pat1 Pat3 pat1 pat3 c1 c3 ep1 ep3 bd4 ep a i hNZ hi1 hi
    hep ha (axK' D Sg Th hNZ hK) (axA2' D Sg Th hA2) (thetaDomination_d_of_axK_of_domMinA D Sg Th hNZ hK hD) hE hLE hLS
  simp only [lsup_eq] at h
  exact h

theorem oneLevelAfterA : TC.OneLevelAfterA := oneLevelAfterOfOldA one_level_inequality

end main

end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1

namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A2

open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism.FourierDecayAlt.P.BudgetLiftBounds Formalism.FourierDecayAlt.TC

theorem reductionAfterOfSteps : ReductionAfterOfSteps := by
  intro hOL hEps hA4 hJ C₀ hC₀
  obtain ⟨C', C, hJ'⟩ := hJ C₀ hC₀
  refine ⟨max C' 1, C, ?_⟩
  intro E _ _ H _ _ _ W _ len Kl f Θ D Pat1 Pat3 _ pat1 pat3 c1 c3 ep1 ep3 bd4 Φ tr w0 V jn ρ c
    hKl hf hΘ hr hK hA2 hDA hE hLS hLE hlim hw0 hV hPSD hsum
  have hΘ1 : 1 ≤ Θ := le_trans (le_max_right _ _) hΘ
  have hΘ0 : 0 < Θ := by linarith
  have hep : 0 ≤ (C₀ * Θ ^ (-((Kl : ℝ) - 5 / 2))) ^ f := by
    apply pow_nonneg
    apply mul_nonneg (by linarith)
    first
    | exact Real.rpow_nonneg hΘ0.le _
    | exact Real.rpow_nonneg_of_nonneg hΘ0.le _
  have ha : 0 ≤ (C₀ / Θ) ^ f := pow_nonneg (div_nonneg (by linarith) hΘ0.le) _
  have hG : ∀ Sg : ℕ → ℕ → Finset E, NZSg Sg → (gram (D.K (D.r + 1)) V (PT Sg (D.r + 1))).re ≤
      (1 + C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * jn := by
    intro Sg hNZ
    obtain ⟨Th, hD⟩ := hDA Sg hNZ
    refine hEps E H W len (D.K (D.r + 1)) (PT Sg (D.r + 1)) Φ V w0 (4 * Kl * (D.r + 1))
      ((1 + C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i))) jn
      (by omega) (fun eps heps => ?_) hlim (fun p hp => hV p (A1.isPt_of_mem_pt Sg hNZ _ p hp))
    let σ : ℕ → ℝ := fun i => √(lsup D len Kl Sg (Φ eps) i)
    let e' : ℕ → ℝ := fun i => max (D.e i) 0
    have hstep : ∀ i, 1 ≤ i → i ≤ D.r + 1 → σ i ≤
        (1 + (C₀ * Θ ^ (-((Kl : ℝ) - 5 / 2))) ^ f) * √(1 + e' i) * σ (i - 1) +
          ∑ t ∈ Icc 2 i, ((C₀ / Θ) ^ f) ^ (t - 1) * σ (i - t) := by
      intro i hi1 hi
      have he : e' i = D.e i := max_eq_left (hE i hi1 hi).1
      simp only [σ, he]
      exact hOL E H W len Kl D Sg (Φ eps) (tr eps i) Pat1 Pat3 (pat1 i) (pat3 i) (c1 i) (c3 i) (ep1 i)
        (ep3 i) (bd4 i) _ _ i hNZ hi1 hi hep ha hK hA2 ⟨Th, hD⟩ hE
        (hLE eps heps i (Finset.mem_Icc.mpr ⟨hi1, hi⟩)) (hLS i (Finset.mem_Icc.mpr ⟨hi1, hi⟩))
    have hrec := hJ' (Kl : ℝ) Θ f D.r e' σ (by exact_mod_cast hKl) hf (le_trans (le_max_left _ _) hΘ) hr
      (fun i => le_max_right _ _) (fun i => Real.sqrt_nonneg _) hstep
    have hprod : ∏ i ∈ Icc 1 (D.r + 1), (1 + e' i) = ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) :=
      Finset.prod_congr rfl fun i hi => by
        show 1 + max (D.e i) 0 = 1 + D.e i
        rw [max_eq_left (hE i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2).1]
    rw [hprod] at hrec
    have h0 : ∀ w, TA.Slev D Sg (Φ eps) w 0 = ‖Φ eps w []‖ ^ 2 := by
      intro w
      obtain ⟨hK1, -⟩ := hK
      simp only [TA.Slev, TA.gram, PT, Finset.sum_singleton, hK1, one_mul]
      first
      | exact inner_self_eq_norm_sq (𝕜 := ℂ) _
      | simp
    have hl0 : lsup D len Kl Sg (Φ eps) 0 =
        wsup len (4 * Kl * (D.r + 1)) (fun w => ‖Φ eps w []‖ ^ 2) := by
      unfold TA.lsup
      simp only [Nat.sub_zero, h0]
    have hnn : 0 ≤ lsup D len Kl Sg (Φ eps) 0 := by
      rw [hl0]
      unfold TA.wsup
      exact Real.iSup_nonneg fun _ => sq_nonneg _
    have hσ0 : σ 0 ^ 2 = wsup len (4 * Kl * (D.r + 1)) (fun w => ‖Φ eps w []‖ ^ 2) := by
      simp only [σ]
      rw [Real.sq_sqrt hnn, hl0]
    have hg : (gram (D.K (D.r + 1)) (Φ eps w0) (PT Sg (D.r + 1))).re ≤
        lsup D len Kl Sg (Φ eps) (D.r + 1) := by
      unfold TA.lsup TA.wsup
      have hw : len w0 ≤ 4 * Kl * (D.r + 1 - (D.r + 1)) := by omega
      exact le_ciSup (f := fun w : {w // len w ≤ 4 * Kl * (D.r + 1 - (D.r + 1))} =>
        TA.Slev D Sg (Φ eps) w.1 (D.r + 1)) (Set.finite_range _).bddAbove ⟨w0, hw⟩
    have hsq : lsup D len Kl Sg (Φ eps) (D.r + 1) ≤ σ (D.r + 1) ^ 2 := by
      simp only [σ]
      by_cases h : 0 ≤ lsup D len Kl Sg (Φ eps) (D.r + 1)
      · rw [Real.sq_sqrt h]
      · exact le_trans (le_of_lt (not_le.mp h)) (sq_nonneg _)
    calc (gram (D.K (D.r + 1)) (Φ eps w0) (PT Sg (D.r + 1))).re ≤ σ (D.r + 1) ^ 2 := le_trans hg hsq
      _ ≤ (1 + C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * σ 0 ^ 2 :=
        hrec
      _ = _ := by rw [hσ0]
  exact hA4 E H (D.r + 1) (D.K (D.r + 1)) V ρ c _ hG hPSD hsum

theorem domAfterA_of_old {E : Type} [Field E] [DecidableEq E] (D : Data E) (h : ThetaDomination D) :
    DomAfterA D := by
  exact (A1.afterOfOldA E D h).2

theorem reductionOfAfter : ReductionOfAfter := by
  intro hR C₀ h0
  obtain ⟨C', C, hC⟩ := hR C₀ h0
  refine ⟨C', C, ?_⟩
  intro E _ _ H _ _ _ W _ len Kl f Θ D Pat1 Pat3 _ pat1 pat3 c1 c3 ep1 ep3 bd4 Φ tr w0 V jn ρ c
    hKl hf hΘ hr hK hA2 hA13 hE
  exact hC E H W len Kl f Θ D Pat1 Pat3 pat1 pat3 c1 c3 ep1 ep3 bd4 Φ tr w0 V jn ρ c
    hKl hf hΘ hr hK hA2 (domAfterA_of_old D hA13) hE

end Formalism.FourierDecayAlt.P.RecursionWithDensities.A2

namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1

open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical

theorem psd_congr {α : Type} {Y : Finset α} {k k' : α → α → ℂ}
    (h : ∀ x ∈ Y, ∀ y ∈ Y, k x y = k' x y) (hk : PSDOn Y k) : PSDOn Y k' := by
  unfold TB.PSDOn at hk ⊢
  have e : (Matrix.of fun x y : Y => k' x y) = Matrix.of fun x y : Y => k x y := by
    ext x y
    simp only [Matrix.of_apply]
    exact (h x x.2 y y.2).symm
  rw [e]
  exact hk

theorem psd_zero {α : Type} (Y : Finset α) : PSDOn Y (fun _ _ => (0 : ℂ)) := by
  unfold TB.PSDOn
  have e : (Matrix.of fun x y : Y => (0 : ℂ)) = 0 := by
    ext x y
    simp
  rw [e]
  exact Matrix.PosSemidef.zero

theorem psd_add {α : Type} {Y : Finset α} {k k' : α → α → ℂ} (h : PSDOn Y k) (h' : PSDOn Y k') :
    PSDOn Y (fun x y => k x y + k' x y) := by
  unfold TB.PSDOn at h h' ⊢
  have e : (Matrix.of fun x y : Y => k x y + k' x y) =
      (Matrix.of fun x y : Y => k x y) + Matrix.of fun x y : Y => k' x y := by
    ext x y
    simp
  rw [e]
  exact h.add h'

private theorem sum_attach_ite_eq {α : Type} (X : Finset α) (a : α) (F : α → ℂ) :
    (∑ j ∈ X.attach, if (j : α) = a then F j else 0) = if a ∈ X then F a else 0 := by
  rw [Finset.sum_attach (s := X) (f := fun j => if j = a then F j else 0)]
  first
  | exact Finset.sum_ite_eq' X a F
  | simp

theorem psd_restrict {α : Type} {X : Finset α} (Y : Finset α) {k : α → α → ℂ} (hk : PSDOn X k) :
    PSDOn Y (fun x y => if x ∈ X ∧ y ∈ X then k x y else 0) := by
  unfold TB.PSDOn at hk ⊢
  have hB := hk.conjTranspose_mul_mul_same
    (Matrix.of fun (x : X) (y : Y) => if (x : α) = (y : α) then (1 : ℂ) else 0)
  convert hB using 1
  ext y y'
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite (star : ℂ → ℂ)]
  rw [sum_attach_ite_eq X (y' : α) (fun a => ∑ j ∈ X.attach, if (j : α) = (y : α) then k j a else 0),
    sum_attach_ite_eq X (y : α) (fun a => k a y')]
  by_cases hy : (y : α) ∈ X <;> by_cases hy' : (y' : α) ∈ X <;> simp [hy, hy']

theorem psd_smul {α : Type} {Y : Finset α} {k : α → α → ℂ} (c : ℝ) (hc : 0 ≤ c) (h : PSDOn Y k) :
    PSDOn Y (fun x y => (c : ℂ) * k x y) := by
  unfold TB.PSDOn at h ⊢
  have e : (Matrix.of fun x y : Y => (c : ℂ) * k x y) = (c : ℂ) • Matrix.of fun x y : Y => k x y := by
    ext x y
    simp
  rw [e]
  exact h.smul (Complex.zero_le_real.mpr hc)

variable {E W : Type} [Field E]

theorem domMinOfText : DomMinOfText := by
  intro E W _ D T Th hT i s hs hsi hi
  obtain ⟨_, h2, h3, h4⟩ := hT i s hs hsi hi
  refine ⟨fun t ht => h2 t ?_, fun t _ t' _ hl => h3 t t' hl, fun S _ hS => h4 S hS⟩
  rintro rfl
  exact T.zero_not_mem _ _ ht

theorem afterOfOld : AfterOfOld := by
  intro E W _ D hKer hA
  obtain ⟨hKr, hTh⟩ := hKer
  have hT : ∀ T : Tower E, DomText D T D.Th := by
    intro T i s hs hsi hi
    obtain ⟨_, h2, h3, h4⟩ := hA i s hs hsi hi
    have hL : ∀ h ∈ T.X (i - s), level h = i - s := fun h hh => ((T.isTower (i - s) h).mp hh).1
    exact ⟨fun t => hTh i s t _, fun t ht => h2 t ht _ hL,
      fun t t' hl h _ h' _ => by rw [h3 t t' hl], fun S hS => h4 S hS _ hL⟩
  exact ⟨hKr, fun i hi1 hi => (hA i 1 le_rfl hi1 hi).1, hT,
    fun T => ⟨D.Th, domMinOfText E W D T D.Th (hT T)⟩⟩

theorem majorantPSD : MajorantPSD := by
  intro E W _ D T Th hK hD i s hs hsi hi t ht
  have h1 := (hD i s hs hsi hi).1 t ht
  have h2 : TB.PSDOn (T.X (i - s)) (TB.blk (D.Kr i) s t t) := by
    have hY := hK i ((T.X (i - s)).image fun h => join h s t)
    unfold TB.PSDOn at hY ⊢
    have := hY.submatrix (fun h : T.X (i - s) =>
      (⟨join h.1 s t, Finset.mem_image_of_mem _ h.2⟩ : ((T.X (i - s)).image fun h => join h s t)))
    convert this using 1
    ext x y
    rfl
  refine psd_congr ?_ (psd_add h1 h2)
  intro x _ y _
  exact sub_add_cancel _ _

theorem domMonoE : DomMonoE := by
  intro E W _ D T Th e' hK he hD i s hs hsi hi
  obtain ⟨h1, h2, h3⟩ := hD i s hs hsi hi
  refine ⟨h1, h2, fun S hS hSd => ?_⟩
  have ha := psd_add (h3 S hS hSd)
    (psd_smul (e' i - D.e i) (by linarith [he i]) (hK (i - s) (T.X (i - s))))
  refine psd_congr (fun x _ y _ => ?_) ha
  dsimp only
  push_cast
  ring

theorem psd_restrict' {α : Type} {X : Finset α} (Y : Finset α) {k k' : α → α → ℂ} (hk : PSDOn X k)
    (h1 : ∀ x y, x ∈ X ∧ y ∈ X → k' x y = k x y) (h0 : ∀ x y, ¬ (x ∈ X ∧ y ∈ X) → k' x y = 0) :
    PSDOn Y k' := by
  refine psd_congr (fun x _ y _ => ?_) (psd_restrict Y hk)
  show (if x ∈ X ∧ y ∈ X then k x y else 0) = k' x y
  by_cases h : x ∈ X ∧ y ∈ X
  · rw [if_pos h, h1 x y h]
  · rw [if_neg h, h0 x y h]

theorem mk_eq_iff (L : AddSubgroup E) (a b : E) : ((a : E ⧸ L) = (b : E ⧸ L)) ↔ a - b ∈ L := by
  exact QuotientAddGroup.eq_iff_sub_mem

def good (L : AddSubgroup E) (S : Finset E) (c : E ⧸ L) : Prop := ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c

noncomputable def sel (L : AddSubgroup E) (S : Finset E) (c : E ⧸ L) : E :=
  if h : good L S c then h.choose else 0

theorem sel_mem {L : AddSubgroup E} {S : Finset E} {c : E ⧸ L} (h : good L S c) : sel L S c ∈ S := by
  unfold sel
  rw [dif_pos h]
  exact h.choose_spec.1

theorem sel_mk {L : AddSubgroup E} {S : Finset E} {c : E ⧸ L} (h : good L S c) :
    ((sel L S c : E) : E ⧸ L) = c := by
  unfold sel
  rw [dif_pos h]
  exact h.choose_spec.2

noncomputable def KrR (D : Data E W) (T : Tower E) : ℕ → Pt E → Pt E → ℂ :=
  fun i p q => if p ∈ T.X i ∧ q ∈ T.X i then D.Kr i p q else 0

noncomputable def ThR (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) :
    ℕ → ℕ → E → Pt E → Pt E → ℂ :=
  fun i s t h h' =>
    if (1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1) ∧
        good (D.La (i - s + 1) s) (T.Sg (i - s + 1) s) (t : E ⧸ D.La (i - s + 1) s) then
      (if h ∈ T.X (i - s) ∧ h' ∈ T.X (i - s) then
        Th i s (sel (D.La (i - s + 1) s) (T.Sg (i - s + 1) s) (t : E ⧸ D.La (i - s + 1) s)) h h'
      else 0)
    else 0

noncomputable def Dp (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) : Data E W :=
  { D with
    Kr := KrR D T
    K0 := by simp [KrR, Formalism.FourierDecayAlt.P.OneLevelCoefficients.X0, D.K0]
    Th := ThR D T Th }

theorem join_mem (T : Tower E) {i s : ℕ} (hs : 1 ≤ s) (hsi : s ≤ i) {t : E}
    (ht : t ∈ T.Sg (i - s + 1) s) (h : Pt E) : join h s t ∈ T.X i ↔ h ∈ T.X (i - s) := by
  have E1 : ∀ k (hk' : k < h.length) (hk2 : k < (join h s t).length),
      (join h s t)[k]'hk2 = h[k]'hk' := by
    intro k hk' hk2
    first
    | simp [join, List.getElem_append_left hk']
    | simp [join, List.getElem_append, hk']
  have E2 : ∀ k, k ≤ h.length → blockStart (join h s t) k = blockStart h k := by
    intro k hk'
    simp [blockStart, join, List.take_append_of_le_length hk']
  rw [T.isTower i, T.isTower (i - s)]
  constructor
  · rintro ⟨hl, hk⟩
    have hl' : level h + s = i := by simpa [level, join] using hl
    refine ⟨by omega, fun k hk' => ?_⟩
    have hk2 : k < (join h s t).length := by simp [join]; omega
    have := hk k hk2
    rw [E1 k hk' hk2, E2 k hk'.le] at this
    exact this
  · rintro ⟨hl, hk⟩
    refine ⟨?_, fun k hk2 => ?_⟩
    · simp [level, join] at hl ⊢
      omega
    · by_cases hk' : k < h.length
      · rw [E1 k hk' hk2, E2 k hk'.le]
        exact hk k hk'
      · have hkl : k = h.length := by simp [join] at hk2; omega
        subst hkl
        have e1 : (join h s t)[h.length]'hk2 = (s, t) := by simp [join]
        have e2 : blockStart (join h s t) h.length = level h + 1 := by
          simp [blockStart, join, level, List.take_append_of_le_length (le_refl h.length)]
        rw [e1, e2, hl]
        exact ⟨hs, ht⟩

theorem join_not_mem (T : Tower E) {i s : ℕ} {t : E}
    (ht : t ∉ T.Sg (i - s + 1) s) (h : Pt E) : join h s t ∉ T.X i := by
  intro hm
  rw [T.isTower i] at hm
  obtain ⟨hl, hk⟩ := hm
  have hl' : level h + s = i := by simpa [level, join] using hl
  have hk2 : h.length < (join h s t).length := by simp [join]
  have := (hk h.length hk2).2
  have e1 : (join h s t)[h.length]'hk2 = (s, t) := by simp [join]
  have e2 : blockStart (join h s t) h.length = level h + 1 := by
    simp [blockStart, join, level, List.take_append_of_le_length (le_refl h.length)]
  rw [e1, e2] at this
  have e3 : level h = i - s := by omega
  rw [e3] at this
  exact ht this

theorem ThR_psd (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) (hK : KrPSD D)
    (hD : DomMin D T Th) (i s : ℕ) (t : E) (Y : Finset (Pt E)) : PSDOn Y (ThR D T Th i s t) := by
  unfold ThR
  by_cases hc : (1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1) ∧
      good (D.La (i - s + 1) s) (T.Sg (i - s + 1) s) (t : E ⧸ D.La (i - s + 1) s)
  · obtain ⟨⟨hs, hsi, hi⟩, hg⟩ := id hc
    refine psd_congr (fun x _ y _ => ?_)
      (psd_restrict Y (majorantPSD E W D T Th hK hD i s hs hsi hi _ (sel_mem hg)))
    simp only [if_pos hc]
    first
    | exact if_congr Iff.rfl rfl rfl
    | (split_ifs <;> rfl)
  · refine psd_congr (fun x _ y _ => ?_) (psd_zero Y)
    simp only [if_neg hc]

theorem thetaDomination_dp_of_krPSD_of_domMin (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) (hK : KrPSD D)
    (hE : EBounds D) (hD : DomMin D T Th) : (Dp D T Th).ThetaDomination := by
  intro i s hs hsi hi
  obtain ⟨h1, h2, h3⟩ := hD i s hs hsi hi
  have hr : 1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1 := ⟨hs, hsi, hi⟩
  refine ⟨hE i (by omega) hi, ?_, ?_, ?_⟩
  · intro t _ Y _
    show PSDOn Y (fun h h' => ThR D T Th i s t h h' - blk (KrR D T i) s t t h h')
    by_cases ht : t ∈ T.Sg (i - s + 1) s
    · have hg : good (D.La (i - s + 1) s) (T.Sg (i - s + 1) s) (t : E ⧸ D.La (i - s + 1) s) :=
        ⟨t, ht, rfl⟩
      refine psd_restrict' Y (h1 t ht) (fun x y hxy => ?_) (fun x y hxy => ?_)
      · simp only [ThR, if_pos (And.intro hr hg), blk, KrR, join_mem T hs hsi ht, if_pos hxy]
        rw [h2 _ (sel_mem hg) t ht ((mk_eq_iff _ _ _).1 (sel_mk hg)) x hxy.1 y hxy.2]
      · simp only [ThR, blk, KrR, join_mem T hs hsi ht, if_neg hxy, ite_self, sub_zero]
    · refine psd_congr (fun x _ y _ => ?_) (ThR_psd D T Th hK hD i s t Y)
      simp only [blk, KrR, join_not_mem T ht, false_and, if_false, sub_zero]
  · intro t t' htt
    show ThR D T Th i s t = ThR D T Th i s t'
    have e : (t : E ⧸ D.La (i - s + 1) s) = t' := (mk_eq_iff _ _ _).2 htt
    funext h h'
    simp only [ThR, e]
  · intro S hS Y _
    show PSDOn Y (fun h h' => (1 + (D.e i : ℂ)) * KrR D T (i - s) h h' - ∑ t ∈ S, ThR D T Th i s t h h')
    set L := D.La (i - s + 1) s with hL
    set G := T.Sg (i - s + 1) s with hG
    set S' : Finset E := (S.filter (fun t : E => good L G (t : E ⧸ L))).image
      (fun t : E => sel L G (t : E ⧸ L)) with hS'
    have hsub : S' ⊆ G := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
      exact sel_mem (Finset.mem_filter.1 ht).2
    have hinc : ∀ t ∈ S', ∀ t' ∈ S', t - t' ∈ L → t = t' := by
      intro a ha b hb hab
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hb
      have e := (mk_eq_iff L _ _).2 hab
      rw [sel_mk (Finset.mem_filter.1 ht).2, sel_mk (Finset.mem_filter.1 ht').2] at e
      rw [e]
    have hinj : Set.InjOn (fun t : E => sel L G (t : E ⧸ L))
        (S.filter (fun t : E => good L G (t : E ⧸ L)) : Finset E) := by
      intro a ha b hb hab
      have ha' := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
      have hb' := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      have e : (a : E ⧸ L) = b := by
        rw [← sel_mk ha'.2, ← sel_mk hb'.2]; exact congrArg _ hab
      exact hS a ha'.1 b hb'.1 ((mk_eq_iff L _ _).1 e)
    refine psd_restrict' Y (h3 S' hsub hinc) (fun x y hxy => ?_) (fun x y hxy => ?_)
    · have hsum : ∑ t ∈ S, ThR D T Th i s t x y = ∑ t₁ ∈ S', Th i s t₁ x y := by
        rw [hS', Finset.sum_image (f := fun t₁ => Th i s t₁ x y) hinj, Finset.sum_filter]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases hg : good L G (t : E ⧸ L)
        · simp only [ThR, if_pos hg, if_pos hxy]
          exact if_pos (And.intro hr hg)
        · have : ¬ ((1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1) ∧ good L G (t : E ⧸ L)) := fun h => hg h.2
          simp only [ThR, if_neg hg]
          exact if_neg this
      rw [hsum]
      simp only [KrR, if_pos hxy]
    · have : ∀ t ∈ S, ThR D T Th i s t x y = 0 := by
        intro t _
        simp only [ThR, if_neg hxy, ite_self]
      rw [Finset.sum_eq_zero this]
      simp only [if_neg hxy, KrR, mul_zero, sub_zero]

theorem Dp_Q (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) (ε : ℝ) (k : ℕ)
    (w : W) : (Dp D T Th).Q T ε k w = D.Q T ε k w := by
  unfold TB.Data.Q TB.Data.Sf
  have e : (∑ p ∈ T.X k, ∑ q ∈ T.X k, (Dp D T Th).Kr k p q * (Dp D T Th).gram ε k w p q) =
      ∑ p ∈ T.X k, ∑ q ∈ T.X k, D.Kr k p q * D.gram ε k w p q := by
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
    show KrR D T k p q * _ = _
    unfold KrR
    rw [if_pos ⟨hp, hq⟩]
    try rfl
  rw [e]
  try rfl

theorem oneLevelAfterOfOld : OneLevelAfterOfOld := by
  intro hOL E W _ D ep C₄ hG hK hW hA2 hE hWv hP hLi hB hLa hep hC hv hv1 T hTh ε hε σ i hi1 hi hσ
    w hw
  obtain ⟨Th, hD⟩ := hTh
  have hA2' : (Dp D T Th).KernelSupport := by
    intro i s hs hsi hi h h' t t' hl hl' ht ht' htt hne
    refine hA2 i s hs hsi hi h h' t t' hl hl' ht ht' htt ?_
    intro h0
    apply hne
    show KrR D T i (join h s t) (join h' s t') = 0
    simp only [KrR, h0, ite_self]
  have hKP : (Dp D T Th).KernelPSD :=
    ⟨fun i Y => psd_restrict' Y (hK i (T.X i))
      (fun x y hxy => by show KrR D T i x y = _; simp only [KrR, if_pos hxy])
      (fun x y hxy => by show KrR D T i x y = _; simp only [KrR, if_neg hxy]), fun i s t Y => ThR_psd D T Th hK hD i s t Y⟩
  have h := hOL E W (Dp D T Th) ep C₄ hG hKP hW hA2' (thetaDomination_dp_of_krPSD_of_domMin D T Th hK hE hD) hWv hP hLi hB hLa
    hep hC hv hv1 T ε hε σ i hi1 hi
    (fun k hk => ⟨(hσ k hk).1, fun w hw => by rw [Dp_Q]; exact (hσ k hk).2 w hw⟩) w hw
  rw [Dp_Q] at h
  exact h

theorem oneLevelAfter : OneLevelAfter := oneLevelAfterOfOld one_level_inequality_split_by_size

end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1

namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B2

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.P.OneLevelCoefficients Finset
open scoped ComplexOrder

variable {E W : Type} [Field E]

theorem theoremAAfterOfSteps : TC.TheoremAAfterOfSteps := by
  intro hOL hLS hJ C₁ C₄ h1 h4
  set C₀ : ℝ := max (3 * C₁) (2 * C₄) with hC₀
  have hC01 : 1 ≤ C₀ := le_trans (by linarith) (le_max_left _ _)
  have hC03 : 3 * C₁ ≤ C₀ := le_max_left _ _
  have hC04 : 2 * C₄ ≤ C₀ := le_max_right _ _
  obtain ⟨C'J, CJ, hJ⟩ := hJ C₀ hC01
  refine ⟨max C₀ CJ, max (max C'J (3 * C₁)) 1, ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hK hf hΘ0 hC' hsm hS hG hKer hW hA2 hEB hDom hE72 hP hE73 hE74 hLat
    hE hCut hA4 R
  set C : ℝ := max C₀ CJ with hC
  have hCC0 : C₀ ≤ C := le_max_left _ _
  have hCCJ : CJ ≤ C := le_max_right _ _
  have hCpos : 0 ≤ C := by linarith
  have hΘ1 : 1 ≤ Θ := le_trans (le_max_right _ _) hC'
  have hΘ3 : 3 * C₁ ≤ Θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC'
  have hΘJ : C'J ≤ Θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC'
  set y : ℝ := Θ ^ (-((D.K : ℝ) - 5 / 2)) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hΘ0.le _
  have hK4 : (4 : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hK
  have hy1 : y ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hΘ1 (by linarith)
  set ep : ℝ := (C₁ * y) ^ D.f with hep
  have hep0 : 0 ≤ ep := by positivity
  have ha : 3 ^ D.f * ep = (3 * C₁ * y) ^ D.f := by rw [hep, ← mul_pow, mul_assoc]
  have h3y : 3 * C₁ * y ≤ 1 := by
    calc 3 * C₁ * y ≤ Θ * Θ⁻¹ := mul_le_mul hΘ3 hy1 hy0 hΘ0.le
      _ = 1 := mul_inv_cancel₀ hΘ0.ne'
  have ha1 : 3 ^ D.f * ep ≤ 1 := by
    rw [ha]; exact pow_le_one₀ (by positivity) h3y
  have ha0 : 0 ≤ 3 ^ D.f * ep := by positivity
  have haC : 3 ^ D.f * ep ≤ (C₀ * y) ^ D.f := by
    rw [ha]; exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hC03 hy0) _
  have hb : 2 ^ D.f * ep ≤ 3 ^ D.f * ep :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _) hep0
  have he : ∀ i, 1 ≤ i → i ≤ D.r + 1 → 0 ≤ D.e i ∧ D.e i ≤ 1 := hEB
  set e' : ℕ → ℝ := fun i => if 1 ≤ i ∧ i ≤ D.r + 1 then D.e i else 0 with he'
  have he'0 : ∀ i, 0 ≤ e' i := by
    intro i; simp only [he']; split_ifs with h
    · exact (he i h.1 h.2).1
    · exact le_rfl
  have hprod : ∏ i ∈ Icc 1 (D.r + 1), (1 + e' i) = ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) := by
    apply Finset.prod_congr rfl
    intro i hi; rw [Finset.mem_Icc] at hi
    simp only [he', if_pos hi]
  have hprod0 : 0 ≤ ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) := by
    apply Finset.prod_nonneg
    intro i hi; rw [Finset.mem_Icc] at hi
    have := (he i hi.1 hi.2).1; linarith
  have hx0 : 0 ≤ (C₀ / Θ) ^ D.f := by positivity
  have hxy : (C₀ / Θ) ^ D.f ≤ (C / Θ) ^ D.f :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hCC0 hΘ0.le) _
  have hr0 : (0 : ℝ) ≤ (D.r : ℝ) + 1 := by positivity
  have hBJ : 1 + CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f ≤ 1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f := by
    have s1 : CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f ≤ C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCCJ hr0) hx0
    have s2 : C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f ≤ C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f :=
      mul_le_mul_of_nonneg_left hxy (by positivity)
    linarith
  have hB0 : 0 ≤ 1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f := by positivity
  have hK0 : (TC.withTh D (fun _ _ _ _ _ => 0)).KernelPSD :=
    ⟨hKer, fun _ _ _ Y => by
      show Matrix.PosSemidef (0 : Matrix Y Y ℂ)
      exact Matrix.PosSemidef.zero⟩
  suffices key : ∀ (T : Tower E) (ε : ℝ), 0 < ε → ∀ σ₀ : ℝ,
      (∀ w ∈ D.Wb D.Ntop, (D.gram ε 0 w [] []).re / D.wt w ≤ σ₀) →
      D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1)) ≤
        ((1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i))) * σ₀ from
    hLS E W (TC.withTh D (fun _ _ _ _ _ => 0)) jn H Vt c hG hK0 hE hCut hA4 _ key R
  intro T ε hε σ₀ hσ₀
  have hempN : D.emp ∈ D.Wb D.Ntop := by
    simp [Data.Wb, D.emp_mem, D.cnt_emp]
  have hσ₀0 : 0 ≤ σ₀ := by
    refine le_trans ?_ (hσ₀ D.emp hempN)
    rw [D.wt_emp, div_one]; exact gram_diag D hG ε hε 0 D.emp []
  set S : ℕ → NNReal := fun k => (D.Wb (D.budget k)).sup (fun w => (D.Q T ε k w).toNNReal) with hSd
  set σ : ℕ → ℝ := fun k => √(S k : ℝ) with hσ
  have hσ0 : ∀ k, 0 ≤ σ k := fun k => Real.sqrt_nonneg _
  have hσsq : ∀ k, σ k ^ 2 = (S k : ℝ) := fun k => Real.sq_sqrt (NNReal.coe_nonneg _)
  have hσQ : ∀ k, ∀ w ∈ D.Wb (D.budget k), D.Q T ε k w ≤ σ k ^ 2 := by
    intro k w hw
    rw [hσsq]
    refine le_trans (Real.le_coe_toNNReal _) ?_
    exact_mod_cast Finset.le_sup (f := fun w => (D.Q T ε k w).toNNReal) hw
  have hSle : ∀ k (X : ℝ), 0 ≤ X → (∀ w ∈ D.Wb (D.budget k), D.Q T ε k w ≤ X) → (S k : ℝ) ≤ X := by
    intro k X hX h
    have : S k ≤ X.toNNReal := Finset.sup_le fun w hw => Real.toNNReal_le_toNNReal (h w hw)
    calc (S k : ℝ) ≤ (X.toNNReal : ℝ) := by exact_mod_cast this
      _ = X := Real.coe_toNNReal _ hX
  have hσle : ∀ k (X : ℝ), 0 ≤ X → (∀ w ∈ D.Wb (D.budget k), √(D.Q T ε k w) ≤ X) → σ k ≤ X := by
    intro k X hX h
    apply Real.sqrt_le_iff.mpr
    exact ⟨hX, hSle k _ (sq_nonneg X) fun w hw => (Real.sqrt_le_iff.mp (h w hw)).2⟩
  have hb0 : D.budget 0 = D.Ntop := by simp [Data.budget, Data.Ntop]
  have hσ00 : σ 0 ^ 2 ≤ σ₀ := by
    rw [hσsq]
    apply hSle 0 σ₀ hσ₀0
    intro w hw
    rw [Q0]; rw [hb0] at hw; exact hσ₀ w hw
  have hrec : ∀ i, 1 ≤ i → i ≤ D.r + 1 →
      σ i ≤ (1 + (C₀ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f) * √(1 + e' i) * σ (i - 1) +
        ∑ t ∈ Icc 2 i, ((C₀ / Θ) ^ D.f) ^ (t - 1) * σ (i - t) := by
    intro i hi1 hi
    have hei : e' i = D.e i := by simp only [he', if_pos (And.intro hi1 hi)]
    rw [hei]
    apply hσle i
    · apply add_nonneg
      · exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (hσ0 _)
      · exact Finset.sum_nonneg fun t _ => mul_nonneg (by positivity) (hσ0 _)
    intro w hw
    refine le_trans (hOL E W D ep C₄ hG hKer hW hA2 hEB hE72 hP hE73 hE74 hLat hep0 h4 hS.1
      (size_le_one D Θ hΘ1 hS) T (hDom T) ε hε σ i hi1 hi (fun k _ => ⟨hσ0 k, hσQ k⟩) w hw) ?_
    apply add_le_add
    · apply mul_le_mul_of_nonneg_right _ (hσ0 _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      have q1 : 0 ≤ 2 ^ D.f * ep := by positivity
      nlinarith
    · apply Finset.sum_le_sum
      intro s hs; rw [Finset.mem_Icc] at hs
      apply mul_le_mul_of_nonneg_right _ (hσ0 _)
      exact coef D Θ C₄ C₀ _ _ hΘ1 h4 hC04 hf hS ha0 ha1 (he i hi1 hi).1 (he i hi1 hi).2 i s hs.1 hs.2 hi
  have hfin := hJ (D.K : ℝ) Θ D.f D.r e' σ hK4 hf hΘJ
    (small D.r D.f C C₀ Θ hΘ0 (by linarith) hCC0 hsm) he'0 hσ0 hrec
  rw [hprod] at hfin
  have hempB : D.emp ∈ D.Wb (D.budget (D.r + 1)) := by
    simp [Data.Wb, D.emp_mem, D.cnt_emp]
  have hQ := hσQ (D.r + 1) D.emp hempB
  have hQS : D.Q T ε (D.r + 1) D.emp = D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1)) := by
    simp [Data.Q, D.wt_emp]
  rw [hQS] at hQ
  have hs0 : 0 ≤ σ 0 ^ 2 := sq_nonneg _
  calc D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1)) ≤ σ (D.r + 1) ^ 2 := hQ
    _ ≤ (1 + CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * σ 0 ^ 2 := hfin
    _ ≤ (1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * σ 0 ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBJ hprod0) hs0
    _ ≤ (1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * σ₀ :=
        mul_le_mul_of_nonneg_left hσ00 (mul_nonneg hB0 hprod0)

theorem theoremAOfAfter : TC.TheoremAOfAfter := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', hC⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hK hf hΘ hC' hr hS hG hKer hWd hA2 hA13 hEW hP hEL hEB hLS hEE
    hCut hA4
  obtain ⟨hKr, hEb, -, hDA⟩ := B1.afterOfOld E W D hKer hA13
  exact hC E W D Θ jn H Vt c hK hf hΘ hC' hr hS hG hKr hWd hA2 hEb hDA hEW hP hEL hEB hLS hEE hCut hA4

end Formalism.FourierDecayAlt.P.RecursionWithDensities.B2

namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate
theorem t_EOfDens : EOfDens := by
  intro r e sd h0 h1 h2 i hi1 hi2
  rcases Nat.lt_or_ge i (r + 1) with h | h
  · have := h0 i (Finset.mem_Icc.mpr ⟨hi1, by omega⟩)
    constructor <;> linarith
  · have hi : i = r + 1 := by omega
    subst hi
    constructor <;> linarith [le_max_right sd 1, max_le h2 (one_le_two : (1 : ℝ) ≤ 2)]

theorem t_ProductOfEMax : ProductOfEMax := by
  intro r e sd h0 h1
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1),
    Finset.prod_eq_one (fun i hi => by rw [h0 i hi, add_zero]), one_mul, h1]

theorem t_DensLeTwo : DensLeTwo := by
  intro f n h
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have h' : (18 : ℝ) * f ≤ 2 ^ n := by exact_mod_cast h
  have hy : 0 < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hpos
  have hy1 : ((2 : ℝ) ^ n)⁻¹ * 2 ^ n = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have hm := mul_le_mul_of_nonneg_left h' hy.le
  have hx : 12 * (f : ℝ) * ((2 : ℝ) ^ n)⁻¹ ≤ 2 / 3 := by nlinarith
  have hl := Real.log_two_gt_d9
  have h3 : Real.exp (12 * (f : ℝ) * ((2 : ℝ) ^ n)⁻¹) ≤ Real.exp (Real.log 2) :=
    Real.exp_le_exp.mpr (by linarith)
  rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h3

theorem t_DensSize : DensSize := by
  intro k r f h
  have hm : f + 5 ≤ k - 2 * r - 2 := by omega
  have hf : f < 2 ^ f := Nat.lt_two_pow_self
  calc 18 * f ≤ 32 * 2 ^ f := by omega
    _ = 2 ^ (f + 5) := by ring
    _ ≤ 2 ^ (k - 2 * r - 2) := Nat.pow_le_pow_right (by norm_num) hm

theorem t_SumBoundMax : SumBoundMax := by
  intro α Y k m sd hk h
  have h2 := B1.psd_smul (max sd 1 - sd) (by linarith [le_max_left sd 1]) hk
  refine B1.psd_congr (fun x _ y _ => ?_) (B1.psd_add h h2)
  push_cast
  ring

theorem t_OnceOnlyMax : OnceOnlyMax := by
  intro hO P _ B hpos hk hA
  have h := hO P B hpos hk hA
  have hA' := hA
  unfold S3.MassData.InTheoremA S3.MassData.Smod at hA'
  have hp := hpos.2
  have hvN : 0 < B.volN := by tauto
  have hvH : 0 < B.volH := by tauto
  have hvN' : 0 < B.volN' := by tauto
  have hvH' : 0 < B.volH' := by tauto
  have hd : 0 < B.dimπ := by tauto
  have hd' : 0 < B.dimπ' := by tauto
  have hn : 0 < B.n0c := by tauto
  have hδ : 0 ≤ B.δ := by tauto
  have c0 : 0 ≤ B.c0 * B.c0' := by unfold S3.MassData.c0 S3.MassData.c0'; positivity
  have h5 : 0 ≤ (1 + B.δ) * B.IntN := le_trans (mul_nonneg c0 hk.2) hA'
  refine h.trans ?_
  have h6 : (1 + B.δ) * B.supdens * (B.n0c * B.IntN) = B.supdens * (B.n0c * ((1 + B.δ) * B.IntN)) := by ring
  have h7 : (1 + B.δ) * max B.supdens 1 * (B.n0c * B.IntN) = max B.supdens 1 * (B.n0c * ((1 + B.δ) * B.IntN)) := by ring
  rw [h6, h7]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hn.le h5)

theorem densityData_covers : MassDataCovers := by
  intro P _ B r e hD h1 h0 hmax
  rw [t_ProductOfEMax r e B.supdens h0 hmax]
  exact max_le hD h1

theorem t_DomTextOfSystems : DomTextOfSystems := by
  intro E W _ D T Th hS i s hs hsi hi
  obtain ⟨_, _, h3, h4, h5, h6⟩ := hS i s hs hsi hi
  exact ⟨h4, h5, h3, h6⟩

theorem t_RecHypAfterOfOld : RecHypAfterOfOld := by
  intro hAO E W _ D C₁ C₄ Θ jn H _ _ Vt c hR
  obtain ⟨h1, h2, h3, h4, h5, hKer, h7, h8, hA13, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hR
  obtain ⟨hKr, hEb, -, hDA⟩ := hAO E W D hKer hA13
  unfold RecHypAfter
  exact ⟨h1, h2, h3, h4, h5, hKr, h7, h8, hEb, hDA, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem recursion_gives_densityData_after : RecursionGivesUniformBoundsAfter := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', hC⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hR hC' hr h0 P _ B hI hδ hS
  unfold RecHypAfter at hR
  obtain ⟨hK, hf, hΘ, hSz, hG, hKr, hWd, hA2, hEb, hDA, hEW, hP, hEL, hEB, hLS, hEE, hCut, hA4⟩ := hR
  have hp : ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) = 1 :=
    Finset.prod_eq_one (fun i hi => by rw [h0 i hi, add_zero])
  have hb := hC E W D Θ jn H Vt c hK hf hΘ hC' hr hSz hG hKr hWd hA2 hEb hDA hEW hP hEL hEB hLS hEE
    hCut hA4
  rw [hp, mul_one] at hb
  unfold S3.MassData.InTheoremA
  rw [hI, hδ]
  exact hS _ hb

theorem t_RecursionWithDens : RecursionWithDens := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', hC⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c sd hR hC' hr h0 hmax R
  unfold RecHypAfter at hR
  obtain ⟨hK, hf, hΘ, hS, hG, hKr, hWd, hA2, hEb, hDA, hEW, hP, hEL, hEB, hLS, hEE, hCut, hA4⟩ := hR
  have hp := t_ProductOfEMax D.r D.e sd h0 hmax
  have hb := hC E W D Θ jn H Vt c hK hf hΘ hC' hr hS hG hKr hWd hA2 hEb hDA hEW hP hEL hEB hLS hEE
    hCut hA4 R
  rwa [hp] at hb

theorem t_DomAgree : DomAgree := by
  intro hAg hTr hTw E W _ _ D T Th hD i s hs hsi hi
  obtain ⟨h1, h2, h3⟩ := hD i s hs hsi hi
  have hX : TA.PT (fun j s => T.Sg (j - s + 1) s) (i - s) = T.X (i - s) := (hTw E T (i - s)).symm
  refine ⟨fun t ht => ?_, fun t ht t' ht' hl h hh h' hh' => ?_, fun R hR hRd => ?_⟩
  · rw [hX]
    apply ((hAg _ _ _).1).mp
    refine B1.psd_congr (fun x _ y _ => ?_) (hTr _ _ _ (h1 t ht))
    rfl
  · rw [hX] at hh hh'
    exact h2 t ht t' ht' hl h' hh' h hh
  · rw [hX]
    apply ((hAg _ _ _).1).mp
    refine B1.psd_congr (fun x _ y _ => ?_) (hTr _ _ _ (h3 R hR hRd))
    push_cast
    rfl

end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1

namespace Formalism.FourierDecayAlt.P

open RecursionWithDensities

theorem domination_minimum_of_text : Formalism.FourierDecayAlt.TC.DomMinOfText := RecursionWithDensities.B1.domMinOfText

theorem after_of_old : Formalism.FourierDecayAlt.TC.AfterOfOld := RecursionWithDensities.B1.afterOfOld

theorem majorant_positive_semidefinite : Formalism.FourierDecayAlt.TC.MajorantPSD := RecursionWithDensities.B1.majorantPSD

theorem domination_monotone : Formalism.FourierDecayAlt.TC.DomMonoE := RecursionWithDensities.B1.domMonoE

theorem one_level_after : Formalism.FourierDecayAlt.TC.OneLevelAfter := RecursionWithDensities.B1.oneLevelAfter

theorem one_level_after_of_old : Formalism.FourierDecayAlt.TC.OneLevelAfterOfOld := RecursionWithDensities.B1.oneLevelAfterOfOld

theorem theorem_a_after : Formalism.FourierDecayAlt.TC.TheoremAAfter := RecursionWithDensities.B2.theoremAAfterOfSteps RecursionWithDensities.B1.oneLevelAfter limitStep joint_theorem_A'

theorem theorem_a_after_of_parts : Formalism.FourierDecayAlt.TC.TheoremAAfterOfSteps := RecursionWithDensities.B2.theoremAAfterOfSteps

theorem theorem_a_of_after : Formalism.FourierDecayAlt.TC.TheoremAOfAfter := RecursionWithDensities.B2.theoremAOfAfter

theorem domMinOfTextA_statement : Formalism.FourierDecayAlt.TC.DomMinOfTextA := RecursionWithDensities.A1.domMinOfTextA

theorem afterOfOldA_statement : Formalism.FourierDecayAlt.TC.AfterOfOldA := RecursionWithDensities.A1.afterOfOldA

theorem majorantPSDA_statement : Formalism.FourierDecayAlt.TC.MajorantPSDA := RecursionWithDensities.A1.majorantPSDA

theorem oneLevelAfterA_statement : Formalism.FourierDecayAlt.TC.OneLevelAfterA := RecursionWithDensities.A1.oneLevelAfterA

theorem oneLevelAfterOfOldA_statement : Formalism.FourierDecayAlt.TC.OneLevelAfterOfOldA := RecursionWithDensities.A1.oneLevelAfterOfOldA

theorem reduction_after : Formalism.FourierDecayAlt.TC.ReductionAfter := RecursionWithDensities.A2.reductionAfterOfSteps RecursionWithDensities.A1.oneLevelAfterA epsilon_limit domination_limit joint_theorem_A'

theorem reduction_after_of_parts : Formalism.FourierDecayAlt.TC.ReductionAfterOfSteps := RecursionWithDensities.A2.reductionAfterOfSteps

theorem reduction_of_after_inequality : Formalism.FourierDecayAlt.TC.ReductionOfAfter := RecursionWithDensities.A2.reductionOfAfter

theorem domination_agree : Formalism.FourierDecayAlt.TC.DomAgree := RecursionWithDensities.J1.t_DomAgree

theorem domination_text_of_systems : Formalism.FourierDecayAlt.TC.DomTextOfSystems := RecursionWithDensities.J1.t_DomTextOfSystems

theorem recursion_hypothesis_after_of_old : Formalism.FourierDecayAlt.TC.RecHypAfterOfOld := RecursionWithDensities.J1.t_RecHypAfterOfOld

theorem recursion_gives_explicit_after : Formalism.FourierDecayAlt.TC.RecursionGivesUniformBoundsAfter := RecursionWithDensities.J1.recursion_gives_densityData_after

theorem exponent_of_densities : Formalism.FourierDecayAlt.TC.EOfDens := RecursionWithDensities.J1.t_EOfDens

theorem product_of_exponent_max : Formalism.FourierDecayAlt.TC.ProductOfEMax := RecursionWithDensities.J1.t_ProductOfEMax

theorem density_le_two : Formalism.FourierDecayAlt.TC.DensLeTwo := RecursionWithDensities.J1.t_DensLeTwo

theorem density_size : Formalism.FourierDecayAlt.TC.DensSize := RecursionWithDensities.J1.t_DensSize

theorem sum_bound_max : Formalism.FourierDecayAlt.TC.SumBoundMax := RecursionWithDensities.J1.t_SumBoundMax

theorem recursion_with_densities : Formalism.FourierDecayAlt.TC.RecursionWithDens := RecursionWithDensities.J1.t_RecursionWithDens

theorem once_only_max : Formalism.FourierDecayAlt.TC.OnceOnlyMax := RecursionWithDensities.J1.t_OnceOnlyMax

theorem massData_covers : Formalism.FourierDecayAlt.TC.MassDataCovers := RecursionWithDensities.J1.densityData_covers

end Formalism.FourierDecayAlt.P
