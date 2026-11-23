import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
open GlobalTheory.ClassRefine GlobalTheory.ClassPet

noncomputable section

namespace GlobalTheory.TwoLattices

open scoped Classical

variable {G : Type} [Group G]

def Reps (Γ H : Subgroup G) (T : Finset G) : Prop :=
  ∀ g : G, ∃! t, t ∈ T ∧ ∃ (γ : Γ) (κ : G), κ ∈ H ∧ g = (γ : G) * t * κ

def Cover (Γ H : Subgroup G) : Prop :=
  ∃ S : Finset G, ∀ g : G, ∃ s ∈ S, ∃ (γ : Γ) (κ : G), κ ∈ H ∧ g = (γ : G) * s * κ

def wsum (Γ H : Subgroup G) (T : Finset G) (Φ : G → ℂ) : ℂ :=
  ∑ t ∈ T, ((Nat.card (stabQ Γ H t) : ℂ))⁻¹ * Φ t

def dsum (Γ H : Subgroup G) (Φ : G → ℂ) : ℂ := if h : ∃ T, Reps Γ H T then wsum Γ H h.choose Φ else 0

def cj (K : Subgroup G) (x : G) : Subgroup G := K.comap (MulAut.conj x⁻¹).toMonoidHom

theorem mem_cj {K : Subgroup G} {x κ : G} : κ ∈ cj K x ↔ x⁻¹ * κ * x ∈ K := by
  simp [cj]

theorem Reps.cover {Γ H : Subgroup G} {T : Finset G} (h : Reps Γ H T) : Cover Γ H :=
  ⟨T, fun g => by obtain ⟨t, ⟨ht, e⟩, -⟩ := h g; exact ⟨t, ht, e⟩⟩

theorem Cover.reps {Γ H : Subgroup G} (h : Cover Γ H) : ∃ T, Reps Γ H T := by
  obtain ⟨S, hS⟩ := h
  let q : G → DoubleCoset.Quotient (Γ : Set G) (H : Set G) := DoubleCoset.mk Γ H
  have hq : ∀ a b, q a = q b ↔ ∃ (γ : Γ) (κ : G), κ ∈ H ∧ b = (γ : G) * a * κ := fun a b => by
    rw [DoubleCoset.eq]
    exact ⟨fun ⟨h, hh, k, hk, e⟩ => ⟨⟨h, hh⟩, k, hk, e⟩, fun ⟨h, k, hk, e⟩ => ⟨h, h.2, k, hk, e⟩⟩
  refine ⟨S.image fun s => (q s).out, fun g => ?_⟩
  obtain ⟨s, hs, e⟩ := hS g
  have e1 : q s = q g := (hq _ _).2 e
  have ho : ∀ c : DoubleCoset.Quotient (Γ : Set G) (H : Set G), q c.out = c := fun c => Quotient.out_eq c
  refine ⟨(q s).out, ⟨Finset.mem_image_of_mem _ hs, (hq _ _).1 ((ho _).trans e1)⟩, ?_⟩
  rintro t ⟨ht, h⟩
  obtain ⟨s', -, rfl⟩ := Finset.mem_image.1 ht
  have := (hq _ _).2 h
  rw [ho] at this
  rw [this, e1]

theorem Cover.mono {Γ H H' : Subgroup G} (h : Cover Γ H') (hle : H' ≤ H) : Cover Γ H := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun g => by obtain ⟨s, hs, γ, κ, hκ, e⟩ := hS g; exact ⟨s, hs, γ, κ, hle hκ, e⟩⟩

theorem Cover.of_relIndex {Γ H H' : Subgroup G} (h : Cover Γ H) (hne : H'.relIndex H ≠ 0) : Cover Γ H' := by
  rw [← Subgroup.inf_relIndex_right] at hne
  obtain ⟨U, -, hU, -⟩ := exists_cosetReps (inf_le_right : H' ⊓ H ≤ H) hne
  obtain ⟨S, hS⟩ := h
  refine ⟨(S ×ˢ U).image fun p => p.1 * p.2, fun g => ?_⟩
  obtain ⟨t, ht, γ, κ, hκ, e⟩ := hS g
  obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hU κ hκ
  exact ⟨t * u, Finset.mem_image.2 ⟨(t, u), Finset.mem_product.2 ⟨ht, hu⟩, rfl⟩, γ, u⁻¹ * κ, hu'.1, by rw [e]; group⟩

theorem dsum_eq {Γ H : Subgroup G} {T : Finset G} (hT : Reps Γ H T) {Φ : G → ℂ} (hl : ∀ (γ : Γ) g, Φ ((γ : G) * g) = Φ g)
    (hr : ∀ κ ∈ H, ∀ g, Φ (g * κ) = Φ g) : dsum Γ H Φ = wsum Γ H T Φ := by
  have h : ∃ T, Reps Γ H T := ⟨T, hT⟩
  rw [dsum, dif_pos h, wsum, sum_classReps_refine le_rfl hT h.choose_spec Φ hl hr (F := {1}) (by simp [H.one_mem])
    (fun κ hκ => ⟨1, by simpa using hκ, fun u hu => by simpa using hu.1⟩)]
  simp [wsum]

theorem dsum_refine {Γ H H' : Subgroup G} (hle : H' ≤ H) (hc : Cover Γ H') {Φ : G → ℂ}
    (hl : ∀ (γ : Γ) g, Φ ((γ : G) * g) = Φ g) (hr : ∀ κ ∈ H', ∀ g, Φ (g * κ) = Φ g) {F : Finset G} (hF : ∀ κ ∈ F, κ ∈ H)
    (hFu : ∀ κ ∈ H, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ H') : dsum Γ H' Φ = dsum Γ H fun g => ∑ u ∈ F, Φ (g * u) := by
  have h := (hc.mono hle).reps
  have h' := hc.reps
  rw [dsum, dif_pos h', dsum, dif_pos h, wsum, wsum, sum_classReps_refine hle h.choose_spec h'.choose_spec Φ hl hr hF hFu]

theorem dsum_mul (Γ H : Subgroup G) (c : ℂ) (Φ : G → ℂ) : dsum Γ H (fun g => c * Φ g) = c * dsum Γ H Φ := by
  unfold dsum wsum
  split_ifs
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp

theorem dsum_sum (Γ H : Subgroup G) {ι : Type} (s : Finset ι) (Φ : ι → G → ℂ) :
    dsum Γ H (fun g => ∑ i ∈ s, Φ i g) = ∑ i ∈ s, dsum Γ H (Φ i) := by
  unfold dsum wsum
  split_ifs
  · simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  · simp

theorem dsum_index {Γ H H' : Subgroup G} (hle : H' ≤ H) (hne : H'.relIndex H ≠ 0) (hc : Cover Γ H') {Φ : G → ℂ}
    (hl : ∀ (γ : Γ) g, Φ ((γ : G) * g) = Φ g) (hr : ∀ κ ∈ H, ∀ g, Φ (g * κ) = Φ g) :
    dsum Γ H' Φ = (H'.relIndex H : ℂ) * dsum Γ H Φ := by
  obtain ⟨F, h1, h2, h3⟩ := exists_cosetReps hle hne
  rw [dsum_refine hle hc hl (fun κ hκ => hr κ (hle hκ)) h1 h2, ← dsum_mul]
  congr 1
  funext g
  rw [Finset.sum_congr rfl fun u hu => hr u (h1 u hu) g, Finset.sum_const, h3, nsmul_eq_mul]

theorem reps_conj {Γ H : Subgroup G} {T : Finset G} (hT : Reps Γ H T) (δ x : G) :
    Reps (cj Γ δ) (cj H x) (T.image fun t => δ * t * x⁻¹) := by
  intro g
  obtain ⟨t, ⟨ht, γ, κ, hκ, e⟩, hu⟩ := hT (δ⁻¹ * g * x)
  refine ⟨δ * t * x⁻¹, ⟨Finset.mem_image_of_mem _ ht, ⟨δ * γ * δ⁻¹, mem_cj.2 (by simp [mul_assoc])⟩, x * κ * x⁻¹,
    mem_cj.2 (by simpa [mul_assoc] using hκ), ?_⟩, ?_⟩
  · have : g = δ * (δ⁻¹ * g * x) * x⁻¹ := by group
    rw [this, e]
    simp [mul_assoc]
  · rintro s ⟨hs, γ', κ', hκ', e'⟩
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hs
    rw [hu t' ⟨ht', ⟨_, mem_cj.1 γ'.2⟩, _, mem_cj.1 hκ', by rw [e']; simp [mul_assoc]⟩]

def stabConj (Γ H : Subgroup G) (δ x t : G) : stabQ (cj Γ δ) (cj H x) (δ * t * x⁻¹) ≃ stabQ Γ H t where
  toFun γ := ⟨⟨_, mem_cj.1 γ.1.2⟩, mem_stabQ.2 (by simpa [mul_assoc] using mem_cj.1 (mem_stabQ.1 γ.2))⟩
  invFun γ := ⟨⟨δ * γ.1 * δ⁻¹, mem_cj.2 (by simp [mul_assoc])⟩,
    mem_stabQ.2 (mem_cj.2 (by simpa [mul_assoc] using mem_stabQ.1 γ.2))⟩
  left_inv γ := Subtype.ext (Subtype.ext (by simp [mul_assoc]))
  right_inv γ := Subtype.ext (Subtype.ext (by simp [mul_assoc]))

theorem dsum_conj {Γ H : Subgroup G} (hc : Cover Γ H) {Φ : G → ℂ} (hl : ∀ (γ : Γ) g, Φ ((γ : G) * g) = Φ g)
    (hr : ∀ κ ∈ H, ∀ g, Φ (g * κ) = Φ g) (δ x : G) :
    dsum (cj Γ δ) (cj H x) (fun g => Φ (δ⁻¹ * g * x)) = dsum Γ H Φ := by
  obtain ⟨T, hT⟩ := hc.reps
  rw [dsum_eq hT hl hr, dsum_eq (reps_conj hT δ x), wsum, wsum, Finset.sum_image (fun a _ b _ e => by simpa using e)]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [Nat.card_congr (stabConj Γ H δ x t)]
    simp [mul_assoc]
  · intro γ g
    rw [← hl ⟨_, mem_cj.1 γ.2⟩ (δ⁻¹ * g * x)]
    simp [mul_assoc]
  · intro κ hκ g
    rw [← hr _ (mem_cj.1 hκ) (δ⁻¹ * g * x)]
    simp [mul_assoc]

theorem cj_one (K : Subgroup G) : cj K 1 = K := by
  ext; simp [mem_cj]

theorem relIndex_cj {K : Subgroup G} (h : ∀ x, (cj K x).relIndex K ≠ 0) (x : G) : K.relIndex (cj K x) ≠ 0 := by
  have := h x⁻¹
  rw [cj, Subgroup.relIndex_comap] at this
  convert this using 2
  ext κ
  rw [mem_cj]
  exact ⟨fun h => ⟨_, h, by simp [mul_assoc]⟩, by rintro ⟨k, hk, rfl⟩; simpa [mul_assoc] using hk⟩

def ind (Δ H : Subgroup G) (x g : G) : ℂ := if ∃ δ ∈ Δ, ∃ κ ∈ H, g = δ * x * κ then 1 else 0

theorem ind_left {Δ H : Subgroup G} {x δ : G} (hδ : δ ∈ Δ) (g : G) : ind Δ H x (δ * g) = ind Δ H x g := by
  unfold ind
  refine if_congr ⟨fun ⟨a, ha, k, hk, e⟩ => ⟨δ⁻¹ * a, Δ.mul_mem (Δ.inv_mem hδ) ha, k, hk, ?_⟩,
    fun ⟨a, ha, k, hk, e⟩ => ⟨δ * a, Δ.mul_mem hδ ha, k, hk, by rw [e]; group⟩⟩ rfl rfl
  rw [mul_assoc, mul_assoc, ← mul_assoc a, ← e]; group

theorem ind_right {Δ H : Subgroup G} {x κ : G} (hκ : κ ∈ H) (g : G) : ind Δ H x (g * κ) = ind Δ H x g := by
  unfold ind
  refine if_congr ⟨fun ⟨a, ha, k, hk, e⟩ => ⟨a, ha, k * κ⁻¹, H.mul_mem hk (H.inv_mem hκ), ?_⟩,
    fun ⟨a, ha, k, hk, e⟩ => ⟨a, ha, k * κ, H.mul_mem hk hκ, by rw [e]; group⟩⟩ rfl rfl
  rw [← mul_assoc, ← e]; group

theorem mass_refine (Δ : Subgroup G) {H H' : Subgroup G} (hle : H' ≤ H) (hne : H'.relIndex H ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ Γ : Subgroup G, Γ ≤ Δ → Cover Γ H' → dsum Γ H' (ind Δ H' 1) = n * dsum Γ H (ind Δ H 1) := by
  obtain ⟨F, h1, h2, -⟩ := exists_cosetReps hle hne
  refine ⟨(F.filter fun u => ∃ δ ∈ Δ, ∃ κ ∈ H', u = δ * 1 * κ).card, ?_, fun Γ hΓ hc => ?_⟩
  · obtain ⟨u, ⟨hu, hu'⟩, -⟩ := h2 1 H.one_mem
    exact Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨hu, 1, Δ.one_mem, u, by simpa using hu', by simp⟩)
  rw [dsum_refine hle hc (fun γ => ind_left (hΓ γ.2)) (fun κ hκ => ind_right hκ) h1 h2, ← dsum_mul]
  congr 1
  funext g
  by_cases hg : ∃ δ ∈ Δ, ∃ κ ∈ H, g = δ * 1 * κ
  · obtain ⟨δ, hδ, κ, hκ, rfl⟩ := hg
    have e : ∑ u ∈ F, ind Δ H' 1 (κ * u) = ∑ u ∈ F, ind Δ H' 1 u := by
      choose! r hr hru using fun u (hu : u ∈ H) => h2 u hu
      have hm : ∀ u ∈ F, κ * u ∈ H := fun u hu => H.mul_mem hκ (h1 u hu)
      refine Finset.sum_bij (fun u _ => r (κ * u)) (fun u hu => (hr _ (hm u hu)).1) (fun a ha b hb e => ?_) (fun b hb => ?_)
        (fun u hu => ?_)
      · have h3 := (hr _ (hm a ha)).2
        have h4 := (hr _ (hm b hb)).2
        rw [e] at h3
        have := H'.mul_mem (H'.inv_mem h3) h4
        exact (hru b (h1 b hb) a ⟨ha, by simpa [mul_assoc] using this⟩).trans
          (hru b (h1 b hb) b ⟨hb, by simp [H'.one_mem]⟩).symm
      · have hb' : κ⁻¹ * b ∈ H := H.mul_mem (H.inv_mem hκ) (h1 b hb)
        refine ⟨r (κ⁻¹ * b), (hr _ hb').1, (hru _ (hm _ (hr _ hb').1) b ⟨hb, ?_⟩).symm⟩
        simpa [mul_assoc] using H'.inv_mem (hr _ hb').2
      · rw [← ind_right (hr _ (hm u hu)).2 (r (κ * u))]
        simp
    simp_rw [mul_one, mul_assoc, ind_left hδ]
    rw [e, ← one_mul κ, ind_right hκ]
    simp only [ind]
    rw [if_pos ⟨1, Δ.one_mem, 1, H.one_mem, by simp⟩, Finset.sum_boole, mul_one]
    simp only [mul_one]
  · rw [ind, if_neg hg, mul_zero]
    refine Finset.sum_eq_zero fun u hu => if_neg fun ⟨δ, hδ, κ, hκ, e⟩ => hg ⟨δ, hδ, κ * u⁻¹, H.mul_mem (hle hκ) (H.inv_mem (h1 u hu)), ?_⟩
    rw [← mul_assoc, ← e]; group

theorem mass_pos {Δ Γ H : Subgroup G} (hΓ : Γ ≤ Δ) (hc : Cover Γ H) (hf : ∀ t, Finite (stabQ Γ H t)) :
    ∃ m : ℝ, 0 < m ∧ dsum Γ H (ind Δ H 1) = m := by
  obtain ⟨T, hT⟩ := hc.reps
  refine ⟨∑ t ∈ T, ((Nat.card (stabQ Γ H t) : ℝ))⁻¹ * if ∃ δ ∈ Δ, ∃ κ ∈ H, t = δ * 1 * κ then 1 else 0, ?_, ?_⟩
  · obtain ⟨t, ⟨ht, γ, κ, hκ, e⟩, -⟩ := hT 1
    refine Finset.sum_pos' (fun s _ => by positivity) ⟨t, ht, ?_⟩
    have e' : t = (γ : G)⁻¹ * 1 * κ⁻¹ := by rw [e]; group
    rw [if_pos ⟨(γ : G)⁻¹, Δ.inv_mem (hΓ γ.2), κ⁻¹, H.inv_mem hκ, e'⟩, mul_one]
    haveI := hf t
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  · rw [dsum_eq hT (fun γ => ind_left (hΓ γ.2)) (fun κ hκ => ind_right hκ), wsum]
    push_cast
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold ind
    split_ifs <;> simp

theorem dsum_prop {Δ Γ Γ' K : Subgroup G} (hK : ∀ x, (cj K x).relIndex K ≠ 0) (hΓ : Γ ≤ Δ) (hΓ' : Γ' ≤ Δ)
    (hc : Cover Γ K) (hc' : Cover Γ' K) (hf : ∀ t, Finite (stabQ Γ K t)) (hf' : ∀ t, Finite (stabQ Γ' K t)) :
    ∃ c : ℝ, 0 < c ∧ ∀ Φ : G → ℂ, (∀ δ ∈ Δ, ∀ g, Φ (δ * g) = Φ g) → (∀ κ ∈ K, ∀ g, Φ (g * κ) = Φ g) →
      dsum Γ K Φ = c * dsum Γ' K Φ := by
  obtain ⟨m, hm, em⟩ := mass_pos hΓ hc hf
  obtain ⟨m', hm', em'⟩ := mass_pos hΓ' hc' hf'
  have key : ∀ x, ∃ q : ℂ, ∀ Γ : Subgroup G, Γ ≤ Δ → Cover Γ K → dsum Γ K (ind Δ K x) = q * dsum Γ K (ind Δ K 1) := by
    intro x
    have h1 : (cj K x ⊓ K).relIndex K ≠ 0 := by rw [Subgroup.inf_relIndex_right]; exact hK x
    have h2 : (cj K x ⊓ K).relIndex (cj K x) ≠ 0 := by rw [Subgroup.inf_relIndex_left]; exact relIndex_cj hK x
    obtain ⟨n, -, en⟩ := mass_refine Δ inf_le_right h1
    obtain ⟨n', hn', en'⟩ := mass_refine Δ inf_le_left h2
    refine ⟨n / n', fun Γ hΓ hc => ?_⟩
    have hn'' : (n' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn'
    rw [div_mul_eq_mul_div, ← en Γ hΓ (hc.of_relIndex h1), en' Γ hΓ (hc.of_relIndex h1), mul_div_cancel_left₀ _ hn'',
      ← dsum_conj hc (fun γ => ind_left (hΓ γ.2)) (fun κ hκ => ind_right hκ) 1 x, cj_one]
    congr 1
    funext g
    unfold ind
    refine if_congr ⟨fun ⟨a, ha, k, hk, e⟩ => ⟨a, ha, x * k * x⁻¹, mem_cj.2 (by simpa [mul_assoc] using hk), ?_⟩,
      fun ⟨a, ha, k, hk, e⟩ => ⟨a, ha, _, mem_cj.1 hk, by rw [e]; group⟩⟩ rfl rfl
    have : g = (1⁻¹ * g * x) * x⁻¹ := by group
    rw [this, e]; group
  choose q hq using key
  have hcΔ : Cover Δ K := by
    obtain ⟨S, hS⟩ := hc
    exact ⟨S, fun g => by obtain ⟨s, hs, γ, e⟩ := hS g; exact ⟨s, hs, ⟨γ, hΓ γ.2⟩, e⟩⟩
  obtain ⟨X, hX⟩ := hcΔ.reps
  refine ⟨m / m', div_pos hm hm', fun Φ hl hr => ?_⟩
  have hΦ : Φ = fun g => ∑ x ∈ X, Φ x * ind Δ K x g := by
    funext g
    obtain ⟨x, ⟨hx, δ, κ, hκ, e⟩, hu⟩ := hX g
    rw [Finset.sum_eq_single_of_mem x hx fun y hy hne => ?_]
    · rw [ind, if_pos ⟨δ, δ.2, κ, hκ, e⟩, mul_one, e, hr κ hκ, hl _ δ.2]
    · rw [ind, if_neg fun ⟨a, ha, k, hk, e'⟩ => hne (hu y ⟨hy, ⟨a, ha⟩, k, hk, e'⟩), mul_zero]
  have hm'' : (m' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm'.ne'
  rw [hΦ, dsum_sum, dsum_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dsum_mul, dsum_mul, hq x Γ hΓ hc, hq x Γ' hΓ' hc', em, em']
  push_cast
  field_simp

end GlobalTheory.TwoLattices

end
