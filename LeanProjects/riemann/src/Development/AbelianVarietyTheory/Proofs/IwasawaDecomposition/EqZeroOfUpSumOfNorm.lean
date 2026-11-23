import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfAffineHyperplaneLineSumsStatement

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.UpInj

variable {R V k W : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W]
  {res : R →+* k} {t : R} {Λ : Submodule R V} {π : V → W}

def Rel (res : R →+* k) (t : R) (Λ : Submodule R V) (π : V → W) (q : Pr R V k) (w : W) : Prop :=
  q.Ok res ∧ q.IsKer Λ ∧ ∃ e, q.f e = 1 ∧ π (t • e) = w

theorem mem_of_one {q : Pr R V k} (h : q.Ok res) {e : V} (he : q.f e = 1) : e ∈ q.L := by
  by_contra hn
  rw [h.off e hn] at he
  exact zero_ne_one he

theorem f_sub {q : Pr R V k} (h : q.Ok res) {x y : V} (hx : x ∈ q.L) (hy : y ∈ q.L) :
    q.f (x - y) = q.f x - q.f y := by
  have := h.add (x - y) (sub_mem hx hy) y hy
  rw [sub_add_cancel] at this
  rw [this]; ring

theorem pi_sub (h : Red res t Λ π) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) : π (x - y) = π x - π y := by
  have := h.add (x - y) (sub_mem hx hy) y hy
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem te_mem (ht : res t = 0) {q : Pr R V k} (h : q.Ok res) (hk : q.IsKer Λ) {e : V} (he : e ∈ q.L) :
    t • e ∈ Λ :=
  (hk _).2 ⟨q.L.smul_mem _ he, by rw [h.smul _ _ he, ht, zero_mul]⟩

theorem mem_of_pi (htf : ∀ x : V, t • x = 0 → x = 0) (hsat : ∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ)
    (hr : Red res t Λ π) {x : V} (hx : t • x ∈ Λ) (h0 : π (t • x) = 0) : x ∈ Λ := by
  obtain ⟨y, hy, s, hs, h⟩ := (hr.ker _ hx).1 h0
  have : s • x - y = 0 := htf _ (by rw [smul_sub, smul_comm, h, sub_self])
  exact hsat s x hs (by rw [sub_eq_zero.1 this]; exact hy)

theorem rel_fun (ht : res t = 0) (hr : Red res t Λ π) {q : Pr R V k} {w w' : W}
    (h : Rel res t Λ π q w) (h' : Rel res t Λ π q w') : w = w' := by
  obtain ⟨ho, hk, e, he, rfl⟩ := h
  obtain ⟨-, -, e', he', rfl⟩ := h'
  have m := mem_of_one ho he
  have m' := mem_of_one ho he'
  have h1 : e - e' ∈ Λ := (hk _).2 ⟨sub_mem m m', by rw [f_sub ho m m', he, he', sub_self]⟩
  have h2 := hr.smul t _ h1
  rw [ht, zero_smul, smul_sub, pi_sub hr (te_mem ht ho hk m) (te_mem ht ho hk m')] at h2
  exact sub_eq_zero.1 h2

theorem le_of_sub (hs : Function.Surjective res) {q q' : Pr R V k} (ho : q.Ok res) (hk : q.IsKer Λ)
    (ho' : q'.Ok res) (hk' : q'.IsKer Λ) {e e' : V} (he : q.f e = 1) (he' : q'.f e' = 1) (h : e - e' ∈ Λ)
    (y : V) (hy : y ∈ q.L) : y ∈ q'.L ∧ q'.f y = q.f y := by
  have m := mem_of_one ho he
  have m' := mem_of_one ho' he'
  obtain ⟨a, ha⟩ := hs (q.f y)
  have h1 : y - a • e ∈ Λ := (hk _).2 ⟨sub_mem hy (q.L.smul_mem _ m), by
    rw [f_sub ho hy (q.L.smul_mem _ m), ho.smul _ _ m, he, ha, mul_one, sub_self]⟩
  have h2 : y - a • e' ∈ Λ := by
    have := add_mem h1 (Λ.smul_mem a h)
    rwa [smul_sub, sub_add_sub_cancel] at this
  obtain ⟨h3, h4⟩ := (hk' _).1 h2
  have h5 : y ∈ q'.L := by
    have := add_mem h3 (q'.L.smul_mem a m')
    rwa [sub_add_cancel] at this
  refine ⟨h5, ?_⟩
  rw [f_sub ho' h5 (q'.L.smul_mem _ m'), ho'.smul _ _ m', he', mul_one, ha] at h4
  exact sub_eq_zero.1 h4

theorem rel_inj (hs : Function.Surjective res) (ht : res t = 0) (htf : ∀ x : V, t • x = 0 → x = 0)
    (hsat : ∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ) (hr : Red res t Λ π) {q q' : Pr R V k} {w : W}
    (h : Rel res t Λ π q w) (h' : Rel res t Λ π q' w) : q = q' := by
  obtain ⟨ho, hk, e, he, rfl⟩ := h
  obtain ⟨ho', hk', e', he', hw⟩ := h'
  have m := te_mem ht ho hk (mem_of_one ho he)
  have m' := te_mem ht ho' hk' (mem_of_one ho' he')
  have h1 : e - e' ∈ Λ := mem_of_pi htf hsat hr (by rw [smul_sub]; exact sub_mem m m')
    (by rw [smul_sub, pi_sub hr m m', hw, sub_self])
  have h2 : e' - e ∈ Λ := by rw [← neg_sub]; exact neg_mem h1
  have A := le_of_sub hs ho hk ho' hk' he he' h1
  have B := le_of_sub hs ho' hk' ho hk he' he h2
  ext y
  · exact ⟨fun h => (A y h).1, fun h => (B y h).1⟩
  · by_cases hy : y ∈ q.L
    · exact (A y hy).2.symm
    · rw [ho.off y hy, ho'.off y (fun h => hy (B y h).1)]

theorem rel_ne (ht : res t = 0) (htf : ∀ x : V, t • x = 0 → x = 0)
    (hsat : ∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ) (hr : Red res t Λ π) (q : Pr R V k) :
    ¬ Rel res t Λ π q 0 := by
  rintro ⟨ho, hk, e, he, h⟩
  have := ((hk _).1 (mem_of_pi htf hsat hr (te_mem ht ho hk (mem_of_one ho he)) h)).2
  rw [he] at this
  exact one_ne_zero this

theorem rel_ex (hs : Function.Surjective res) {q : Pr R V k} (ho : q.Ok res) (hk : q.IsKer Λ) :
    ∃ w, Rel res t Λ π q w := by
  obtain ⟨x, hx⟩ := ho.ne
  have m : x ∈ q.L := by
    by_contra hn
    exact hx (ho.off x hn)
  obtain ⟨a, ha⟩ := hs (q.f x)⁻¹
  exact ⟨_, ho, hk, a • x, by rw [ho.smul _ _ m, ha, inv_mul_cancel₀ hx], rfl⟩

theorem rel_dil (hs : Function.Surjective res) (ht : res t = 0) (hr : Red res t Λ π) {q : Pr R V k} {w : W}
    (h : Rel res t Λ π q w) {a : k} (ha : a ≠ 0) : Rel res t Λ π (q.dil a⁻¹) (a • w) := by
  obtain ⟨ho, hk, e, he, rfl⟩ := h
  obtain ⟨b, rfl⟩ := hs a
  have m := mem_of_one ho he
  refine ⟨ho.dil (inv_ne_zero ha), fun y => ?_, b • e, ?_, ?_⟩
  · rw [hk y]
    show _ ↔ y ∈ q.L ∧ (res b)⁻¹ * q.f y = 0
    simp [ha]
  · show (res b)⁻¹ * q.f (b • e) = 1
    rw [ho.smul _ _ m, he, mul_one, inv_mul_cancel₀ ha]
  · rw [smul_comm, hr.smul _ _ (te_mem ht ho hk m)]

end GlobalTheory.LevelHecke.UpInj

namespace GlobalTheory.LevelHecke

open UpInj in

theorem eq_zero_of_upSum_of_norm : ∀ (R V k W M : Type) [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W] [Fintype k] [DecidableEq k] [Finite W] [AddCommGroup M] [Module ℂ M] (res : R →+* k) (t : R) (Λ : Submodule R V) (π : V → W) (Φ : Pr R V k → M), Function.Surjective res → res t = 0 → (∀ x : V, t • x = 0 → x = 0) → (∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ) → Red res t Λ π → (∀ g : Module.Dual k W, g ≠ 0 → ∃ d : Pr R V k, d.L = Λ ∧ (∀ x ∈ Λ, d.f x = g (π x)) ∧ ∑ᶠ q ∈ {q | Pr.Inc res t d q}, Φ q = 0) → (∀ q : Pr R V k, q.Ok res → q.IsKer Λ → ∑ a : kˣ, Φ (q.dil (a : k)) = 0) → ∀ q : Pr R V k, q.Ok res → q.IsKer Λ → Φ q = 0 := by
  intro R V k W M _ _ _ _ _ _ _ _ _ _ _ res t Λ π Φ hs ht htf hsat hr hup hnm
  classical
  let ψ : W → M := fun w => if h : ∃ q, Rel res t Λ π q w then Φ h.choose else 0
  have ψ1 : ∀ q w, Rel res t Λ π q w → ψ w = Φ q := fun q w h => by
    have h0 : ∃ q, Rel res t Λ π q w := ⟨q, h⟩
    simp only [ψ, dif_pos h0]
    rw [rel_inj hs ht htf hsat hr h0.choose_spec h]
  have ψ0 : ∀ w, (¬ ∃ q, Rel res t Λ π q w) → ψ w = 0 := fun w h => dif_neg h
  let j : Pr R V k → W := fun q => if h : ∃ w, Rel res t Λ π q w then h.choose else 0
  have j1 : ∀ q : Pr R V k, q.Ok res → q.IsKer Λ → Rel res t Λ π q (j q) := fun q ho hk => by
    have h0 : ∃ w, Rel res t Λ π q w := rel_ex hs ho hk
    simp only [j, dif_pos h0]
    exact h0.choose_spec
  have key := GlobalTheory.T.eq_zero_of_affineHyperplane_line_sums k W M ψ (ψ0 _ fun ⟨q, h⟩ => rel_ne ht htf hsat hr q h) (fun g hg => ?_) (fun w => ?_)
  · intro q ho hk
    rw [← ψ1 q _ (j1 q ho hk)]
    exact key _
  · obtain ⟨d, rfl, hd, hsum⟩ := hup g hg
    have hinj : Set.InjOn j {q | Pr.Inc res t d q} := fun q hq q' hq' h =>
      rel_inj hs ht htf hsat hr (j1 q hq.1 hq.2.1) (h ▸ j1 q' hq'.1 hq'.2.1)
    have e1 : ∑ᶠ x ∈ {x | g x = 1}, ψ x = ∑ᶠ x ∈ j '' {q | Pr.Inc res t d q}, ψ x := by
      apply finsum_mem_inter_support_eq'
      intro w hw
      have hex : ∃ q, Rel res t d.L π q w := by
        by_contra hn
        exact hw (ψ0 w hn)
      obtain ⟨q, hq⟩ := hex
      constructor
      · intro hg1
        refine ⟨q, ?_, rel_fun ht hr (j1 q hq.1 hq.2.1) hq⟩
        obtain ⟨ho, hk, e, he, rfl⟩ := hq
        exact ⟨ho, hk, e, he, by rw [hd _ (te_mem ht ho hk (mem_of_one ho he))]; exact hg1⟩
      · rintro ⟨q', ⟨ho, hk, e, he, h1⟩, rfl⟩
        rw [hd _ (te_mem ht ho hk (mem_of_one ho he))] at h1
        show g _ = 1
        rw [rel_fun ht hr (j1 q' ho hk) ⟨ho, hk, e, he, rfl⟩]
        exact h1
    rw [e1, finsum_mem_image hinj, ← hsum]
    exact finsum_mem_congr rfl fun q hq => ψ1 q _ (j1 q hq.1 hq.2.1)
  · by_cases hex : ∃ q, Rel res t Λ π q w
    · obtain ⟨q, hq⟩ := hex
      rw [← hnm q hq.1 hq.2.1, ← Equiv.sum_comp (Equiv.inv kˣ)]
      refine Finset.sum_congr rfl fun a _ => ?_
      have := ψ1 _ _ (rel_dil hs ht hr hq (a⁻¹).ne_zero)
      rw [Units.val_inv_eq_inv_val, inv_inv] at this
      rw [← this, Equiv.inv_apply, Units.val_inv_eq_inv_val]
    · refine Finset.sum_eq_zero fun a _ => ψ0 _ ?_
      rintro ⟨q, hq⟩
      have := rel_dil hs ht hr hq (inv_ne_zero a.ne_zero)
      rw [smul_smul, inv_mul_cancel₀ a.ne_zero, one_smul] at this
      exact hex ⟨_, this⟩

end GlobalTheory.LevelHecke
