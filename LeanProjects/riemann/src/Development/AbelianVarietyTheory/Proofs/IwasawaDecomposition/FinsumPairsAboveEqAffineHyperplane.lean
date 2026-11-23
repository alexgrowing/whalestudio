import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.AboveSum

variable {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]

theorem mem_of_one {res : R →+* k} {q : Pr R V k} (h : q.Ok res) {e : V} (he : q.f e = 1) : e ∈ q.L := by
  by_contra hn
  rw [h.off e hn] at he
  exact zero_ne_one he

theorem smul_mem_ker {res : R →+* k} {q : Pr R V k} {Λ : Submodule R V} (h : q.Ok res) (hk : q.IsKer Λ) {t : R}
    (ht : res t = 0) {e : V} (he : q.f e = 1) : t • e ∈ Λ :=
  (hk _).2 ⟨q.L.smul_mem _ (mem_of_one h he), by rw [h.smul _ _ (mem_of_one h he), ht, zero_mul]⟩

theorem sub_mem_ker {res : R →+* k} {q : Pr R V k} {Λ : Submodule R V} (h : q.Ok res) (hk : q.IsKer Λ)
    {e : V} (he : q.f e = 1) {y : V} (hy : y ∈ q.L) {a : R} (ha : res a = q.f y) : y + (-a) • e ∈ Λ := by
  have he' := mem_of_one h he
  refine (hk _).2 ⟨q.L.add_mem hy (q.L.smul_mem _ he'), ?_⟩
  rw [h.add _ hy _ (q.L.smul_mem _ he'), h.smul _ _ he', he, map_neg, ha]
  ring

theorem le_of_ker {res : R →+* k} (hres : Function.Surjective res) {q q' : Pr R V k} {Λ : Submodule R V}
    (h : q.Ok res) (hk : q.IsKer Λ) (h' : q'.Ok res) (hk' : q'.IsKer Λ) {e e' : V} (he : q.f e = 1)
    (he' : q'.f e' = 1) (hd : e - e' ∈ Λ) {y : V} (hy : y ∈ q.L) : y ∈ q'.L ∧ q'.f y = q.f y := by
  obtain ⟨a, ha⟩ := hres (q.f y)
  have h1 := sub_mem_ker h hk he hy ha
  have h2 := (hk' _).1 (Λ.add_mem h1 (Λ.smul_mem a hd))
  have h3 := mem_of_one h' he'
  have e0 : y = (y + (-a) • e + a • (e - e')) + a • e' := by
    rw [smul_sub, neg_smul]; abel
  have h4 := q'.L.smul_mem a h3
  constructor
  · rw [e0]; exact q'.L.add_mem h2.1 h4
  · have h5 := h'.add _ h2.1 _ h4
    rw [← e0, h2.2, h'.smul _ _ h3, he', ha] at h5
    rw [h5]; ring

theorem eq_of_ker {res : R →+* k} (hres : Function.Surjective res) {q q' : Pr R V k} {Λ : Submodule R V}
    (h : q.Ok res) (hk : q.IsKer Λ) (h' : q'.Ok res) (hk' : q'.IsKer Λ) {e e' : V} (he : q.f e = 1)
    (he' : q'.f e' = 1) (hd : e - e' ∈ Λ) : q = q' := by
  have hd' : e' - e ∈ Λ := by rw [← neg_sub]; exact Λ.neg_mem hd
  ext y
  · exact ⟨fun hy => (le_of_ker hres h hk h' hk' he he' hd hy).1,
      fun hy => (le_of_ker hres h' hk' h hk he' he hd' hy).1⟩
  · by_cases hy : y ∈ q.L
    · exact (le_of_ker hres h hk h' hk' he he' hd hy).2.symm
    · rw [h.off y hy, h'.off y (fun hy' => hy (le_of_ker hres h' hk' h hk he' he hd' hy').1)]

theorem finsum_above : ∀ (R V k W M : Type) [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W] [AddCommMonoid M] (res : R →+* k) (t : R) (p : Pr R V k) (π : V → W) (φ : Module.Dual k W) (q : W → Pr R V k) (Φ : Pr R V k → M), Function.Surjective res → res t = 0 → (∀ x : V, t • x = 0 → x = 0) → (∀ s x, res s ≠ 0 → s • x ∈ p.L → x ∈ p.L) → Red res t p.L π → (∀ x ∈ p.L, p.f x = φ (π x)) → (∀ w, φ w = 1 → (q w).Ok res ∧ (q w).IsKer p.L ∧ ∃ e, (q w).f e = 1 ∧ π (t • e) = w) → ∑ᶠ q' ∈ {q' | Pr.Inc res t p q'}, Φ q' = ∑ᶠ w ∈ {w | φ w = 1}, Φ (q w) := by
  intro R V k W M _ _ _ _ _ _ _ res t p π φ q Φ hres ht htf hsat hred hf hq
  symm
  refine finsum_mem_eq_of_bijOn q ⟨?_, ?_, ?_⟩ (fun _ _ => rfl)
  · intro w hw
    obtain ⟨h1, h2, e, h3, h4⟩ := hq w hw
    refine ⟨h1, h2, e, h3, ?_⟩
    rw [hf _ (smul_mem_ker h1 h2 ht h3), h4]
    exact hw
  · intro w hw w' hw' hww
    obtain ⟨h1, h2, e, h3, h4⟩ := hq w hw
    obtain ⟨-, -, e', h3', h4'⟩ := hq w' hw'
    rw [← hww] at h3'
    have hd : e + (-1 : R) • e' ∈ p.L :=
      sub_mem_ker h1 h2 h3' (mem_of_one h1 h3) (by rw [map_one, h3])
    have e0 : t • e = t • e' + t • (e + (-1 : R) • e') := by
      rw [neg_smul, one_smul, smul_add, smul_neg]; abel
    rw [← h4, ← h4', e0, hred.add _ (smul_mem_ker h1 h2 ht h3') _ (p.L.smul_mem _ hd), hred.smul _ _ hd, ht,
      zero_smul, add_zero]
  · rintro q' ⟨h1', h2', e', h3', h4'⟩
    have hm' := smul_mem_ker h1' h2' ht h3'
    have hw : φ (π (t • e')) = 1 := by rw [← hf _ hm', h4']
    refine ⟨π (t • e'), hw, ?_⟩
    obtain ⟨h1, h2, e, h3, h4⟩ := hq _ hw
    have hm := smul_mem_ker h1 h2 ht h3
    have h0 : π (t • e + (-1 : R) • t • e') = 0 := by
      rw [hred.add _ hm _ (p.L.smul_mem _ hm'), hred.smul _ _ hm', h4, map_neg, map_one, neg_smul, one_smul,
        add_neg_cancel]
    obtain ⟨y, hy, s, hs, hsy⟩ := (hred.ker _ (p.L.add_mem hm (p.L.smul_mem _ hm'))).1 h0
    have h5 : s • (e - e') - y = 0 := by
      apply htf
      rw [smul_sub, ← hsy, smul_comm t s, neg_smul, one_smul, smul_sub t, sub_eq_add_neg (t • e), sub_self]
    refine eq_of_ker hres h1 h2 h1' h2' h3 h3' (hsat s _ hs ?_)
    rw [sub_eq_zero.1 h5]; exact hy

end GlobalTheory.LevelHecke.AboveSum
