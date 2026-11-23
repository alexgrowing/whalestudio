import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList

open MvPolynomial

namespace PositivityTheory.Groth.ChartWirtingerDerivatives

def toZAlg {σ : Type*} (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ) :
    MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
  AlgHom.mk ψ (by
    intro r
    show ψ (algebraMap ℤ (MvPolynomial σ ℤ) r) = algebraMap ℤ (MvPolynomial σ ℤ) r
    rw [algebraMap_eq, eq_intCast C r]
    exact map_intCast ψ r)

theorem tri_supported_le {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) (N : ℕ) :
    supported ℤ {t | w t < N} ≤ (supported ℤ {t | w t < N}).map (toZAlg ψ) := by
  induction N with
  | zero =>
    intro x hx
    have he : {t | w t < 0} = (∅ : Set σ) := by
      ext t
      simp
    rw [he, supported_empty] at hx
    obtain ⟨r, rfl⟩ := Algebra.mem_bot.1 hx
    exact Subalgebra.algebraMap_mem _ r
  | succ N ih =>
    intro x hx
    rw [supported_eq_adjoin_X] at hx
    refine Algebra.adjoin_le ?_ hx
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨ε, p, hp, hψ⟩ := h s
    have hs' : w s < N + 1 := hs
    have hXs : X s ∈ supported ℤ {t | w t < N + 1} := X_mem_supported.2 hs
    have h1 : ψ (X s) ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.mem_map.2 ⟨X s, hXs, rfl⟩
    have h2 : p ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) := by
      have hp' : p ∈ supported ℤ {t | w t < N} := by
        rw [mem_supported]
        intro t ht
        have := hp t ht
        show w t < N
        omega
      refine Subalgebra.map_mono (supported_mono ?_) (ih hp')
      intro t ht
      have ht' : w t < N := ht
      show w t < N + 1
      omega
    have key : X s = ((ε⁻¹ : ℤˣ) : ℤ) • (ψ (X s) - p) := by
      rw [hψ, add_sub_cancel_right, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [key]
    exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ h1 h2) _

theorem tri_surj {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Surjective ψ := by
  have hrange : ∀ s, X s ∈ (toZAlg ψ).range := by
    intro s
    have hmem := tri_supported_le w ψ h (w s + 1)
      (X_mem_supported.2 (show w s < w s + 1 by omega))
    obtain ⟨y, -, hy⟩ := Subalgebra.mem_map.1 hmem
    exact (AlgHom.mem_range _).2 ⟨y, hy⟩
  have htop : (toZAlg ψ).range = ⊤ := by
    rw [eq_top_iff, ← adjoin_range_X, Algebra.adjoin_le_iff]
    rintro _ ⟨s, rfl⟩
    exact hrange s
  intro y
  have hy : y ∈ (toZAlg ψ).range := by
    rw [htop]
    exact Algebra.mem_top
  obtain ⟨x, hx⟩ := (AlgHom.mem_range _).1 hy
  exact ⟨x, hx⟩

theorem tri_bij {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Bijective ψ := by
  refine ⟨?_, tri_surj w ψ h⟩
  have hpre : ∀ s, ∃ (ε : ℤˣ) (q : MvPolynomial σ ℤ), (∀ t ∈ q.vars, w t < w s) ∧
      ψ ((ε : ℤ) • X s + q) = X s := by
    intro s
    obtain ⟨ε, p, hp, hψ⟩ := h s
    have hp' : ((ε⁻¹ : ℤˣ) : ℤ) • p ∈ supported ℤ {t | w t < w s} := by
      apply Subalgebra.smul_mem
      rw [mem_supported]
      intro t ht
      exact hp t ht
    obtain ⟨q, hq, hqe⟩ := Subalgebra.mem_map.1 (tri_supported_le w ψ h (w s) hp')
    refine ⟨ε⁻¹, -q, ?_, ?_⟩
    · intro t ht
      rw [vars_neg] at ht
      exact (mem_supported.1 hq) (Finset.mem_coe.2 ht)
    · have hqe' : ψ q = ((ε⁻¹ : ℤˣ) : ℤ) • p := hqe
      rw [map_add, map_neg, map_zsmul, hψ, hqe', smul_add, smul_smul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_smul, add_neg_cancel_right]
  choose ε' q hq hψq using hpre
  let φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ :=
    (aeval fun s => ((ε' s : ℤˣ) : ℤ) • X s + q s).toRingHom
  have hφX : ∀ s, φ (X s) = ((ε' s : ℤˣ) : ℤ) • X s + q s := fun s => aeval_X _ _
  have hφs : Function.Surjective φ := tri_surj w φ (fun s => ⟨ε' s, q s, hq s, hφX s⟩)
  have hcomp : ∀ a, ψ (φ a) = a := by
    have hc : ψ.comp φ = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show ψ (φ (C r)) = C r
        simp only [eq_intCast C r, map_intCast]
      · intro s
        show ψ (φ (X s)) = X s
        rw [hφX]
        exact hψq s
    intro a
    rw [← RingHom.comp_apply, hc, RingHom.id_apply]
  intro a b hab
  obtain ⟨a', rfl⟩ := hφs a
  obtain ⟨b', rfl⟩ := hφs b
  rw [hcomp, hcomp] at hab
  rw [hab]

theorem uni_inj {M I : Type*} (L : M ≃ I) (w : M → ℕ) (f : M → I →₀ ℤ)
    (h1 : ∀ m, f m (L m) = 1) (hlt : ∀ m n, f m (L n) ≠ 0 → m = n ∨ w m < w n) :
    Function.Injective (Finsupp.linearCombination ℤ f) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  have hsupp : a.support.Nonempty := Finsupp.support_nonempty_iff.2 hne
  obtain ⟨n, hn, hmin⟩ := a.support.exists_min_image w hsupp
  have hcoef := congrArg (fun g => g (L n)) ha
  simp only [Finsupp.linearCombination_apply, Finsupp.coe_zero, Pi.zero_apply] at hcoef
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single n] at hcoef
  · simp only [Finsupp.smul_apply, h1, smul_eq_mul, mul_one] at hcoef
    exact (Finsupp.mem_support_iff.1 hn) hcoef
  · intro m hm hmn
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases hf : f m (L n) = 0
    · simp [hf]
    · rcases hlt m n hf with h | h
      · exact absurd h hmn
      · exact absurd (hmin m hm) (not_le.2 h)
  · intro hn'
    exact absurd hn hn'

theorem uni_exists {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    ∀ n, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 := by
  classical
  intro n
  suffices key : ∀ d n, b (c n) - w n = d → ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 from key _ n rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro n hd
    set v : I →₀ ℤ := Finsupp.single (L n) 1 - f n with hv
    have hvsupp : ∀ i ∈ v.support, c (L.symm i) = c n ∧
        b (c (L.symm i)) - w (L.symm i) < d := by
      intro i hi
      have hvi : v i ≠ 0 := Finsupp.mem_support_iff.1 hi
      set m := L.symm i with hm
      have hi' : i = L m := by rw [hm, Equiv.apply_symm_apply]
      have hne : m ≠ n := by
        intro hmn
        apply hvi
        rw [hi', hmn, hv, Finsupp.sub_apply, Finsupp.single_eq_same, h1, sub_self]
      have hf : f n (L m) ≠ 0 := by
        intro hf0
        apply hvi
        rw [hi', hv, Finsupp.sub_apply, hf0, sub_zero, Finsupp.single_apply, if_neg]
        intro heq
        exact hne (L.injective heq).symm
      obtain ⟨hc, hw⟩ := hlt n m hf
      rcases hw with hw | hw
      · exact absurd hw.symm hne
      · refine ⟨hc.symm, ?_⟩
        have hbm := hb m
        rw [← hc] at hbm ⊢
        omega
    have hex : ∀ i ∈ v.support, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
        Finsupp.linearCombination ℤ f a = Finsupp.single i 1 := by
      intro i hi
      obtain ⟨hc, hlt'⟩ := hvsupp i hi
      obtain ⟨a, ha1, ha2⟩ := ih _ hlt' (L.symm i) rfl
      refine ⟨a, fun m hm => (ha1 m hm).trans hc, ?_⟩
      rw [ha2, Equiv.apply_symm_apply]
    choose! g hg1 hg2 using hex
    refine ⟨Finsupp.single n 1 + ∑ i ∈ v.support, v i • g i, ?_, ?_⟩
    · intro m hm
      rcases Finset.mem_union.1 (Finsupp.support_add hm) with hm1 | hm1
      · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hm1
        rw [hm1]
      · obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hm1)
        exact hg1 i hi m (Finsupp.support_smul hmi)
    · rw [map_add, map_sum, Finsupp.linearCombination_single, one_smul]
      rw [Finset.sum_congr rfl (fun i hi => by rw [map_smul, hg2 i hi])]
      have hsum : ∑ i ∈ v.support, v i • Finsupp.single i (1 : ℤ) = v := by
        conv_rhs => rw [← Finsupp.sum_single v]
        rw [Finsupp.sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsum, hv]
      abel

theorem uni_bij {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    Function.Bijective (Finsupp.linearCombination ℤ f) := by
  refine ⟨uni_inj L w f h1 (fun m n hf => (hlt m n hf).2), ?_⟩
  have hrange : ∀ i, Finsupp.single i (1 : ℤ) ∈ LinearMap.range (Finsupp.linearCombination ℤ f) := by
    intro i
    obtain ⟨a, -, ha⟩ := uni_exists L c w b f hb h1 hlt (L.symm i)
    rw [Equiv.apply_symm_apply] at ha
    exact LinearMap.mem_range.2 ⟨a, ha⟩
  intro g
  have hg : g ∈ LinearMap.range (Finsupp.linearCombination ℤ f) := by
    refine Finsupp.induction_linear g ?_ ?_ ?_
    · exact Submodule.zero_mem _
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
    · intro i r
      have hmem := Submodule.smul_mem _ r (hrange i)
      rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at hmem
  exact LinearMap.mem_range.1 hg

end PositivityTheory.Groth.ChartWirtingerDerivatives

namespace PositivityTheory.Groth

theorem triAut : TriAut := fun _ w ψ h => ChartWirtingerDerivatives.tri_bij w ψ h

theorem uniTri : UniTri := fun _ _ _ L c w b f hb h1 hlt =>
  ⟨ChartWirtingerDerivatives.uni_bij L c w b f hb h1 hlt, ChartWirtingerDerivatives.uni_exists L c w b f hb h1 hlt⟩

end PositivityTheory.Groth
