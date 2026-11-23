import Mathlib
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4

section Adic

variable {R : Type*} [CommRing R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]

private lemma ev_le {x : AdicCompletion I M} {s m : ℕ} (h : s ≤ m)
    (e : AdicCompletion.eval I M m x = 0) : AdicCompletion.eval I M s x = 0 := by
  have hx := x.2 h
  rw [AdicCompletion.eval_apply] at e ⊢
  rw [← hx, e, map_zero]

private lemma cauchy_far (d : ℕ → AdicCompletion I M) (n : ℕ)
    (hd : ∀ k, AdicCompletion.eval I M (n + k) (d (k + 1) - d k) = 0) (k j : ℕ) :
    AdicCompletion.eval I M (n + k) (d (k + j) - d k) = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := ev_le (show n + k ≤ n + (k + j) by omega) (hd (k + j))
    have e : d (k + (j + 1)) - d k = (d (k + j + 1) - d (k + j)) + (d (k + j) - d k) := by
      rw [← add_assoc]; abel
    rw [e, map_add, h1, ih, add_zero]

private lemma lim_exists (d : ℕ → AdicCompletion I M) (n : ℕ)
    (hd : ∀ k, AdicCompletion.eval I M (n + k) (d (k + 1) - d k) = 0) :
    ∃ L : AdicCompletion I M, ∀ k, AdicCompletion.eval I M (n + k) (L - d k) = 0 := by
  have hc : ∀ s j, AdicCompletion.eval I M s (d (s + j)) = AdicCompletion.eval I M s (d s) :=
    fun s j => sub_eq_zero.1 (by
      rw [← map_sub]; exact ev_le (by omega) (cauchy_far d n hd s j))
  obtain ⟨L, hLe⟩ : ∃ L : AdicCompletion I M, ∀ s, AdicCompletion.eval I M s L =
      AdicCompletion.eval I M s (d s) := by
    refine ⟨⟨fun s => AdicCompletion.eval I M s (d s), ?_⟩, fun _ => rfl⟩
    intro m p hmp
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmp
    have hx := (d (m + j)).2 hmp
    have hy := hc m j
    simp only [AdicCompletion.eval_apply] at hy ⊢
    rw [hx, hy]
  refine ⟨L, fun k => ?_⟩
  have h := cauchy_far d n hd k n
  rw [map_sub, sub_eq_zero, add_comm k n] at h
  rw [map_sub, sub_eq_zero, hLe, h]

end Adic

private lemma vand (l : ℕ) [Fact l.Prime] (w : ℕ) : ∃ (c : ℕ) (E : Fin (w + 1) → Fin (w + 1) → ℤ_[l]),
    ∀ i i' : Fin (w + 1), ∑ j : Fin (w + 1), E i j * (((j : ℕ) : ℤ_[l]) ^ (i' : ℕ)) =
      if i = i' then (l : ℤ_[l]) ^ c else 0 := by
  set V : Matrix (Fin (w + 1)) (Fin (w + 1)) ℤ_[l] :=
    Matrix.vandermonde (fun j : Fin (w + 1) => ((j : ℕ) : ℤ_[l])) with hV
  have hdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_vandermonde_ne_zero_iff]
    intro a b h
    exact Fin.ext (Nat.cast_injective h)
  refine ⟨V.det.valuation, fun i j => ((PadicInt.unitCoeff hdet)⁻¹ : (ℤ_[l])ˣ) * V.adjugate i j, ?_⟩
  intro i i'
  have h1 : (V.adjugate * V) i i' = ∑ j, V.adjugate i j * V j i' := Matrix.mul_apply
  rw [Matrix.adjugate_mul] at h1
  have h2 := PadicInt.unitCoeff_spec hdet
  have h3 : ∑ j : Fin (w + 1), ((PadicInt.unitCoeff hdet)⁻¹ : (ℤ_[l])ˣ) * V.adjugate i j * (((j : ℕ) : ℤ_[l]) ^ (i' : ℕ))
      = ((PadicInt.unitCoeff hdet)⁻¹ : (ℤ_[l])ˣ) * ∑ j, V.adjugate i j * V j i' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hV, Matrix.vandermonde_apply, mul_assoc]
  rw [h3, ← h1]
  by_cases hii : i = i'
  · subst hii
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, if_true]
    exact (Units.inv_mul_eq_iff_eq_mul _).2 h2
  · simp [Matrix.smul_apply, Matrix.one_apply_ne hii, hii]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private lemma un_pow (X : Tower Ω ε) {l a b P : ℕ} {f : X.Kˣ} (hf : f ∈ X.Un (l ^ (a + b))) :
    f ^ P ∈ X.Un (l ^ b) := by
  intro W hW
  obtain ⟨g, hg⟩ := hf W hW
  refine ⟨(g ^ (l ^ a)) ^ P, ?_⟩
  have e : (((f ^ P : X.Kˣ) : X.K) / (((g ^ (l ^ a)) ^ P : X.Kˣ) : X.K) ^ (l ^ b)) =
      ((f : X.K) / (g : X.K) ^ (l ^ (a + b))) ^ P := by
    push_cast
    rw [div_pow, pow_add]
    congr 1
    ring
  rw [e, map_pow, hg, one_pow]

private lemma cls_pow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s P : ℕ) (f : X.Kˣ) :
    X.cls l s (f ^ P) = (P : ℤ_[l]) • X.cls l s f := by
  unfold Tower.cls
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  rw [ofMul_pow, Nat.cast_smul_eq_nsmul ℤ_[l]]
  exact map_nsmul (TensorProduct.mk ℤ ℤ_[l] (Additive X.Kˣ) 1) P (Additive.ofMul f)

private lemma cls_le (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {s m : ℕ} (h : s ≤ m) (f : X.Kˣ) {x : X.Khat l}
    (e : AdicCompletion.eval (idl l) (X.Kl l) m x = X.cls l m f) :
    AdicCompletion.eval (idl l) (X.Kl l) s x = X.cls l s f := by
  have hx := x.2 h
  rw [AdicCompletion.eval_apply] at e ⊢
  rw [← hx, e]
  rfl

private lemma kmap_cong (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) {s : ℕ} {x : X.Khat l}
    (e : AdicCompletion.eval (idl l) (X.Kl l) s x = 0) :
    AdicCompletion.eval (idl l) (X.Kl l) s (X.kmap l φ x) = 0 := by
  rw [AdicCompletion.eval_apply] at e ⊢
  unfold Tower.kmap
  simp only [LinearMap.restrictScalars_apply]
  rw [AdicCompletion.map_val_apply, e, map_zero]

end UpperTheory.Kd.K4

theorem UpperTheory.Kd.K4.lim :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l : ℕ) [Fact l.Prime] (N w : ℕ), ∃ c : ℕ, ∀ (n : ℕ) (t : ℕ → X.Fn l), (∀ k, PolMod X l w (n + k) (t k)) →
      (∀ k, CgF X l (n + k) (t (k + 1)) (t k)) → (∀ k, ∀ γ ∈ Gam N l, CgF X l (n + k) (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (t k)) (t k)) →
      ∃ b, LiftB X l N w n c (t 0) b := by
  intro Ω _ _ _ ε X l _ N w
  obtain ⟨c, E, hE⟩ := vand l w
  refine ⟨c, fun n t hP hC hI => ?_⟩
  choose a hp using hP
  have ht := fun k => (hp k).2
  have hrec : ∀ k i, ((l : ℤ_[l]) ^ c) • a k i =
      ∑ j : Fin (w + 1), E i j • t k ![((j : ℕ) : ℤ_[l]), 1] := by
    intro k i
    have e : ∀ j : Fin (w + 1), E i j • t k ![((j : ℕ) : ℤ_[l]), 1] =
        ∑ i' : Fin (w + 1), (E i j * (((j : ℕ) : ℤ_[l]) ^ (i' : ℕ))) • a k i' := by
      intro j
      rw [ht k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      simp [smul_smul]
    simp_rw [e]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hE]
    simp
  have hd : ∀ i k, AdicCompletion.eval (idl l) (X.Kl l) (n + k)
      (((l : ℤ_[l]) ^ c) • a (k + 1) i - ((l : ℤ_[l]) ^ c) • a k i) = 0 := by
    intro i k
    rw [hrec, hrec, ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← smul_sub, map_smul, hC k _, smul_zero]
  choose L hL using fun i => lim_exists (fun k => ((l : ℤ_[l]) ^ c) • a k i) n (hd i)
  let b : X.Fn l := fun u => ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • L i
  have hb : ∀ k u, AdicCompletion.eval (idl l) (X.Kl l) (n + k) (b u - ((l : ℤ_[l]) ^ c) • t k u) = 0 := by
    intro k u
    show AdicCompletion.eval (idl l) (X.Kl l) (n + k)
      ((∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • L i) - ((l : ℤ_[l]) ^ c) • t k u) = 0
    rw [ht k u, Finset.smul_sum, ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [smul_comm ((l : ℤ_[l]) ^ c), ← smul_sub, map_smul, hL i k, smul_zero]
  have hA : ∀ i, L i ∈ X.ASet l := by
    intro i s
    obtain ⟨f, hf, hr⟩ := (hp s).1 i
    refine ⟨f ^ (l ^ c), un_pow X hf, ?_⟩
    have h1 := ev_le (show s ≤ n + s by omega) (hL i s)
    rw [map_sub, sub_eq_zero, map_smul] at h1
    rw [h1, cls_le X l (show s ≤ n + s by omega) f hr, cls_pow]
    push_cast
    rfl
  have hpol : b ∈ X.Pol l w :=
    ⟨L, fun i => Submodule.subset_span (hA i), fun u => rfl⟩
  have hinv : ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
    intro γ hγ
    funext u
    apply AdicCompletion.ext
    intro s
    have h1 := ev_le (show s ≤ n + s by omega) (hb s u)
    have h2 := ev_le (show s ≤ n + s by omega) (hb s (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))
    have h3 := kmap_cong X l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv h2
    have h4 := ev_le (show s ≤ n + s by omega) (hI s γ hγ u)
    have e : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b u - b u =
        (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
          (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) - ((l : ℤ_[l]) ^ c) • t s (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)))
        + ((l : ℤ_[l]) ^ c) • (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (t s) u - t s u)
        - (b u - ((l : ℤ_[l]) ^ c) • t s u) := by
      show X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)) - b u = _ + ((l : ℤ_[l]) ^ c) • (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (t s (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)) - t s u) - _
      rw [map_sub, map_smul, smul_sub]
      abel
    have h5 : AdicCompletion.eval (idl l) (X.Kl l) s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b u - b u) = 0 := by
      rw [e, map_sub, map_add, map_smul, h3, h4, h1]
      simp
    rw [map_sub, sub_eq_zero] at h5
    exact h5
  exact ⟨b, Submodule.subset_span ⟨hpol, hinv⟩, fun u => hb 0 u⟩
