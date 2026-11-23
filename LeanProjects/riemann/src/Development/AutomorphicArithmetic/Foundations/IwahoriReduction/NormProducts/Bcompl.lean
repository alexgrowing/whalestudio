import Mathlib
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitEvalEqKummerClassStatement

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4.BoundedComplement

section Abs

variable {R : Type*} [CommRing R] (p : R) {M : Type*} [AddCommGroup M] [Module R M]

private theorem memP (n : ℕ) (x : M) :
    x ∈ ((Ideal.span {p}) ^ n • (⊤ : Submodule R M)) ↔ ∃ y : M, x = p ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  simp [Submodule.mem_smul_pointwise_iff_exists, eq_comm]

private def IsS (x : ℕ → M) (s : M) : Prop :=
  ∀ n, ∃ y : M, s = ∑ k ∈ Finset.range n, p ^ k • x k + p ^ n • y

private theorem splt (x : ℕ → M) (m j : ℕ) :
    ∑ k ∈ Finset.range (m + j), p ^ k • x k =
      ∑ k ∈ Finset.range m, p ^ k • x k + p ^ m • ∑ i ∈ Finset.range j, p ^ i • x (m + i) := by
  rw [Finset.sum_range_add, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [pow_add, mul_smul]

private theorem IsS.eq' [IsHausdorff (Ideal.span {p}) M] {x : ℕ → M} {s t : M}
    (hs : IsS p x s) (ht : IsS p x t) : s = t := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {p}) inferInstance _ fun n => ?_
  rw [SModEq.zero, memP]
  obtain ⟨y, hy⟩ := hs n
  obtain ⟨z, hz⟩ := ht n
  exact ⟨y - z, by rw [hy, hz, smul_sub]; abel⟩

private theorem IsS.ex [IsPrecomplete (Ideal.span {p}) M] (x : ℕ → M) : ∃ s, IsS p x s := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {p}) (inferInstance : IsPrecomplete (Ideal.span {p}) M)
    (f := fun n => ∑ k ∈ Finset.range n, p ^ k • x k) (by
      intro m n hmn
      rw [SModEq.sub_mem, memP]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨-∑ i ∈ Finset.range j, p ^ i • x (m + i), ?_⟩
      simp only [splt p x m j, smul_neg]
      abel)
  refine ⟨L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, memP] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨-y, by rw [smul_neg, ← hy]; abel⟩

private theorem IsS.shift {x : ℕ → M} {t : M} (n : ℕ) (ht : IsS p (fun k => x (n + k)) t) :
    IsS p x (∑ k ∈ Finset.range n, p ^ k • x k + p ^ n • t) := by
  intro m
  obtain ⟨y, hy⟩ := ht m
  refine ⟨∑ i ∈ Finset.range n, p ^ i • x (m + i) + p ^ n • y, ?_⟩
  have e1 := splt p x n m
  have e2 := splt p x m n
  rw [Nat.add_comm m n] at e2
  rw [hy, smul_add, ← add_assoc, ← e1, e2, smul_add (p ^ m), smul_comm (p ^ m) (p ^ n) y, add_assoc]

private theorem IsS.map {x : ℕ → M} {s : M} (φ : M →ₗ[R] M) (h : IsS p x s) :
    IsS p (fun k => φ (x k)) (φ s) := by
  intro n
  obtain ⟨y, hy⟩ := h n
  exact ⟨φ y, by rw [hy]; simp [map_sum]⟩

private theorem IsS.fsum {ι : Type*} (S : Finset ι) {x : ι → ℕ → M} {s : ι → M}
    (h : ∀ i ∈ S, IsS p (x i) (s i)) :
    IsS p (fun k => ∑ i ∈ S, x i k) (∑ i ∈ S, s i) := by
  intro n
  choose! y hy using fun i (hi : i ∈ S) => h i hi n
  refine ⟨∑ i ∈ S, y i, ?_⟩
  rw [Finset.sum_congr rfl hy, Finset.sum_add_distrib, Finset.smul_sum]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]

private theorem IsS.smul {x : ℕ → M} {s : M} (r : R) (h : IsS p x s) :
    IsS p (fun k => r • x k) (r • s) := h.map p (r • LinearMap.id)

end Abs

section Conc

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem khat_complete (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : IsAdicComplete (idl l) (X.Khat l) :=
  AdicCompletion.isAdicComplete ⟨{(l : ℤ_[l])}, by simp⟩

private theorem memA (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {x : ℕ → X.Khat l} {s : X.Khat l}
    (hx : ∀ k, x k ∈ X.A l) (hs : IsS (l : ℤ_[l]) x s) : s ∈ X.A l := by
  refine Submodule.subset_span fun n => ?_
  obtain ⟨y, hy⟩ := hs n
  obtain ⟨φ, hφ, hd⟩ := X.j_hol
  obtain ⟨f, hf, e⟩ := GlobalTheory.T.exists_unit_eval_eq_kummer_class ε X ⟨φ, hd, hφ⟩ l n
    (∑ k ∈ Finset.range n, (l : ℤ_[l]) ^ k • x k)
    (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hx k))
  refine ⟨f, hf, ?_⟩
  rw [hy, map_add, e, map_smul]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n y)
  rw [← hz, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).2 ((memP _ n _).2 ⟨z, rfl⟩), add_zero]

private theorem bset_of_mem (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) {b : X.Fn l}
    (hb : b ∈ X.B N l w) : b ∈ X.BSet N l w := by
  unfold Tower.B at hb
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    exact ⟨⟨fun _ => 0, fun _ => Submodule.zero_mem _, fun u => by simp⟩, fun γ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨⟨c, hc, ec⟩, ix⟩ := hx
    obtain ⟨⟨d, hd, ed⟩, iy⟩ := hy
    refine ⟨⟨fun i => c i + d i, fun i => Submodule.add_mem _ (hc i) (hd i), fun u => ?_⟩,
      fun γ hγ => by rw [map_add, ix γ hγ, iy γ hγ]⟩
    simp only [Pi.add_apply, ec, ed, smul_add, Finset.sum_add_distrib]
  | smul r x _ hx =>
    obtain ⟨⟨c, hc, ec⟩, ix⟩ := hx
    refine ⟨⟨fun i => r • c i, fun i => Submodule.smul_mem _ _ (hc i), fun u => ?_⟩,
      fun γ hγ => by rw [map_smul, ix γ hγ]⟩
    simp only [Pi.smul_apply, ec, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

private theorem sfun (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) (d : ℕ → X.Fn l)
    (hd : ∀ k, d k ∈ X.BSet N l w) :
    ∃ t ∈ X.BSet N l w, ∀ u, IsS (l : ℤ_[l]) (fun k => d k u) (t u) := by
  haveI := khat_complete X l
  choose c hcA hc using fun k => (hd k).1
  choose s hs using fun i => IsS.ex (l : ℤ_[l]) (fun k => c k i)
  have hsum : ∀ u : Fin 2 → ℤ_[l], IsS (l : ℤ_[l]) (fun k => d k u)
      (∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • s i) := fun u => by
    have h := IsS.fsum (l : ℤ_[l]) (Finset.univ : Finset (Fin (w + 1)))
      (x := fun i k => (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c k i)
      (s := fun i => (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • s i)
      (fun i _ => (hs i).smul _ _)
    simpa only [hc] using h
  refine ⟨fun u => ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • s i,
    ⟨⟨s, fun i => memA X l (fun k => hcA k i) (hs i), fun u => rfl⟩, fun γ hγ => ?_⟩, hsum⟩
  funext u
  have h1 := (hsum (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)).map (l : ℤ_[l])
    (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv)
  have e : (fun k => X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (d k (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))) = fun k => d k u :=
    funext fun k => congrFun ((hd k).2 γ hγ) u
  rw [e] at h1
  exact h1.eq' _ (hsum u)

end Conc

end UpperTheory.Kd.K4.BoundedComplement

open UpperTheory.Kd.K4.BoundedComplement in
theorem UpperTheory.Kd.K4.bcompl :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ), IsAdicComplete (idl l) (X.B N l w) := by
  intro Ω _ _ _ ε X l _ N w
  haveI := khat_complete X l
  have hH : IsHausdorff (idl l) (X.B N l w) := ⟨fun x hx => by
    refine Subtype.ext (funext fun u => ?_)
    show (x : X.Fn l) u = 0
    refine IsHausdorff.haus (I := idl l) (inferInstance : IsHausdorff (idl l) (X.Khat l)) _ fun n => ?_
    have h := hx n
    rw [SModEq.zero, memP] at h ⊢
    obtain ⟨y, hy⟩ := h
    exact ⟨(y : X.Fn l) u, by rw [hy]; rfl⟩⟩
  have hP : IsPrecomplete (idl l) (X.B N l w) := ⟨fun {f} hf => by
    have hstep : ∀ k, ∃ y : X.B N l w, f k - f (k + 1) = (l : ℤ_[l]) ^ k • y := fun k => by
      have h := hf (Nat.le_succ k)
      rwa [SModEq.sub_mem, memP] at h
    choose d hd using hstep
    have hB : ∀ k, (d k : X.Fn l) ∈ X.BSet N l w := fun k => bset_of_mem X l N w (d k).2
    have mkB : ∀ {b : X.Fn l}, b ∈ X.BSet N l w → b ∈ X.B N l w := fun h => Submodule.subset_span h
    obtain ⟨t0, ht0, hs0⟩ := sfun X l N w (fun k => (d k : X.Fn l)) hB
    have hfn : ∀ n, f n = f 0 - ∑ k ∈ Finset.range n, (l : ℤ_[l]) ^ k • d k := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ← hd n, ih]
        abel
    refine ⟨f 0 - ⟨t0, mkB ht0⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, memP]
    obtain ⟨tn, htn, hsn⟩ := sfun X l N w (fun k => (d (n + k) : X.Fn l)) fun k => hB _
    refine ⟨⟨tn, mkB htn⟩, ?_⟩
    rw [hfn n]
    ext u
    have e := (hs0 u).eq' _ ((hsn u).shift (l : ℤ_[l]) n (x := fun k => (d k : X.Fn l) u))
    simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, Submodule.coe_sum, Finset.sum_apply, e]
    abel_nf⟩
  exact ⟨⟩
