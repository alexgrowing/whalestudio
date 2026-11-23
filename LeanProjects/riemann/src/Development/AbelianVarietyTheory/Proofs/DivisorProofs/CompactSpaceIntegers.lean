import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open scoped TensorProduct
open GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.UPel.HT

namespace GlobalTheory.AdelicLimitCompactness

theorem exists_limit_compact (p : ℕ) (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] (c : ℕ → ℤ)
    (hc : ∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime (n * m) p → ∃ z : ℤ, c (n * m) = c n + n * z) :
    ∃ a : O, ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∃ b : O, a = (c n : O) + n * b := by
  let I := {n : ℕ // 0 < n ∧ Nat.Coprime n p}
  haveI : Nonempty I := ⟨⟨1, one_pos, Nat.coprime_one_left p⟩⟩
  let S : I → Set O := fun n => Set.range fun b : O => (c n.1 : O) + (n.1 : O) * b
  have hcomp : ∀ n, IsCompact (S n) := fun n => isCompact_range (by fun_prop)
  have hsub : ∀ (n k : I) (m : ℕ), 0 < m → k.1 = n.1 * m → S k ⊆ S n := by
    rintro n k m hm hk _ ⟨b, rfl⟩
    obtain ⟨z, hz⟩ := hc n.1 m n.2.1 hm (hk ▸ k.2.2)
    refine ⟨z + m * b, ?_⟩
    simp only [hk, hz]
    push_cast
    ring
  have hdir : Directed (fun x y => x ⊇ y) S := by
    intro n m
    refine ⟨⟨n.1 * m.1, Nat.mul_pos n.2.1 m.2.1, Nat.Coprime.mul_left n.2.2 m.2.2⟩, ?_, ?_⟩
    · exact hsub n _ m.1 m.2.1 rfl
    · exact hsub m _ n.1 n.2.1 (mul_comm _ _)
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hdir
    (fun n => Set.range_nonempty _) hcomp (fun n => (hcomp n).isClosed)
  refine ⟨a, fun n hn hp => ?_⟩
  obtain ⟨b, hb⟩ := Set.mem_iInter.1 ha ⟨n, hn, hp⟩
  exact ⟨b, hb.symm⟩

theorem compactSpace_integers {R : Type} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]
    [IsDedekindDomain R] [IsFractionRing R ℚ] (v : HeightOneSpectrum R) :
    CompactSpace (v.adicCompletionIntegers ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm.compactSpace

variable {p : ℕ}

def ofInt (x : ∀ v : AwayP p, v.1.adicCompletionIntegers ℚ) : AfP p :=
  RestrictedProduct.mk (fun v => (x v : v.1.adicCompletion ℚ)) (Filter.Eventually.of_forall fun v => (x v).2)

theorem eval_ofInt (x : ∀ v : AwayP p, v.1.adicCompletionIntegers ℚ) (v : AwayP p) :
    AfP.eval v (ofInt x) = x v := rfl

theorem isInt_ofInt (x : ∀ v : AwayP p, v.1.adicCompletionIntegers ℚ) : IsIntAf (ofInt x) :=
  fun v => (x v).2

theorem afp_ext {a b : AfP p} (h : ∀ v, AfP.eval v a = AfP.eval v b) : a = b :=
  RestrictedProduct.ext _ _ h

theorem exists_limit_adele (c : ℕ → ℤ)
    (hc : ∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime (n * m) p → ∃ z : ℤ, c (n * m) = c n + n * z) :
    ∃ a : AfP p, ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∃ b : AfP p, IsIntAf b ∧ a = (c n : AfP p) + n * b := by
  have h : ∀ v : AwayP p, ∃ a : v.1.adicCompletionIntegers ℚ, ∀ n : ℕ, 0 < n → Nat.Coprime n p →
      ∃ b : v.1.adicCompletionIntegers ℚ, a = (c n : v.1.adicCompletionIntegers ℚ) + n * b := fun v =>
    haveI := compactSpace_integers v.1
    exists_limit_compact p _ c hc
  choose a ha using h
  refine ⟨ofInt a, fun n hn hp => ?_⟩
  choose b hb using fun v => ha v n hn hp
  refine ⟨ofInt b, isInt_ofInt b, afp_ext fun v => ?_⟩
  rw [map_add, map_mul, map_intCast, map_natCast, eval_ofInt, eval_ofInt, hb v]
  push_cast
  rfl

variable [Fact p.Prime] (D : Datum p)

def inHom : D.La →+ AfP p ⊗[ℚ] VQ D where
  toFun := inAf D
  map_zero' := by simp [inAf]
  map_add' x y := by simp [inAf, TensorProduct.tmul_add]

theorem smul_inAf (a : AfP p) (x : D.La) : a • inAf D x = a ⊗ₜ ((1 : ℚ) ⊗ₜ x) := by
  rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem smul_inAf_mem {a : AfP p} (ha : IsIntAf a) (x : D.La) : a • inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨a, x, ha, smul_inAf D a x⟩

theorem smul_mem {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', x, ha', rfl⟩ := hz
    rw [← smul_inAf, smul_smul]
    exact smul_inAf_mem D (fun v => by rw [map_mul]; exact mul_mem (ha v) (ha' v)) x
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_adelic_limit (g : ℕ → D.La →+ D.La)
    (hg : ∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime (n * m) p → ∀ x : D.La, ∃ z : D.La, g (n * m) x = g n x + n • z) :
    ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧
      ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∀ x : D.La, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w := by
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let B := Algebra.TensorProduct.basis (AfP p) (Algebra.TensorProduct.basis ℚ b)
  have hB : ∀ i, B i = inAf D (b i) := fun i => by
    simp only [B, Algebra.TensorProduct.basis_apply, inAf]
  have hlim := fun i j => exists_limit_adele (p := p) (fun n => b.repr (g n (b i)) j) (by
    intro n m hn hm hp
    obtain ⟨z, hz⟩ := hg n m hn hm hp (b i)
    exact ⟨b.repr z j, by simp [hz]⟩)
  choose a ha using hlim
  let h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := B.constr (AfP p) fun i => ∑ j, a i j • inAf D (b j)
  have h₀b : ∀ i, h₀ (inAf D (b i)) = ∑ j, a i j • inAf D (b j) := fun i => by
    rw [← hB]; exact B.constr_basis _ _ i
  have key : ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∀ x : D.La,
      ∃ w ∈ LaHat D, h₀ (inHom D x) = inHom D (g n x) + n • w := by
    intro n hn hp x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := b.mem_span x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      choose e he he' using fun j => ha i j n hn hp
      refine ⟨∑ j, e j • inAf D (b j), sum_mem fun j _ => smul_inAf_mem D (he j) _, ?_⟩
      conv_rhs => rw [← b.sum_repr (g n (b i)), map_sum]
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine (h₀b i).trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [he' j, map_zsmul, add_smul, mul_smul, Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul]
      rfl
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw, e⟩ := hx
      obtain ⟨w', hw', e'⟩ := hy
      refine ⟨w + w', add_mem hw hw', ?_⟩
      rw [map_add, map_add, e, e', map_add, map_add, nsmul_add]
      abel
    | smul k x _ hx =>
      obtain ⟨w, hw, e⟩ := hx
      refine ⟨k • w, zsmul_mem hw k, ?_⟩
      rw [map_zsmul, map_zsmul, e, map_zsmul, map_zsmul, zsmul_add, smul_comm k n w]
  refine ⟨h₀, fun v hv => ?_, key⟩
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', x, ha', rfl⟩ := hz
    obtain ⟨w, hw, e⟩ := key 1 one_pos (Nat.coprime_one_left p) x
    rw [← smul_inAf, map_smul]
    change a' • h₀ (inHom D x) ∈ _
    rw [e, smul_add, one_nsmul]
    exact add_mem (smul_inAf_mem D ha' _) (smul_mem D ha' hw)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem main : ∀ (p : ℕ) [Fact (Nat.Prime p)] (D : Datum p) (g : ℕ → D.La →+ D.La),
    (∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime (n * m) p → ∀ x : D.La, ∃ z : D.La, g (n * m) x = g n x + n • z) →
    ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧
      ∀ n : ℕ, 0 < n → Nat.Coprime n p → ∀ x : D.La, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w :=
  fun _ _ D g hg => exists_adelic_limit D g hg

end GlobalTheory.AdelicLimitCompactness
