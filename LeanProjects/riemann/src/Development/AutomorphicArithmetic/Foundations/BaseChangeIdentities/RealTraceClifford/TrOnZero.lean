import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TraceRestrictSupDisjoint
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TrOnBot

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem F_wsp {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hg : GlRel F) (a b : Fin n) {μ : Wt n} {x : V}
    (hx : x ∈ wsp F μ) : F a b x ∈ wsp F (μ + rt a b) := by
  have hx' : IsWeight F μ x := hx
  show IsWeight F (μ + rt a b) (F a b x)
  intro c
  have h := LinearMap.congr_fun (hg c c a b) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx' c, map_smul] at h
  have e : F c c (F a b x) = ((μ c : ℝ) : ℂ) • F a b x +
      ((if c = a then F c b else 0) x - (if b = c then F a c else 0) x) := by
    rw [← h]; abel
  rw [e]
  by_cases h1 : c = a <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [rt]
  · subst h1
    have h3 : c ≠ b := fun h => h2 h.symm
    simp [rt, h2, h3, add_smul]
  · subst h2
    simp [rt, h1, sub_eq_add_neg, add_smul]
  · have h3 : c ≠ b := fun h => h2 h.symm
    simp [rt, h1, h2, h3]

private theorem trOn_zero' {V : Type} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) :
    trOn W (0 : Module.End ℂ V) = 0 := by
  simpa using ((UpperTheory.RealTr.trAdd V 0).2.1 W 0 0 (by simp) (by simp)).2.1

private theorem trOn_sum' {V : Type} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) {ι : Type}
    (I : Finset ι) (f : ι → Module.End ℂ V) (hf : ∀ i ∈ I, ∀ x ∈ W, f i x ∈ W) :
    trOn W (∑ i ∈ I, f i) = ∑ i ∈ I, trOn W (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using trOn_zero' W
  | insert i I hi ih =>
    have hI : ∀ j ∈ I, ∀ x ∈ W, f j x ∈ W := fun j hj => hf j (mem_insert_of_mem hj)
    have hs : ∀ x ∈ W, (∑ j ∈ I, f j) x ∈ W := fun x hx => by
      rw [LinearMap.sum_apply]
      exact W.sum_mem fun j hj => hI j hj x hx
    rw [sum_insert hi, sum_insert hi, ← ih hI]
    exact ((UpperTheory.RealTr.trAdd V (f i)).2.1 W (∑ j ∈ I, f j) 0 (hf i (mem_insert_self i I)) hs).1

private theorem trOn_smul' {V : Type} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V)
    (Q B : Module.End ℂ V) (k : ℂ) (hQ : ∀ x ∈ W, Q x ∈ W) (hB : ∀ x ∈ W, B x ∈ W)
    (h : ∀ x ∈ W, Q x = k • B x) : trOn W Q = k * trOn W B := by
  have hk : ∀ x ∈ W, (k • B) x ∈ W := fun x hx => W.smul_mem k (hB x hx)
  rw [((UpperTheory.RealTr.trAdd V Q).2.1 W (k • B) 1 hQ hk).2.2 h]
  exact ((UpperTheory.RealTr.trAdd V B).2.1 W B k hB hB).2.1

private theorem trOn_comb {V : Type} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V)
    (P Q B : Module.End ℂ V) (k : ℂ) (hP : ∀ x ∈ W, P x ∈ W) (hQ : ∀ x ∈ W, Q x ∈ W)
    (hB : ∀ x ∈ W, B x ∈ W) (h : ∀ x ∈ W, Q x = P x + k • B x) :
    trOn W Q = trOn W P + k * trOn W B := by
  have hk : ∀ x ∈ W, (k • B) x ∈ W := fun x hx => W.smul_mem k (hB x hx)
  have hPk : ∀ x ∈ W, (P + k • B) x ∈ W := fun x hx => W.add_mem (hP x hx) (hk x hx)
  rw [((UpperTheory.RealTr.trAdd V Q).2.1 W (P + k • B) 1 hQ hPk).2.2 h,
    ((UpperTheory.RealTr.trAdd V P).2.1 W (k • B) 1 hP hk).1,
    ((UpperTheory.RealTr.trAdd V B).2.1 W B k hB hB).2.1]

private theorem sum_split {n : ℕ} (g : Fin n × Fin n → ℂ) :
    ∑ q, g q = ∑ a, g (a, a) + ∑ p ∈ posP n, (g p + g p.swap) := by
  have h : ∀ q : Fin n × Fin n, g q = (if q.1 = q.2 then g q else 0) +
      ((if q.1 < q.2 then g q else 0) + (if q.2 < q.1 then g q else 0)) := by
    intro q
    rcases lt_trichotomy q.1 q.2 with h | h | h
    · simp [h, h.ne, h.not_gt]
    · simp [h]
    · simp [h, h.ne', h.not_gt]
  have h1 : ∑ q : Fin n × Fin n, (if q.1 = q.2 then g q else 0) = ∑ a, g (a, a) := by
    rw [Fintype.sum_prod_type]; simp
  have h2 : ∑ q : Fin n × Fin n, (if q.1 < q.2 then g q else 0) = ∑ p ∈ posP n, g p := by
    rw [posP, sum_filter]
  have h3 : ∑ q : Fin n × Fin n, (if q.2 < q.1 then g q else 0) = ∑ p ∈ posP n, g p.swap := by
    rw [posP, sum_filter]
    exact (Equiv.sum_comp (Equiv.prodComm (Fin n) (Fin n))
      (fun q => if q.2 < q.1 then g q else 0)).symm
  rw [sum_congr rfl fun q _ => h q, sum_add_distrib, sum_add_distrib, h1, h2, h3, sum_add_distrib]

theorem UpperTheory.RealTr.chLap :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ B c (s : ℂ), Cm F S B → IsCh F S B c → (∀ x ∈ S, Cas F x = s • x) → ∃ t : Fin n × Fin n → FR n,
      (∀ p ∈ posP n, ∀ μ, cf (t p) μ - cf (t p) (μ + rt p.1 p.2) = ((μ p.1 - μ p.2 : ℝ) : ℂ) * cf c μ) ∧
      ∀ μ, s * cf c μ = (nsq μ : ℂ) * cf c μ + ∑ p ∈ posP n, (cf (t p) μ + cf (t p) (μ + rt p.1 p.2)) := by
  intro n V _ _ F hF S hS hSt B c s hC hc hs
  choose t ht using fun p : Fin n × Fin n =>
    UpperTheory.RealTr.chEx n V F hF S hS hSt (F p.1 p.2 * F p.2 p.1 * B)
  have hg := hF.gl
  haveI := hS
  have hFW : ∀ a b μ x, x ∈ wsp F μ ⊓ S → F a b x ∈ wsp F (μ + rt a b) ⊓ S :=
    fun a b μ x hx => ⟨F_wsp hg a b hx.1, hSt a b x hx.2⟩
  have hBW : ∀ μ x, x ∈ wsp F μ ⊓ S → B x ∈ wsp F μ ⊓ S := by
    intro μ x hx
    refine ⟨?_, hC.2 x hx.2⟩
    have hx' : IsWeight F μ x := hx.1
    show IsWeight F μ (B x)
    intro a
    have h := LinearMap.congr_fun (hC.1 a a) x
    simp only [Module.End.mul_apply] at h
    rw [← h, hx' a, map_smul]
  have hrt : ∀ (a b : Fin n) (μ : Wt n), μ + rt a b + rt b a = μ := by
    intro a b μ; ext c; simp only [rt, Pi.add_apply, Pi.sub_apply]; ring
  have hback : ∀ a b μ x, x ∈ wsp F (μ + rt a b) ⊓ S → F b a x ∈ wsp F μ ⊓ S := by
    intro a b μ x hx
    have := hFW b a _ x hx
    rwa [hrt] at this
  have hP : ∀ a b μ x, x ∈ wsp F μ ⊓ S → (F a b * F b a * B) x ∈ wsp F μ ⊓ S :=
    fun a b μ x hx => hback b a μ _ (hFW b a μ _ (hBW μ x hx))
  have hcyc : ∀ a b μ, trOn (wsp F μ ⊓ S) (F b a * F a b * B) = cf (t (a, b)) (μ + rt a b) := by
    intro a b μ
    have h := (UpperTheory.RealTr.trAdd V (F b a)).2.2.1 (wsp F (μ + rt a b) ⊓ S) (wsp F μ ⊓ S)
      (F a b * B) inferInstance inferInstance (hback a b μ)
      (fun x hx => hFW a b μ _ (hBW μ x hx))
    have e1 : F a b * B * F b a = F a b * F b a * B := by
      rw [mul_assoc, hC.1 b a, mul_assoc]
    rw [e1, ← mul_assoc] at h
    rw [← h]
    exact (ht (a, b) _).symm
  refine ⟨t, ?_, ?_⟩
  · rintro ⟨a, b⟩ - μ
    show cf (t (a, b)) μ - cf (t (a, b)) (μ + rt a b) = ((μ a - μ b : ℝ) : ℂ) * cf c μ
    have h0 : cf (t (a, b)) μ = trOn (wsp F μ ⊓ S) (F a b * F b a * B) := ht (a, b) μ
    rw [← hcyc a b μ, h0, hc μ]
    rw [trOn_comb (wsp F μ ⊓ S) (F b a * F a b * B) (F a b * F b a * B) B ((μ a - μ b : ℝ) : ℂ)
      (hP b a μ) (hP a b μ) (hBW μ)]
    · ring
    · intro x hx
      have hy : IsWeight F μ (B x) := (hBW μ x hx).1
      have h := LinearMap.congr_fun (hg a b b a) (B x)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, hy a, hy b] at h
      simp only [Module.End.mul_apply]
      rw [sub_eq_iff_eq_add'] at h
      rw [h]
      push_cast
      rw [sub_smul]
  · intro μ
    have hs' : ∀ q : Fin n × Fin n, ∀ x ∈ wsp F μ ⊓ S,
        (F q.1 q.2 * F q.2 q.1 * B) x ∈ wsp F μ ⊓ S := fun q => hP q.1 q.2 μ
    have hall : ∀ x ∈ wsp F μ ⊓ S, (∑ q : Fin n × Fin n, F q.1 q.2 * F q.2 q.1 * B) x ∈ wsp F μ ⊓ S := by
      intro x hx
      rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun q _ => hs' q x hx
    have hcas : trOn (wsp F μ ⊓ S) (∑ q : Fin n × Fin n, F q.1 q.2 * F q.2 q.1 * B) =
        s * trOn (wsp F μ ⊓ S) B := by
      refine trOn_smul' _ _ _ _ hall (hBW μ) fun x hx => ?_
      rw [← hs (B x) (hBW μ x hx).2, Cas, Fintype.sum_prod_type]
      simp [LinearMap.sum_apply, Module.End.mul_apply]
    have hsum := trOn_sum' (wsp F μ ⊓ S) univ (fun q : Fin n × Fin n => F q.1 q.2 * F q.2 q.1 * B)
      (fun q _ => hs' q)
    have hdiag : ∀ a, trOn (wsp F μ ⊓ S) (F a a * F a a * B) =
        ((μ a : ℂ)) ^ 2 * trOn (wsp F μ ⊓ S) B := by
      intro a
      refine trOn_smul' _ _ _ _ (hP a a μ) (hBW μ) fun x hx => ?_
      have hy : IsWeight F μ (B x) := (hBW μ x hx).1
      simp only [Module.End.mul_apply, hy a, map_smul, smul_smul, sq]
    rw [hc μ, ← hcas, hsum, sum_split]
    simp only [hdiag, Prod.swap]
    rw [← Finset.sum_mul]
    congr 1
    · simp [nsq]
    · refine sum_congr rfl fun p _ => ?_
      have h0 : cf (t p) μ = trOn (wsp F μ ⊓ S) (F p.1 p.2 * F p.2 p.1 * B) := ht p μ
      rw [h0]
      congr 1
      exact hcyc p.1 p.2 μ
