import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorCommutation

open Finset Polynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.DeterminantVectorSums

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

section ring

variable {A : Type} [Ring A] [Algebra ℂ A] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → A)

def Tch (u : ℂ) (j l : Fin (N + 1)) : A :=
  ((-1 : ℂ) ^ ((j : ℕ) + (l : ℕ))) • qminor E j.succAbove l.succAbove u

theorem zs (k : ℕ) (a : A) : ((-1 : ℤ) ^ k) • a = ((-1 : ℂ) ^ k) • a := by
  rw [← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  rfl

theorem sumT (hE : GlRel E) (w : ℂ) (j c : Fin (N + 1)) :
    ∑ l, Tch E (w - 1) j l * Tm E w c l = if c = j then qdet E w else 0 := by
  have h := QuantumMinorExpansion.sumA E hE id id j c w
  simp only [Function.id_comp, id_eq, zs] at h
  have h2 := congrArg (fun z => ((-1 : ℂ) ^ (j : ℕ)) • z) h
  simp only [Finset.smul_sum, smul_smul, ← pow_add] at h2
  simp only [Tch, smul_mul_assoc]
  rw [h2]
  split_ifs
  · rw [smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul]
    rfl
  · rw [smul_zero]

theorem detVecR (hE : GlRel E) (y : Fin (N + 1) → A) (hy : IsVec E y) (w : ℂ) (j : Fin (N + 1)) :
    qdet E w * y j = y j * qdet E w - ∑ l, Tch E (w - 1) j l * y l := by
  have h := sumT E hE w j j
  rw [if_pos rfl] at h
  rw [← h, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hM : Commute (y j) (Tch E (w - 1) j l) := by
    refine Commute.smul_right (QuantumMinorCommutation.commute_qminor E _ _ _ _ (fun s s' => ?_)) _
    have := hy (j.succAbove s) (l.succAbove s') j
    rw [if_neg (Fin.succAbove_ne j s), sub_eq_zero] at this
    exact this.symm
  have hT : Tm E w j l * y j - y j * Tm E w j l = -y l := by
    rw [QuantumMinorCommutation.Tm_comm, hy, if_pos rfl]
  have hT' : Tm E w j l * y j = y j * Tm E w j l - y l := by
    rw [sub_eq_add_neg, ← hT]; abel
  rw [mul_assoc, hT', mul_sub, ← mul_assoc, ← hM.eq, mul_assoc]

theorem star (hE : GlRel E) (y : Fin (N + 1) → A) (hy : IsVec E y) (w : ℂ) (j : Fin (N + 1)) :
    ∑ l, Tch E (w - 1) j l * ((w + 1) • y l + ∑ c, E c l * y c) = y j * qdet E w := by
  have h1 : ∀ l, (w + 1) • y l + ∑ c, E c l * y c = y l + ∑ c, Tm E w c l * y c := by
    intro l
    simp only [Tm, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [add_smul, one_smul, Algebra.smul_def]
    abel
  simp only [h1, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, sumT E hE, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [detVecR E hE y hy]
  abel

theorem vecD (hE : GlRel E) (y : Fin (N + 1) → A) (hy : IsVec E y) : IsVec E (fun l => ∑ c, E c l * y c) := by
  intro a b l
  have h1 : ∀ c, E a b * (E c l * y c) - E c l * y c * E a b =
      ((if b = c then E a l else 0) - (if l = a then E c b else 0)) * y c + E c l * (if a = c then -y b else 0) := by
    intro c
    rw [← hE a b c l, ← hy a b c]
    noncomm_ring
  simp only []
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [h1, sub_mul, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hal : a = l
  · subst hal
    simp only [if_true, mul_neg]
    abel
  · rw [if_neg hal]
    simp [Ne.symm hal]

theorem vec_add {y z : Fin (N + 1) → A} (hy : IsVec E y) (hz : IsVec E z) : IsVec E (fun l => y l + z l) := by
  intro a b c
  have h1 := hy a b c
  have h2 := hz a b c
  simp only [mul_add, add_mul]
  rw [add_sub_add_comm, h1, h2]
  split_ifs <;> simp [add_comm]

theorem vec_smul (k : ℂ) {y : Fin (N + 1) → A} (hy : IsVec E y) : IsVec E (fun l => k • y l) := by
  intro a b c
  have h1 := hy a b c
  simp only [mul_smul_comm, smul_mul_assoc]
  rw [← smul_sub, h1]
  split_ifs <;> simp

end ring

section abs

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem coeffs (hPV : PolyVanish) (K : Module.End ℂ W) (A : ℕ → Module.End ℂ W) (d : ℕ) (P : ℂ[X])
    (hP : P.natDegree < d + 1) (x : W)
    (h : ∀ u : ℂ, (∑ s ∈ range d, u ^ s • A s) (u • x - K x) = P.eval u • x) :
    ∀ s ∈ range (d + 1),
      (if s = 0 then 0 else A (s - 1) x) - (if s < d then A s (K x) else 0) = P.coeff s • x := by
  intro s hs
  have key := hPV W (d + 1)
    (fun s => (if s = 0 then 0 else A (s - 1) x) - (if s < d then A s (K x) else 0) - P.coeff s • x) ∅ ?_ s hs
  · exact sub_eq_zero.1 key
  intro u _
  have hu := h u
  simp only [smul_sub, Finset.sum_sub_distrib]
  have e1 : ∑ s ∈ range (d + 1), u ^ s • (if s = 0 then (0 : W) else A (s - 1) x) =
      ∑ s ∈ range d, u ^ s • A s (u • x) := by
    rw [Finset.sum_range_succ']
    simp only [if_true, smul_zero, add_zero, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, map_smul, smul_smul, pow_succ]
  have e2 : ∑ s ∈ range (d + 1), u ^ s • (if s < d then A s (K x) else (0 : W)) =
      ∑ s ∈ range d, u ^ s • A s (K x) := by
    rw [Finset.sum_range_succ, if_neg (lt_irrefl d), smul_zero, add_zero]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [if_pos (Finset.mem_range.1 hs)]
  have e3 : ∑ s ∈ range (d + 1), u ^ s • P.coeff s • x = P.eval u • x := by
    rw [Polynomial.eval_eq_sum_range' hP, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [smul_smul, mul_comm]
  rw [e1, e2, e3, ← hu, ← Finset.sum_sub_distrib]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sub]
  rw [Finset.sum_sub_distrib, sub_self]

theorem pow_mem (G : Submodule ℂ W) (K : Module.End ℂ W) (hK : ∀ x ∈ G, K x ∈ G) (s : ℕ) : ∀ x ∈ G, (K ^ s) x ∈ G := by
  induction s with
  | zero => intro x hx; simpa using hx
  | succ s ih =>
    intro x hx
    rw [pow_succ', Module.End.mul_apply]
    exact hK _ (ih x hx)

theorem aeval_mem (G : Submodule ℂ W) (K : Module.End ℂ W) (hK : ∀ x ∈ G, K x ∈ G) (q : ℂ[X]) :
    ∀ x ∈ G, aeval K q x ∈ G := by
  intro x hx
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine Submodule.sum_mem _ (fun s _ => ?_)
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (pow_mem G K hK s x hx)

theorem ch (hPV : PolyVanish) (G : Submodule ℂ W) (K : Module.End ℂ W) (hK : ∀ x ∈ G, K x ∈ G)
    (A : ℕ → Module.End ℂ W) (d : ℕ) (P : ℂ[X]) (hP : P.natDegree < d + 1)
    (h : ∀ x ∈ G, ∀ u : ℂ, (∑ s ∈ range d, u ^ s • A s) (u • x - K x) = P.eval u • x) :
    ∀ x ∈ G, aeval K P x = 0 := by
  intro x hx
  rw [Polynomial.aeval_eq_sum_range' hP, LinearMap.sum_apply]
  have h1 : ∀ s ∈ range (d + 1), (P.coeff s • K ^ s) x =
      (if s = 0 then 0 else A (s - 1) ((K ^ s) x)) - (if s < d then A s (K ((K ^ s) x)) else 0) := by
    intro s hs
    rw [LinearMap.smul_apply]
    exact (coeffs hPV K A d P hP _ (h _ (pow_mem G K hK s x hx)) s hs).symm
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_range_succ', Finset.sum_range_succ (fun s => if s < d then _ else _),
    if_neg (lt_irrefl d), if_pos rfl, add_zero, add_zero, sub_eq_zero]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [if_pos (Finset.mem_range.1 hs), if_neg (Nat.succ_ne_zero s), Nat.add_sub_cancel, pow_succ', Module.End.mul_apply]

theorem basis_mul {n : ℕ} (r : Fin n → ℂ) (i : Fin n) :
    (X - C (r i)) * Lagrange.basis univ r i =
      C (∏ j ∈ univ.erase i, (r i - r j)⁻¹) * ∏ j, (X - C (r j)) := by
  unfold Lagrange.basis Lagrange.basisDivisor
  rw [Finset.prod_mul_distrib, ← map_prod, ← Finset.mul_prod_erase univ _ (Finset.mem_univ i)]
  ring

theorem decomp (hPV : PolyVanish) (G : Submodule ℂ W) (K : Module.End ℂ W) (hK : ∀ x ∈ G, K x ∈ G)
    (A : ℕ → Module.End ℂ W) (N : ℕ) (r : Fin (N + 1) → ℂ) (hr : Function.Injective r)
    (h : ∀ x ∈ G, ∀ u : ℂ, (∑ s ∈ range (N + 1), u ^ s • A s) (u • x - K x) = (∏ j, (u - r j)) • x) :
    ∀ x ∈ G, ∃ Φ : Fin (N + 1) → W, (∀ i, Φ i ∈ G) ∧ ∑ i, Φ i = x ∧
      ∀ i u, (∑ s ∈ range (N + 1), u ^ s • A s) (Φ i) = (∏ j ∈ univ.erase i, (u - r j)) • Φ i := by
  intro x hx
  have hP : (∏ j, (X - C (r j))).natDegree < (N + 1) + 1 := by
    simp
  have hev : ∀ (S : Finset (Fin (N + 1))) (u : ℂ), (∏ j ∈ S, (X - C (r j))).eval u = ∏ j ∈ S, (u - r j) := by
    intro S u
    rw [Polynomial.eval_prod]
    simp
  have hch := ch hPV G K hK A (N + 1) (∏ j, (X - C (r j))) hP (by intro x hx u; rw [hev]; exact h x hx u)
  refine ⟨fun i => aeval K (Lagrange.basis univ r i) x, fun i => aeval_mem G K hK _ x hx, ?_, ?_⟩
  · rw [← LinearMap.sum_apply, ← map_sum, Lagrange.sum_basis (hr.injOn) Finset.univ_nonempty, map_one]
    rfl
  intro i u
  set φ := aeval K (Lagrange.basis univ r i) x with hφ
  have hφG : φ ∈ G := aeval_mem G K hK _ x hx
  have hKφ : K φ = r i • φ := by
    have h1 : aeval K ((X - C (r i)) * Lagrange.basis univ r i) x = 0 := by
      rw [basis_mul, map_mul, Module.End.mul_apply, hch x hx, map_zero]
    rw [map_mul, Module.End.mul_apply, ← hφ, map_sub, aeval_X, aeval_C, LinearMap.sub_apply, sub_eq_zero] at h1
    rw [h1]
    rfl
  have hQ : (∏ j ∈ univ.erase i, (X - C (r j))).natDegree < N + 1 := by
    simp
  have h2 := hPV W (N + 1) (fun s => A s φ - (∏ j ∈ univ.erase i, (X - C (r j))).coeff s • φ) {r i} ?_
  · have h3 : ∑ s ∈ range (N + 1), u ^ s • (A s φ - (∏ j ∈ univ.erase i, (X - C (r j))).coeff s • φ) = 0 :=
      Finset.sum_eq_zero (fun s hs => by rw [h2 s hs, smul_zero])
    simp only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero] at h3
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [h3, ← hev, Polynomial.eval_eq_sum_range' hQ, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [smul_smul, mul_comm]
  intro u hu
  have hne : u - r i ≠ 0 := sub_ne_zero.2 (by simpa using hu)
  have h4 := h φ hφG u
  rw [hKφ, ← sub_smul, map_smul, ← Finset.mul_prod_erase univ _ (Finset.mem_univ i), mul_smul] at h4
  have h5 := smul_right_injective W hne h4
  simp only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero]
  rw [LinearMap.sum_apply] at h5
  simp only [LinearMap.smul_apply] at h5
  rw [h5, ← hev, Polynomial.eval_eq_sum_range' hQ, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [smul_smul, mul_comm]

end abs

section mod

variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)

def Gd (v : V) : Submodule ℂ (Fin (N + 1) → V) where
  carrier := {x | ∃ y : Fin (N + 1) → Module.End ℂ V, IsVec E y ∧ ∀ l, x l = y l v}
  add_mem' := by
    rintro x x' ⟨y, hy, hx⟩ ⟨y', hy', hx'⟩
    exact ⟨_, vec_add E hy hy', fun l => by rw [Pi.add_apply, hx, hx']; rfl⟩
  zero_mem' := ⟨fun _ => 0, fun a b c => by simp, fun l => rfl⟩
  smul_mem' := by
    rintro k x ⟨y, hy, hx⟩
    exact ⟨_, vec_smul E k hy, fun l => by rw [Pi.smul_apply, hx]; rfl⟩

def EE : Module.End ℂ (Fin (N + 1) → V) := LinearMap.pi fun l => ∑ c, (E c l) ∘ₗ LinearMap.proj c

theorem EE_apply (x : Fin (N + 1) → V) (l : Fin (N + 1)) : EE E x l = ∑ c, E c l (x c) := by
  simp [EE, LinearMap.sum_apply]

def MM (T : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V) : Module.End ℂ (Fin (N + 1) → V) :=
  LinearMap.pi fun j => ∑ l, (T j l) ∘ₗ LinearMap.proj l

theorem MM_apply (T : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V) (x : Fin (N + 1) → V) (j : Fin (N + 1)) :
    MM T x j = ∑ l, T j l (x l) := by
  simp [MM, LinearMap.sum_apply]

theorem EE_mem (hE : GlRel E) (v : V) : ∀ x ∈ Gd E v, EE E x ∈ Gd E v := by
  rintro x ⟨y, hy, hx⟩
  refine ⟨_, vecD E hE y hy, fun l => ?_⟩
  rw [EE_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun c _ => by rw [hx]; rfl)

theorem main (hQ : QminorPoly) (hPV : PolyVanish) (y : Fin (N + 1) → Module.End ℂ V) (hE : GlRel E) (hy : IsVec E y)
    (m : Fin (N + 1) → ℂ) (hm : Function.Injective m) (v : V) (hv : v ∈ CapSp E m) :
    ∃ Φ : Fin (N + 1) → Fin (N + 1) → V,
      (∀ x, ∑ i, Φ i x = y x v) ∧
      (∀ i x, Φ i x ∈ CapSp E (Function.update m i (m i - 1))) ∧
      ∀ (i x : Fin (N + 1)) (u : ℂ),
        ∑ l : Fin (N + 1), ((-1 : ℂ) ^ ((x : ℕ) + (l : ℕ))) • qminor (t := N) E (skip1 x) (skip1 l) (u - 1) (Φ i l) =
          (∏ j ∈ Finset.univ.erase i, (u + m j)) • Φ i x := by
  choose cf hcf using fun j l : Fin (N + 1) => hQ (Module.End ℂ V) (N + 1) N E j.succAbove l.succAbove
  have hMM : ∀ u : ℂ, ∑ s ∈ range (N + 1), u ^ s • MM (fun j l => ((-1 : ℂ) ^ ((j : ℕ) + (l : ℕ))) • cf j l s) =
      MM (Tch E u) := by
    intro u
    refine LinearMap.ext (fun x => ?_)
    funext j
    rw [MM_apply, LinearMap.sum_apply, Finset.sum_apply]
    simp only [LinearMap.smul_apply, Pi.smul_apply, MM_apply, Tch, hcf, Finset.smul_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun s _ => ?_))
    rw [smul_comm]
  have hv' := mem_CapSp.1 hv
  have hK : ∀ x ∈ Gd E v, (-((2 : ℂ) • (1 : Module.End ℂ (Fin (N + 1) → V)) + EE E)) x ∈ Gd E v := by
    intro x hx
    rw [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.smul_apply]
    exact Submodule.neg_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (EE_mem E hE v x hx))
  have hstar : ∀ x ∈ Gd E v, ∀ u : ℂ,
      (∑ s ∈ range (N + 1), u ^ s • MM (fun j l => ((-1 : ℂ) ^ ((j : ℕ) + (l : ℕ))) • cf j l s))
        (u • x - (-((2 : ℂ) • (1 : Module.End ℂ (Fin (N + 1) → V)) + EE E)) x) = (∏ j, (u - (-1 - m j))) • x := by
    rintro x ⟨z, hz, hx⟩ u
    rw [hMM]
    funext j
    have h1 := congrArg (fun T : Module.End ℂ V => T v) (star E hE z hz (u + 1) j)
    simp only [add_sub_cancel_right, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, hv' (u + 1), map_smul] at h1
    rw [MM_apply, Pi.smul_apply, hx j]
    have h2 : cpol m (u + 1) = ∏ j, (u - (-1 - m j)) := by
      unfold cpol
      exact Finset.prod_congr rfl (fun j _ => by ring)
    rw [← h2, ← h1]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    congr 1
    simp only [Pi.sub_apply, Pi.smul_apply, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, Pi.neg_apply, Pi.add_apply, EE_apply, hx]
    rw [sub_neg_eq_add, ← add_assoc, ← add_smul]
    congr 2
    ring
  have hr : Function.Injective (fun j => -1 - m j) := by
    intro a b hab
    exact hm (by simpa using hab)
  obtain ⟨Φ, hΦG, hΦs, hΦ⟩ := decomp hPV (Gd E v) _ hK _ N (fun j => -1 - m j) hr hstar (fun l => y l v) ⟨y, hy, fun _ => rfl⟩
  have h3 : ∀ (i x : Fin (N + 1)) (u : ℂ), ∑ l, Tch E (u - 1) x l (Φ i l) = (∏ j ∈ Finset.univ.erase i, (u + m j)) • Φ i x := by
    intro i x u
    have := congrFun (hΦ i (u - 1)) x
    rw [hMM, MM_apply, Pi.smul_apply] at this
    rw [this]
    congr 1
    exact Finset.prod_congr rfl (fun j _ => by ring)
  refine ⟨Φ, fun x => ?_, fun i x => ?_, fun i x u => ?_⟩
  · have := congrFun hΦs x
    rwa [Finset.sum_apply] at this
  · obtain ⟨z, hz, hx⟩ := hΦG i
    rw [mem_CapSp]
    intro w
    have h4 := congrArg (fun T : Module.End ℂ V => T v) (detVecR E hE z hz w x)
    simp only [LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, hv' w, map_smul, ← hx] at h4
    rw [h4, h3, ← sub_smul]
    congr 1
    unfold cpol
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i), ← Finset.mul_prod_erase univ (fun j => w + Function.update m i (m i - 1) j) (Finset.mem_univ i),
      Function.update_self]
    have h5 : ∏ j ∈ univ.erase i, (w + Function.update m i (m i - 1) j) = ∏ j ∈ univ.erase i, (w + m j) :=
      Finset.prod_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    rw [h5]
    ring
  · rw [← h3]
    simp only [QuantumMinorCommutation.skip_one_eq_succAbove]
    rfl

end mod

end Formalism.FourierDecayAlt.P.DeterminantVectorSums

open Formalism.FourierDecayAlt.Qr in
theorem Formalism.FourierDecayAlt.P.qr_vecDown_of : QminorPoly → PolyVanish → VecDown := by
  intro hQ hPV V _ _ n E y hE hy _ m hm v hv
  cases n with
  | zero => exact ⟨fun i => i.elim0, fun x => x.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ N => exact Formalism.FourierDecayAlt.P.DeterminantVectorSums.main E hQ hPV y hE hy m hm v hv
