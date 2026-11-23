import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Lemma4ElementZero
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FockRLinDual

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Lin)

section ND

variable {R : Type} [CommRing R] {n' k : ℕ}

theorem normDeg_univ (r : ℕ) (m : TV n' k →₀ ℕ) :
    normDeg r m = ∑ v : TV n' k, if IsNormal r v then m v else 0 := by
  unfold normDeg
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  rw [Finsupp.notMem_support_iff] at hv
  simp [hv]

theorem normDeg_add (r : ℕ) (m m' : TV n' k →₀ ℕ) : normDeg r (m + m') = normDeg r m + normDeg r m' := by
  simp only [normDeg_univ, Finsupp.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

def NDsub (R : Type) [CommRing R] (n' k r T : ℕ) : Submodule R (MvPolynomial (TV n' k) R) :=
  restrictSupport R {mm | normDeg r mm ≤ T}

theorem mem_NDsub {r T : ℕ} {P : MvPolynomial (TV n' k) R} :
    P ∈ NDsub R n' k r T ↔ ∀ mm ∈ P.support, normDeg r mm ≤ T := by
  show P ∈ restrictSupport R {mm | normDeg r mm ≤ T} ↔ _
  exact ⟨fun h mm hm => h hm, fun h mm hm => h mm hm⟩

theorem NDsub_mono {r T T' : ℕ} (h : T ≤ T') : NDsub R n' k r T ≤ NDsub R n' k r T' := by
  intro P hP
  rw [mem_NDsub] at hP ⊢
  intro mm hm
  exact (hP mm hm).trans h

theorem nd_move (r : ℕ) (mm : TV n' k →₀ ℕ) (v v' : TV n' k) :
    normDeg r (Finsupp.single v 1 + (mm - Finsupp.single v' 1)) ≤ normDeg r mm + 1 := by
  rw [normDeg_add]
  have h1 : normDeg r (Finsupp.single v 1 : TV n' k →₀ ℕ) ≤ 1 := by
    rw [normDeg_univ]
    calc ∑ w : TV n' k, (if IsNormal r w then (Finsupp.single v 1 : TV n' k →₀ ℕ) w else 0)
        ≤ ∑ w : TV n' k, (Finsupp.single v 1 : TV n' k →₀ ℕ) w :=
          Finset.sum_le_sum fun w _ => by split_ifs <;> simp
      _ = 1 := by simp [Finsupp.single_apply]
  have h2 : normDeg r (mm - Finsupp.single v' 1) ≤ normDeg r mm := by
    rw [normDeg_univ, normDeg_univ]
    apply Finset.sum_le_sum
    intro w _
    split_ifs
    · simp only [Finsupp.tsub_apply]
      exact tsub_le_self
    · exact le_rfl
  omega

theorem nd_op (r T : ℕ) (v v' : TV n' k) {P : MvPolynomial (TV n' k) R} (hP : P ∈ NDsub R n' k r T) :
    X v * pderiv v' P ∈ NDsub R n' k r (T + 1) := by
  rw [mem_NDsub] at hP
  rw [P.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun mm hmm => ?_
  rw [pderiv_monomial, ← pow_one (X v), ← monomial_single_add, mem_NDsub]
  intro mm' hmm'
  rw [Finset.mem_singleton.mp (support_monomial_subset hmm')]
  exact (nd_move r mm v v').trans (Nat.add_le_add_right (hP mm hmm) 1)

theorem nd_mul {r T T' : ℕ} {P Q : MvPolynomial (TV n' k) R} (hP : P ∈ NDsub R n' k r T) (hQ : Q ∈ NDsub R n' k r T') :
    P * Q ∈ NDsub R n' k r (T + T') := by
  rw [mem_NDsub] at *
  intro mm hmm
  have h1 := support_mul P Q hmm
  rw [Finset.mem_add] at h1
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  rw [normDeg_add]
  exact Nat.add_le_add (hP a ha) (hQ b hb)

theorem Lin_pderiv (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (s : Fin n') (b : Fin k)
    (f : MvPolynomial (Fin n' × Fin k) R) :
    Lin N (pderiv (s, b) f) = ∑ c, N' s c b • pderiv (s, c) (Lin N f) := by
  simp only [Lin_chain, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have hm : ∀ a, ∑ c, N' s c b * N s a c = (1 : Matrix (Fin k) (Fin k) R) a b := by
    intro a
    rw [← h s, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp [hm, Matrix.one_apply]

theorem nd_Lin_op (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (r T : ℕ) (s : Fin n')
    (a b : Fin k) {f : MvPolynomial (Fin n' × Fin k) R} (hf : Lin N f ∈ NDsub R n' k r T) :
    Lin N (X (s, a) * pderiv (s, b) f) ∈ NDsub R n' k r (T + 1) := by
  rw [map_mul, Lin_X, Lin_pderiv N N' h, Finset.sum_mul]
  refine Submodule.sum_mem _ fun b' _ => ?_
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [mul_smul_comm, mul_assoc, ← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (nd_op r T _ _ hf))

theorem nd_word (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (r T : ℕ)
    {f : MvPolynomial (Fin n' × Fin k) R} (hf : Lin N f ∈ NDsub R n' k r T) :
    ∀ l : List (Fin n' × (Fin k × Fin k)), Lin N (opWord l f) ∈ NDsub R n' k r (T + l.length) := by
  intro l
  induction l with
  | nil => exact hf
  | cons y l ih =>
    show Lin N (X (y.1, y.2.1) * pderiv (y.1, y.2.2) (opWord l f)) ∈ NDsub R n' k r (T + (l.length + 1))
    rw [← Nat.add_assoc]
    exact nd_Lin_op N N' h r (T + l.length) y.1 y.2.1 y.2.2 ih

theorem word_length {τ : Type} (TT : Finset (Fin n')) (c : ℕ) :
    ∀ l : List (Fin n' × τ), (∀ z ∈ l, z.1 ∈ TT) → (∀ s, (l.filter fun z => z.1 = s).length ≤ c) →
      l.length ≤ TT.card * c := by
  intro l hl hc
  have key : ∀ l : List (Fin n' × τ), (∀ z ∈ l, z.1 ∈ TT) →
      l.length = ∑ s ∈ TT, (l.filter fun z => z.1 = s).length := by
    intro l hl
    induction l with
    | nil => simp
    | cons z l ih =>
      have e : ∀ s, ((z :: l).filter fun w => w.1 = s).length =
          (l.filter fun w => w.1 = s).length + if z.1 = s then 1 else 0 := by
        intro s
        by_cases hs : z.1 = s <;> simp [List.filter_cons, hs]
      rw [List.length_cons, ih (fun w hw => hl w (List.mem_cons_of_mem _ hw)),
        Finset.sum_congr rfl (fun s _ => e s), Finset.sum_add_distrib, Finset.sum_ite_eq]
      simp [hl z (by simp)]
  rw [key l hl]
  calc ∑ s ∈ TT, (l.filter fun z => z.1 = s).length ≤ ∑ s ∈ TT, c := Finset.sum_le_sum fun s _ => hc s
    _ = TT.card * c := by rw [Finset.sum_const, smul_eq_mul]

theorem nd_OpCl (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (r T : ℕ) (TT : Finset (Fin n'))
    (c : ℕ) (M : Submodule R (MvPolynomial (Fin n' × Fin k) R)) (hM : ∀ f ∈ M, Lin N f ∈ NDsub R n' k r T) :
    ∀ f ∈ OpCl TT c M, Lin N f ∈ NDsub R n' k r (T + TT.card * c) := by
  intro f hf
  unfold OpCl at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f0, hf0, l, h1, h2, rfl⟩ := hy
    exact NDsub_mono (Nat.add_le_add_left (word_length TT c l h1 h2) T) (nd_word N N' h r T (hM f0 hf0) l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end ND

end Formalism.MainNotions.TestSideCounting
