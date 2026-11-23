import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixExistsFixedFrobeniusSolution
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteBreuilKisinQuotientPrimePowXPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.Cpt

theorem of_add {R : Type} (Q : ℕ → R → Prop) (hmono : ∀ n x, Q (n + 1) x → Q n x) :
    ∀ n k x, Q (n + k) x → Q n x := by
  intro n k x
  induction k with
  | zero => exact id
  | succ k ih => exact fun h => ih (hmono _ _ (by rwa [← add_assoc] at h))

def Good {R : Type} [CommRing R] {ι : Type} (I : ℕ → Ideal R) (Q : ℕ → (ι → R) → Prop) (n : ℕ) (y : ι → R) :
    Prop :=
  ∀ k, n ≤ k → ∃ x, Q k x ∧ ∀ i, x i - y i ∈ I n

theorem exists_seq {R : Type} [CommRing R] (I : ℕ → Ideal R) (hI : ∀ n, I (n + 1) ≤ I n) (hI0 : I 0 = ⊤)
    (hfin : ∀ n, Finite (R ⧸ I n)) (ι : Type) [Finite ι] (Q : ℕ → (ι → R) → Prop)
    (hmono : ∀ n x, Q (n + 1) x → Q n x) (hcong : ∀ n x y, Q n x → (∀ i, x i - y i ∈ I n) → Q n y)
    (hex : ∀ n, ∃ x, Q n x) :
    ∃ y : ℕ → ι → R, (∀ n, Q n (y n)) ∧ ∀ n i, y (n + 1) i - y n i ∈ I n := by
  classical
  have step : ∀ n y, Good I Q n y → ∃ y', Good I Q (n + 1) y' ∧ ∀ i, y' i - y i ∈ I n := by
    intro n y hy
    by_contra hne
    haveI : Finite (ι → R ⧸ I (n + 1)) := by haveI := hfin (n + 1); infer_instance
    let rep : (ι → R ⧸ I (n + 1)) → ι → R := fun t i => Classical.choose (Ideal.Quotient.mk_surjective (t i))
    have hrep : ∀ t i, Ideal.Quotient.mk (I (n + 1)) (rep t i) = t i :=
      fun t i => Classical.choose_spec (Ideal.Quotient.mk_surjective (t i))
    let P : (ι → R ⧸ I (n + 1)) → Prop := fun t =>
      ∃ k, n + 1 ≤ k ∧ ¬ ∃ x, Q k x ∧ ∀ i, x i - rep t i ∈ I (n + 1)
    let kf : (ι → R ⧸ I (n + 1)) → ℕ := fun t => if h : P t then h.choose else 0
    have hkf : ∀ t (h : P t), kf t = h.choose := fun t h => dif_pos h
    obtain ⟨t0, ht0⟩ := Finite.exists_max kf
    obtain ⟨x, hx, hxy⟩ := hy (n + kf t0) (Nat.le_add_right _ _)
    let t : ι → R ⧸ I (n + 1) := fun i => Ideal.Quotient.mk _ (x i)
    have hxt : ∀ i, x i - rep t i ∈ I (n + 1) := fun i =>
      Ideal.Quotient.eq.1 (hrep t i).symm
    have hty : ∀ i, rep t i - y i ∈ I n := fun i => by
      have : rep t i - y i = (x i - y i) - (x i - rep t i) := by ring
      rw [this]
      exact sub_mem (hxy i) (hI n (hxt i))
    have hng : ¬ Good I Q (n + 1) (rep t) := fun hg => hne ⟨rep t, hg, hty⟩
    have hP : P t := by
      by_contra hc
      refine hng fun k hk => ?_
      by_contra hk'
      exact hc ⟨k, hk, hk'⟩
    have hs := hP.choose_spec
    rw [← hkf t hP] at hs
    refine hs.2 ⟨x, ?_, hxt⟩
    have hle : kf t ≤ n + kf t0 := (ht0 t).trans (Nat.le_add_left _ _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    exact of_add Q hmono (kf t) d x (hd ▸ hx)
  choose! f hf1 hf2 using step
  let seq : ℕ → ι → R := fun n => Nat.rec (motive := fun _ => ι → R) 0 (fun n y => f n y) n
  have hgood : ∀ n, Good I Q n (seq n) := by
    intro n
    induction n with
    | zero =>
      intro k _
      obtain ⟨x, hx⟩ := hex k
      exact ⟨x, hx, fun i => by rw [hI0]; exact Submodule.mem_top⟩
    | succ n ih => exact hf1 n (seq n) ih
  refine ⟨seq, fun n => ?_, fun n i => hf2 n (seq n) (hgood n) i⟩
  obtain ⟨x, hx, hxs⟩ := hgood n n le_rfl
  exact hcong n x (seq n) hx hxs

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem X_pow_mem (bk : BK K) (n m : ℕ) :
    (X : bk.S) ^ (bk.Ep.natDegree * (n + m)) ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m} := by
  have h1 : (X : bk.S) ^ (bk.Ep.natDegree * (n + m)) ∈
      (Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E}) ^ (n + m) := by
    rw [pow_mul]; exact Ideal.pow_mem_pow (BK.X_pow_natDegree_mem bk) _
  have h2 := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {bk.E})
    (n := n) (m := m)
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h2
  exact h2 h1

theorem finite_quot (bk : BK K) (n m : ℕ) :
    Finite (bk.S ⧸ (Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m})) := by
  haveI := GlobalTheory.T.finite_breuilKisin_quotient_prime_pow_X_pow l K bk n (bk.Ep.natDegree * (n + m))
  have H : Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ (bk.Ep.natDegree * (n + m))} ≤
      Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m} :=
    sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 (X_pow_mem bk n m))
  refine Finite.of_surjective (Ideal.Quotient.factor H) fun y => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

theorem exists_lim (bk : BK K) (m : ℕ) (s : ℕ → bk.S)
    (hs : ∀ n, s (n + 1) - s n ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m}) :
    ∃ L : bk.S, ∀ n, s (n + m) - L ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m} := by
  have hd : ∀ n, ∃ a b : bk.S, s (n + 1) - s n = (l : bk.S) ^ n * a + bk.E ^ m * b := by
    intro n
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hs n)
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨a, b, by rw [← hyz]; ring⟩
  choose a b hab using hd
  let z : ℕ → bk.S := fun n => s n - bk.E ^ m * ∑ k ∈ Finset.range n, b k
  have hz1 : ∀ n, z (n + 1) - z n = (l : bk.S) ^ n * a n := by
    intro n
    simp only [z, Finset.sum_range_succ]
    linear_combination hab n
  have hcau : ∀ n N, n ≤ N → z N - z n ∈ Ideal.span {(l : bk.S) ^ n} := by
    intro n N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
      have : z (N + 1) - z n = (z (N + 1) - z N) + (z N - z n) := by ring
      rw [this, hz1]
      exact add_mem (Ideal.mem_span_singleton.2 (dvd_mul_of_dvd_left (pow_dvd_pow _ hN) _)) ih
  have hJ : ∀ n, Ideal.span {(l : bk.S) ^ n} ≤ bk.J ^ n := fun n => by
    rw [← Ideal.span_singleton_pow]; exact Ideal.pow_right_mono le_sup_left n
  obtain ⟨L, hL⟩ := bk.complete.toIsPrecomplete.prec (f := z) (fun {p q} hpq => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact neg_mem (hJ p (hcau p q hpq)))
  refine ⟨L, fun n => ?_⟩
  have h1 := hL (n + m)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {bk.E})
    (n := n) (m := m)
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h2
  have : s (n + m) - L = (z (n + m) - L) + bk.E ^ m * ∑ k ∈ Finset.range (n + m), b k := by
    simp only [z]; ring
  rw [this]
  exact add_mem (h2 h1) (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem compact : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) [Finite ι] (m : ℕ)
    (Q : ℕ → (ι → bk.S) → Prop), (∀ n x, Q (n + 1) x → Q n x) →
    (∀ n x y, Q n x → (∀ i, x i - y i ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m}) → Q n y) →
    (∀ n, ∃ x, Q n x) → ∃ x, ∀ n, Q n x := by
  intro l _ K bk ι _ m Q hmono hcong hex
  obtain ⟨y, hQ, hy⟩ := exists_seq (fun n => Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m})
    (fun n => sup_le_sup_right (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ n))) _)
    (by simp) (fun n => finite_quot bk n m) ι Q hmono hcong hex
  choose L hL using fun i => exists_lim bk m (fun n => y n i) (fun n => hy n i)
  exact ⟨L, fun n => hcong n _ _ (of_add Q hmono n m _ (hQ (n + m))) (fun i => hL i n)⟩

end GlobalTheory.BKLim.Cpt
