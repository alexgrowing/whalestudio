import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFB
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Main
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BoundedSums

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLSmall

open PartialDerivEval RowTiePE0 RowTiePProj

section Bd

variable {C : Type} [Field C] {V : VF C}

def Bdd (V : VF C) (s : ℕ → C) : Prop := ∃ K : ℝ, ∀ n, V.Ge K (s n)

theorem bdd_const (x : C) : Bdd V (fun _ => x) := by
  obtain ⟨K, hK⟩ := exists_ge (V := V) x
  exact ⟨K, fun _ => hK⟩

theorem Bdd.add {s t : ℕ → C} (hs : Bdd V s) (ht : Bdd V t) : Bdd V (fun n => s n + t n) := by
  obtain ⟨K, hK⟩ := hs
  obtain ⟨L, hL⟩ := ht
  exact ⟨min K L, fun n => ((hK n).mono (min_le_left _ _)).add ((hL n).mono (min_le_right _ _))⟩

theorem Bdd.mul {s t : ℕ → C} (hs : Bdd V s) (ht : Bdd V t) : Bdd V (fun n => s n * t n) := by
  obtain ⟨K, hK⟩ := hs
  obtain ⟨L, hL⟩ := ht
  exact ⟨K + L, fun n => (hK n).mul (hL n)⟩

theorem Bdd.sum {ι : Type} (S : Finset ι) {s : ι → ℕ → C} (h : ∀ i ∈ S, Bdd V (s i)) :
    Bdd V (fun n => ∑ i ∈ S, s i n) := by
  first | exact GlobalTheory.ScalarStatement.main .. | (apply GlobalTheory.ScalarStatement.main <;> assumption) | (intros; apply GlobalTheory.ScalarStatement.main <;> assumption) | (apply @GlobalTheory.ScalarStatement.main <;> assumption) | (intros; apply @GlobalTheory.ScalarStatement.main <;> assumption) | (apply @GlobalTheory.ScalarStatement.main <;> first | assumption | infer_instance) | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι S s h | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι S s | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι S | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι | exact @GlobalTheory.ScalarStatement.main C ‹_› V | exact @GlobalTheory.ScalarStatement.main C ‹_› | exact @GlobalTheory.ScalarStatement.main C

theorem tends_mul_bdd {s t : ℕ → C} (hs : Bdd V s) (ht : Tends V t 0) : Tends V (fun n => s n * t n) 0 := by
  intro w
  obtain ⟨K, hK⟩ := hs
  obtain ⟨n0, h0⟩ := ht (w - K)
  refine ⟨n0, fun n hn => ?_⟩
  have h := (hK n).mul (h0 n hn)
  have e : (0 : C) - s n * t n = s n * (0 - t n) := by ring
  rw [e]
  exact h.mono (by linarith)

variable {σ : Type}

def BddS (V : VF C) (f : ℕ → MvPowerSeries σ C) : Prop := ∀ μ, Bdd V (fun n => coeff μ (f n))

theorem BddS.const (g : MvPowerSeries σ C) : BddS V (fun _ => g) := fun _ => bdd_const _

theorem BddS.of_int {f : ℕ → MvPowerSeries σ C} (h : ∀ n, IntS V (f n)) : BddS V f :=
  fun μ => ⟨0, fun n => h n μ⟩

theorem BddS.mul {f g : ℕ → MvPowerSeries σ C} (hf : BddS V f) (hg : BddS V g) :
    BddS V (fun n => f n * g n) := fun μ => by
  classical
  simp only [coeff_mul]
  exact Bdd.sum _ fun p _ => (hf p.1).mul (hg p.2)

theorem BddS.pow {f : ℕ → MvPowerSeries σ C} (hf : BddS V f) (k : ℕ) : BddS V (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using BddS.const (V := V) (1 : MvPowerSeries σ C)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem BddS.prod {ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C} (h : ∀ i ∈ S, BddS V (f i)) :
    BddS V (fun n => ∏ i ∈ S, f i n) := by
  first | exact UpperTheory.Reformulated.B.BoundedSums.prod .. | (apply UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (intros; apply UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (apply @UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (apply @UpperTheory.Reformulated.B.BoundedSums.prod <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι S f h | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι S f | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι S | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› | exact @UpperTheory.Reformulated.B.BoundedSums.prod C

theorem BddS.fprod {ι : Type} (d : ι →₀ ℕ) {a : ℕ → ι → MvPowerSeries σ C} (ha : ∀ i, BddS V (fun n => a n i)) :
    BddS V (fun n => d.prod fun i e => a n i ^ e) := by
  unfold Finsupp.prod
  exact BddS.prod _ fun i _ => (ha i).pow _

theorem BddS.subst [Finite σ] {τ : Type} {a : ℕ → σ → MvPowerSeries τ C} {f : ℕ → MvPowerSeries σ C}
    (ha0 : ∀ n s, constantCoeff (a n s) = 0) (ha : ∀ s, BddS V (fun n => a n s)) (hf : BddS V f) :
    BddS V (fun n => MvPowerSeries.subst (a n) (f n)) := fun μ => by
  have e : (fun n => coeff μ (MvPowerSeries.subst (a n) (f n))) = fun n =>
      ∑ d ∈ (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset,
        coeff d (f n) * coeff μ (d.prod fun s e => a n s ^ e) :=
    funext fun n => coeff_subst_eq_sum (ha0 n) _ _
  rw [e]
  exact Bdd.sum _ fun d _ => (hf d).mul (BddS.fprod d ha μ)

theorem TendsS.mul_bdd {f g : ℕ → MvPowerSeries σ C} (hf : BddS V f) (hg : TendsS V g 0) :
    TendsS V (fun n => f n * g n) 0 := fun μ => by
  classical
  show Tends V (fun n => coeff μ (f n * g n)) (coeff μ 0)
  simp only [coeff_mul, map_zero]
  have h := Tends.sum (V := V) (Finset.HasAntidiagonal.antidiagonal μ)
    (s := fun p n => coeff p.1 (f n) * coeff p.2 (g n)) (x := fun _ => 0)
    fun p _ => tends_mul_bdd (hf p.1) (by simpa using hg p.2)
  simpa using h

def Close (V : VF C) (f g : ℕ → MvPowerSeries σ C) : Prop := TendsS V (fun n => f n - g n) 0

theorem Close.refl (f : ℕ → MvPowerSeries σ C) : Close V f f := by
  unfold Close
  simpa using TendsS.const (V := V) (0 : MvPowerSeries σ C)

theorem Close.mul {a a' b b' : ℕ → MvPowerSeries σ C} (ha : BddS V a) (hb' : BddS V b') (h1 : Close V a b)
    (h2 : Close V a' b') : Close V (fun n => a n * a' n) (fun n => b n * b' n) := by
  have e : (fun n => a n * a' n - b n * b' n) = fun n => a n * (a' n - b' n) + b' n * (a n - b n) :=
    funext fun n => by ring
  unfold Close
  rw [e]
  simpa using (TendsS.mul_bdd ha h2).add (TendsS.mul_bdd hb' h1)

theorem Close.pow {a b : ℕ → MvPowerSeries σ C} (ha : BddS V a) (hb : BddS V b) (h : Close V a b) (k : ℕ) :
    Close V (fun n => a n ^ k) (fun n => b n ^ k) := by
  induction k with
  | zero => simpa using Close.refl (V := V) (fun _ => (1 : MvPowerSeries σ C))
  | succ k ih => simpa only [pow_succ] using Close.mul (ha.pow k) hb ih h

theorem Close.prod {ι : Type} (S : Finset ι) {a b : ι → ℕ → MvPowerSeries σ C} (ha : ∀ i ∈ S, BddS V (a i))
    (hb : ∀ i ∈ S, BddS V (b i)) (h : ∀ i ∈ S, Close V (a i) (b i)) :
    Close V (fun n => ∏ i ∈ S, a i n) (fun n => ∏ i ∈ S, b i n) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Close.refl (V := V) (fun _ => (1 : MvPowerSeries σ C))
  | insert x S hx ih =>
    simp only [Finset.prod_insert hx]
    exact Close.mul (ha x (Finset.mem_insert_self x S)) (BddS.prod S fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (h x (Finset.mem_insert_self x S))
      (ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
        fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Close.fprod {ι : Type} (d : ι →₀ ℕ) {a b : ℕ → ι → MvPowerSeries σ C} (ha : ∀ i, BddS V (fun n => a n i))
    (hb : ∀ i, BddS V (fun n => b n i)) (h : ∀ i, Close V (fun n => a n i) (fun n => b n i)) :
    Close V (fun n => d.prod fun i e => a n i ^ e) (fun n => d.prod fun i e => b n i ^ e) := by
  unfold Finsupp.prod
  exact Close.prod _ (fun i _ => (ha i).pow _) (fun i _ => (hb i).pow _) fun i _ => Close.pow (ha i) (hb i) (h i) _

theorem Close.subst [Finite σ] {τ : Type} {a b : ℕ → σ → MvPowerSeries τ C}
    (ha0 : ∀ n s, constantCoeff (a n s) = 0) (hb0 : ∀ n s, constantCoeff (b n s) = 0)
    (ha : ∀ s, BddS V (fun n => a n s)) (hb : ∀ s, BddS V (fun n => b n s))
    (h : ∀ s, Close V (fun n => a n s) (fun n => b n s)) (f : MvPowerSeries σ C) :
    Close V (fun n => MvPowerSeries.subst (a n) f) (fun n => MvPowerSeries.subst (b n) f) := fun μ => by
  show Tends V (fun n => coeff μ (MvPowerSeries.subst (a n) f - MvPowerSeries.subst (b n) f)) (coeff μ 0)
  have e : (fun n => coeff μ (MvPowerSeries.subst (a n) f - MvPowerSeries.subst (b n) f)) = fun n =>
      ∑ d ∈ (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset,
        coeff d f * coeff μ ((d.prod fun s e => a n s ^ e) - (d.prod fun s e => b n s ^ e)) := funext fun n => by
    rw [map_sub, coeff_subst_eq_sum (ha0 n), coeff_subst_eq_sum (hb0 n), ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by rw [map_sub, mul_sub]
  rw [e, map_zero]
  have h2 := Tends.sum (V := V) (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset
    (s := fun d n => coeff d f * coeff μ ((d.prod fun s e => a n s ^ e) - (d.prod fun s e => b n s ^ e)))
    (x := fun _ => 0) fun d _ => by
      have h3 := (tends_const (V := V) (coeff d f)).mul (Close.fprod d ha hb h μ)
      simpa using h3
  simpa using h2

end Bd

end RowTiePLSmall

end Formalism.L2.FormalSeriesBounds
