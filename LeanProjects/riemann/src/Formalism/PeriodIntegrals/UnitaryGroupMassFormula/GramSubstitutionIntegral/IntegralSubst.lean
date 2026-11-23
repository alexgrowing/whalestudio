import Mathlib
import Formalism.PeriodIntegrals.FglGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsSubstitution

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhGram

open PI.FglGram

variable {p : ℕ} [Fact p.Prime]

def Good {σ : Type*} (a : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff a = 0 ∧ IntegralMv a

structure Hyps (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])) : Prop where
  data : Data l ex ph
  swap : ∀ α ∈ S, α.swap ∈ S
  intMul : ∀ α ∈ S, IntegralMv (mulBy l ex α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])
  intAdd : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
  norm : ∀ α ∈ S, Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))
  conj : ∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1)))
  biadd : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2))

section Calc

open PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients

private theorem simeq_iff_lemma {σ : Type*} (f g : MvPowerSeries σ ℂ_[p]) :
    Simeq f g ↔ PI.PhNormUnits.Simeq f g := Iff.rfl

theorem sRefl {σ : Type*} (f : MvPowerSeries σ ℂ_[p]) : Simeq f f := by
  exact (simeq_iff_lemma f f).2 (simeq_refl f)

theorem sOfEq {σ : Type*} {f g : MvPowerSeries σ ℂ_[p]} (h : f = g) : Simeq f g := by
  subst h
  exact sRefl f

theorem sSymm {σ : Type*} {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq g f := by
  exact (simeq_iff_lemma _ _).2 (simeq_symm ((simeq_iff_lemma _ _).1 h))

theorem sTrans {σ : Type*} {f g k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq g k) : Simeq f k := by
  exact (simeq_iff_lemma _ _).2 (simeq_trans ((simeq_iff_lemma _ _).1 h1) ((simeq_iff_lemma _ _).1 h2))

theorem sAdd {σ : Type*} {f g h k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq h k) :
    Simeq (f + h) (g + k) := by
  exact (simeq_iff_lemma _ _).2 (simeq_add ((simeq_iff_lemma _ _).1 h1) ((simeq_iff_lemma _ _).1 h2))

theorem sSum {σ ι : Type*} (s : Finset ι) {f g : ι → MvPowerSeries σ ℂ_[p]} (h : ∀ i ∈ s, Simeq (f i) (g i)) :
    Simeq (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact sRefl 0
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact sAdd (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem integral_subst' {σ τ : Type*} [Finite τ] (s : τ → MvPowerSeries σ ℂ_[p]) (hs : ∀ i, Good (s i))
    {f : MvPowerSeries τ ℂ_[p]} (hf : IntegralMv f) : IntegralMv (MvPowerSeries.subst s f) := by
  exact integral_subst s (fun i => (hs i).1) (fun i => (hs i).2) hf

theorem sSubst {σ τ : Type*} [Finite τ] (s : τ → MvPowerSeries σ ℂ_[p]) (hs : ∀ i, Good (s i))
    {f g : MvPowerSeries τ ℂ_[p]} (h : Simeq f g) :
    Simeq (MvPowerSeries.subst s f) (MvPowerSeries.subst s g) := by
  exact (simeq_iff_lemma _ _).2
    (simeq_subst s (fun i => (hs i).1) (fun i => (hs i).2) ((simeq_iff_lemma _ _).1 h))

end Calc

def GoodAdd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]), Good a → Good b → Good (add l ex a b)

def GoodMul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ : Type) (α : ℂ_[p] × ℂ_[p]), α ∈ S → ∀ a : MvPowerSeries σ ℂ_[p], Good a → Good (mulBy l ex α.1 a)

def BiaddSub : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ : Type) (a b c : MvPowerSeries σ ℂ_[p]), Good a → Good b → Good c →
      Simeq (be l ex ph (add l ex a b) c) (be l ex ph a c + be l ex ph b c)

def NormSub : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ : Type) (α : ℂ_[p] × ℂ_[p]), α ∈ S → ∀ a : MvPowerSeries σ ℂ_[p], Good a →
      Simeq (phAt ph (mulBy l ex α.1 a)) (MvPowerSeries.C (α.1 * α.2) * phAt ph a)

def MoveSub : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ : Type) (α α' : ℂ_[p] × ℂ_[p]), α ∈ S → α' ∈ S → ∀ a b : MvPowerSeries σ ℂ_[p], Good a → Good b →
      Simeq (be l ex ph (mulBy l ex α.1 a) (mulBy l ex α'.1 b)) (be l ex ph (mulBy l ex (α'.2 * α.1) a) b)

def Expand : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ : Type) (m : ℕ) (a : Fin m → MvPowerSeries σ ℂ_[p]), (∀ j, Good (a j)) →
      Simeq (phAt ph (pt ex (∑ j, lg l (a j))))
        (∑ j, phAt ph (a j) + ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), be l ex ph (a j) (a j'))

def SumFirst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ ι : Type) (s : Finset ι) (e : ι → ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]), Good a → Good b →
      (∀ i ∈ s, Good (mulBy l ex (e i) a)) →
      Simeq (∑ i ∈ s, be l ex ph (mulBy l ex (e i) a) b) (be l ex ph (mulBy l ex (∑ i ∈ s, e i) a) b)

def ColumnFor (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])) : Prop :=
  ∀ (k : ℕ) (c d : Fin k → ℂ_[p]), (∀ j, (c j, d j) ∈ S) →
    Simeq (phAt ph (lin l ex c (fun j => (Xv j : MvPowerSeries (Fin k) ℂ_[p]))))
      (∑ j, MvPowerSeries.C (c j * d j) * phAt ph (Xv j) +
        ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'),
          be l ex ph (mulBy l ex (d j' * c j) (Xv j)) (Xv j'))

def Column : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ColumnFor l ex ph S

def Gather : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ColumnFor l ex ph S →
    ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A) (GramRhs l ex ph A)

end PI.UnitaryGroupMassFormula.PhGram
