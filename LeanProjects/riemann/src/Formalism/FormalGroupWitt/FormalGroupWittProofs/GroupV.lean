import Formalism.FormalGroupWitt.FormalGroupWittProofs.FunctionalEquationHomVector
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

noncomputable section

universe u v

namespace Formalism.FG.FormalGroupCoefficients

open MvPowerSeries Formalism.G Formalism.LT

section General

variable {R : Type u} [CommRing R]

theorem hs {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) : HasSubst a :=
  hasSubst_of_constantCoeff_zero ha

theorem cc_subst {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) {g : MvPowerSeries σ R} (hg : constantCoeff g = 0) :
    constantCoeff (subst a g) = 0 :=
  constantCoeff_subst_eq_zero (hs ha) ha hg

theorem cc_X {σ : Type*} (x : σ) : constantCoeff (X x : MvPowerSeries σ R) = 0 := by simp

theorem cc_pderiv {σ : Type*} (g : MvPowerSeries σ R) (i : σ) :
    constantCoeff (pderiv R i g) = coeff (Finsupp.single i 1) g := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem coeff_X_single {σ : Type*} [DecidableEq σ] (i j : σ) :
    coeff (Finsupp.single i 1) (X j : MvPowerSeries σ R) = if i = j then 1 else 0 := by
  rw [coeff_X]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (Finsupp.single_left_injective one_ne_zero h')

theorem lin_subst {σ τ : Type*} [Fintype σ] [Finite τ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ j, constantCoeff (a j) = 0) (g : MvPowerSeries σ R) (i : τ) :
    coeff (Finsupp.single i 1) (g.subst a) =
      ∑ j, coeff (Finsupp.single j 1) g * coeff (Finsupp.single i 1) (a j) := by
  rw [← cc_pderiv, Formalism.G.LogCR.pderiv_subst ha, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, cc_pderiv, Formalism.G.LogP.constantCoeff_subst_of_zero _ ha, cc_pderiv]

end General

section Law

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]

theorem hsX : HasSubst (fun i : ι => (vX i : MvPowerSeries (Fin 2 × ι) R)) :=
  hs fun _ => cc_X _

theorem hsY : HasSubst (fun i : ι => (vY i : MvPowerSeries (Fin 2 × ι) R)) :=
  hs fun _ => cc_X _

theorem inj {f : ι → MvPowerSeries ι R} (hf : IsIdMod2 f) {τ : Type v} [Finite τ]
    {a b : ι → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (h : ∀ j, subst a (f j) = subst b (f j)) : a = b :=
  Formalism.FG.subst_injective_vector.{u, v, v} R ι τ f a b hf ha hb h

variable {f : ι → MvPowerSeries ι R} {F : ι → MvPowerSeries (Fin 2 × ι) R}

theorem key (hF0 : ∀ i, constantCoeff (F i) = 0)
    (hFG : ∀ j, subst F (f j) = atXv (f j) + atYv (f j)) {τ : Type*}
    (b : Fin 2 × ι → MvPowerSeries τ R) (hb : ∀ x, constantCoeff (b x) = 0) (j : ι) :
    subst (fun i => subst b (F i)) (f j) =
      subst (fun i => b ((0 : Fin 2), i)) (f j) + subst (fun i => b ((1 : Fin 2), i)) (f j) := by
  rw [← subst_comp_subst_apply (hs hF0) (hs hb), hFG, subst_add (hs hb), atXv, atYv,
    subst_comp_subst_apply hsX (hs hb), subst_comp_subst_apply hsY (hs hb)]
  simp only [vX, vY, subst_X (hs hb)]

def swp : Fin 2 × ι → MvPowerSeries (Fin 2 × ι) R := fun x => X (Fin.rev x.1, x.2)

def zY : Fin 2 × ι → MvPowerSeries (Fin 2 × ι) R := fun x => if x.1 = 0 then X x else 0

def zX : Fin 2 × ι → MvPowerSeries (Fin 2 × ι) R := fun x => if x.1 = 1 then X x else 0

def c01 : Fin 2 × ι → MvPowerSeries (Fin 3 × ι) R := fun y => v3 (Fin.castSucc y.1) y.2

def c12 : Fin 2 × ι → MvPowerSeries (Fin 3 × ι) R := fun y => v3 y.1.succ y.2

def aL (F : ι → MvPowerSeries (Fin 2 × ι) R) : Fin 2 × ι → MvPowerSeries (Fin 3 × ι) R :=
  fun x => if x.1 = 0 then subst c01 (F x.2) else v3 2 x.2

def aR (F : ι → MvPowerSeries (Fin 2 × ι) R) : Fin 2 × ι → MvPowerSeries (Fin 3 × ι) R :=
  fun x => if x.1 = 0 then v3 0 x.2 else subst c12 (F x.2)

theorem cc_swp (x : Fin 2 × ι) : constantCoeff (swp (R := R) x) = 0 := cc_X _

theorem comm (hf : IsIdMod2 f) (hF0 : ∀ i, constantCoeff (F i) = 0)
    (hFG : ∀ j, subst F (f j) = atXv (f j) + atYv (f j)) : IsCommV F := by
  have h : (fun i => subst swp (F i)) = F := by
    refine inj hf (fun i => cc_subst cc_swp (hF0 i)) hF0 fun j => ?_
    rw [key hF0 hFG swp cc_swp, hFG, add_comm (atXv (f j))]
    rfl
  intro i
  exact congrFun h i

theorem lin (hf : IsIdMod2 f) (hF0 : ∀ i, constantCoeff (F i) = 0)
    (hFG : ∀ j, subst F (f j) = atXv (f j) + atYv (f j)) (i : ι) (x : Fin 2 × ι) :
    coeff (Finsupp.single x 1) (F i) = if x.2 = i then 1 else 0 := by
  have h := congrArg (coeff (Finsupp.single x 1)) (hFG i)
  rw [lin_subst hF0, map_add, atXv, atYv, lin_subst (fun _ => cc_X _),
    lin_subst (fun _ => cc_X _)] at h
  simp only [hf.2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  rw [h, coeff_X_single, coeff_X_single]
  obtain ⟨a, k⟩ := x
  fin_cases a <;> by_cases hk : k = i <;> simp [hk]

end Law

section FunEq

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem integral_X {τ : Type*} (x : τ) : IntegralMv (X x : MvPowerSeries τ K) := fun d => by
  classical
  rw [coeff_X]
  split_ifs <;> simp

end FunEq

end Formalism.FG.FormalGroupCoefficients

namespace Formalism.FG

open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.FormalGroupCoefficients

end Formalism.FG
