import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.Mean4O

section One

variable {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Z : Set X) (r : X → ℝ) (Om : LocPot X)

def leviAt (P : LocPot X) (j : Fin A.n) (y w : Fin e → ℂ) : ℝ :=
  levi (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y w

def LeviEq (P Q : LocPot X) : Prop := ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A P j y w = leviAt A Q j y w

def PshOff (P : LocPot X) : Prop := ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ∀ w, 0 ≤ leviAt A P j y w

def ToBot (u : X → ℝ) : Prop := ∀ a : ℝ, closure {x | x ∉ Z ∧ -a ≤ u x} ⊆ Zᶜ

def cut (S : Set X) (f : X → ℝ) : X → ℝ := (S ∩ Zᶜ).indicator f

def IsBd : Prop :=
  IsClosed Z ∧ (∀ j, MeasureTheory.volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Z) = 0) ∧
  IsPotential A Om ∧ IsPosPot A Om ∧ A.SmoothOn Zᶜ r ∧ (∀ x, x ∉ Z → Real.exp 1 ≤ r x) ∧ ToBot Z (fun x => -r x) ∧
  MIntegrable A (fun _ => Om) (cut Z Set.univ r) ∧
  ∃ c : ℝ, 0 < c ∧ PshOff A Z (Om + LocPot.ofFun fun x => -c * r x)

def ListForm (K : ℝ) (T : LocPot X) : Prop :=
  ∃ (θ : LocPot X) (u : X → ℝ), T = θ + LocPot.ofFun u ∧ IsPotential A θ ∧ IsPsh A (Om.rsmul K + θ) ∧
    IsPsh A (Om.rsmul K + θ.rsmul (-1)) ∧ A.SmoothOn Zᶜ u ∧ (∀ x, x ∉ Z → -(K * Real.log (r x)) ≤ u x ∧ u x ≤ 0) ∧
    (A.Smooth u ∨ ToBot Z u) ∧ PshOff A Z T

def Tail (K C : ℝ) : Prop := ∀ T : Fin e → LocPot X, (∀ i, ListForm A Z r Om K (T i)) →
  MIntegrable A T (cut Z Set.univ fun x => Real.log (r x)) ∧ mInt A T (cut Z Set.univ fun _ => 1) ≤ C ∧
  ∀ R : ℝ, Real.exp 1 ≤ R →
    mInt A T (cut Z {x | R ≤ r x} fun x => Real.log (r x)) ≤ C * Real.log R ^ (e + 1) / R

def Comb (K : ℝ) (P : LocPot X) : Prop :=
  IsPotential A P ∧ ∃ (T : Fin 3 → LocPot X) (c : Fin 3 → ℝ), (∀ l, ListForm A Z r Om K (T l) ∧ |c l| ≤ K) ∧
    ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ∀ w, leviAt A P j y w = ∑ l, c l * leviAt A (T l) j y w

def IsBdSec (L : LocPot X) (s : X → X → ℂ) : Prop :=
  IsPotential A L ∧ IsSection A L s ∧ (∀ x, logNormSec L s x ≤ 0) ∧ Z = P.bdry s ∧ Z ≠ Set.univ ∧
  ∀ x, x ∉ Z → r x = P.rW L s x

theorem IsBdSec.exp_le {L : LocPot X} {s : X → X → ℂ} (h : IsBdSec A Z r L s) (x : X) (hx : x ∉ Z) : Real.exp 1 ≤ r x := by
  rw [h.2.2.2.2.2 x hx, P.rW]
  linarith [h.2.2.1 x]

def IsPoin (b : LocPot X) (p : X → ℝ) : Prop :=
  IsPotential A b ∧ A.SmoothOn Zᶜ p ∧
  (∃ c C : ℝ, 0 < c ∧ ∀ x, x ∉ Z → -(C * Real.log (r x)) ≤ p x ∧ p x ≤ -(c * Real.log (r x))) ∧
  PshOff A Z (b + LocPot.ofFun p)

theorem IsBd.compl_nonempty [Nonempty X] (h : IsBd A Z r Om) : Zᶜ.Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨j, hj⟩ := A.cover x
  by_contra h0
  have h1 := h.2.1 j
  rw [Set.compl_empty_iff.1 (Set.not_nonempty_iff_eq_empty.1 h0), Set.preimage_univ, Set.inter_univ] at h1
  exact ((A.chart j).open_target.measure_pos _ ⟨_, (A.chart j).map_source hj⟩).ne' h1

end One

structure Man (e : ℕ) where

  n : ℕ

  X : Fin (n + 1) → Type
  [top : ∀ σ, TopologicalSpace (X σ)]
  [cpt : ∀ σ, CompactSpace (X σ)]
  [t2 : ∀ σ, T2Space (X σ)]
  [ne : ∀ σ, Nonempty (X σ)]

  A : ∀ σ, FinHolAtlas e (X σ)

  Z : ∀ σ, Set (X σ)

  r : ∀ σ, X σ → ℝ

  Om : ∀ σ, LocPot (X σ)
  bd : ∀ σ, IsBd (A σ) (Z σ) (r σ) (Om σ)

  κ : ℝ
  κ_pos : 0 < κ
  κ_eq : κ = ((n : ℝ) + 1)⁻¹ := by first | exact GlobalTheory.Mean4O.Man.κ_eq _ | simp

attribute [instance] Man.top Man.cpt Man.t2 Man.ne

namespace Man

variable {e : ℕ} (M : Man e)

abbrev Fun : Type := ∀ σ, M.X σ → ℝ

abbrev Pot : Type := ∀ σ, LocPot (M.X σ)

def int (P : Fin e → M.Pot) (u : M.Fun) : ℝ := M.κ * ∑ σ, mInt (M.A σ) (fun i => P i σ) (u σ)

def Smooth (u : M.Fun) : Prop := ∀ σ, (M.A σ).Smooth (u σ)

theorem int_eq (P : Fin e → M.Pot) (u : M.Fun) :
    M.int P u = (∑ σ, mInt (M.A σ) (fun i => P i σ) (u σ)) / ((M.n : ℝ) + 1) := by
  rw [int, M.κ_eq, div_eq_inv_mul]

def FromSec : Prop := ∀ σ, ConnectedSpace (M.X σ) ∧ ∃ (L : LocPot (M.X σ)) (s : M.X σ → M.X σ → ℂ),
  IsBdSec (M.A σ) (M.Z σ) (M.r σ) L s ∧ ∃ (n : ℕ) (W : Fin n → Set (M.X σ)), IsSNC (M.A σ) L s (fun _ => 1) W

end Man

structure Calc {e : ℕ} (M : Man e) where

  V : Type
  [grp : AddCommGroup V]
  [mod : Module ℝ V]

  num : MultilinearMap ℝ (fun _ : Fin (e + 1) => V) ℝ
  symm : ∀ (v : Fin (e + 1) → V) (π : Equiv.Perm (Fin (e + 1))), num (v ∘ π) = num v

  c1 : V → M.Pot
  firstChern_isPotential : ∀ v σ, IsPotential (M.A σ) (c1 v σ)
  isOneCochain_add : ∀ v w σ, LeviEq (M.A σ) (c1 (v + w) σ) (c1 v σ + c1 w σ)
  firstChern_smul_leviEq : ∀ (a : ℝ) v σ, LeviEq (M.A σ) (c1 (a • v) σ) ((c1 v σ).rsmul a)

  ar : M.Fun →ₗ[ℝ] V
  c1_ar : ∀ u, M.Smooth u → ∀ σ, LeviEq (M.A σ) (c1 (ar u) σ) (LocPot.ofFun (u σ))
  num_ar : ∀ u, M.Smooth u → ∀ v : Fin e → V, num (Fin.cons (ar u) v) = M.int (fun i => c1 (v i)) u

attribute [instance] Calc.grp Calc.mod

def Calc.top {e : ℕ} {M : Man e} (K : Calc M) (v : K.V) : ℝ := K.num fun _ => v

def DomL {ι : Type} {N : ℕ} (j : ℕ) (u : ι → Fin N → ℝ) : Prop :=
  ∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (b : ℕ) ≠ j → u τ b ≤ u τ a

structure An {e : ℕ} (M : Man e) (ι : Type) (N : ℕ) where

  th : (ι → Fin N → ℝ) → M.Pot

  a : M.Pot

  ph : (ι → Fin N → ℝ) → M.Fun

  phR : ℝ → (ι → Fin N → ℝ) →ₗ[ℝ] M.Fun

  phS : (ι → Fin N → ℝ) → ℝ → M.Fun

namespace An

variable {e : ℕ} {M : Man e} {ι : Type} [Fintype ι] {N : ℕ} (F : An M ι N) (j : ℕ)

def form (u : ι → Fin N → ℝ) (s : ℝ) (g : M.Fun) : M.Pot :=
  fun σ => F.th u σ + (F.a σ).rsmul s + LocPot.ofFun (g σ)

def FamR : Prop := ∀ Λ : ℝ, ∃ K : ℝ, ∀ u, DomL j u → ‖u‖ ≤ Λ → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ R : ℝ, Real.exp 2 ≤ R → ∀ σ,
  (M.A σ).Smooth (F.phR R u σ) ∧ Comb (M.A σ) (M.Z σ) (M.r σ) (M.Om σ) K (F.form u s (F.phR R u) σ) ∧
  ∀ x, x ∉ M.Z σ → |F.phR R u σ x| ≤ K * Real.log (M.r σ x) ∧
    (M.r σ x ≤ Real.sqrt R → |F.phR R u σ x - F.ph u σ x| ≤ K / R)

def FamS : Prop := ∀ Λ : ℝ, ∃ s₀ : ℝ, 0 < s₀ ∧ ∃ K : ℝ, ∀ u, Dom u → ‖u‖ ≤ Λ → ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ σ,
  (M.A σ).Smooth (F.phS u s σ) ∧ IsPsh (M.A σ) (F.form u s (F.phS u s) σ) ∧
  Comb (M.A σ) (M.Z σ) (M.r σ) (M.Om σ) K (F.form u s (F.phS u s) σ) ∧
  ∀ x, (-(K * Real.log (1 / s)) - K ≤ F.phS u s σ x ∧ F.phS u s σ x ≤ K) ∧
    (x ∉ M.Z σ → F.ph u σ x ≤ F.phS u s σ x ∧ (M.r σ x ≤ (s ^ 2)⁻¹ → F.phS u s σ x ≤ F.ph u σ x + K * s))

def NefAn : Prop := ∀ u, Dom u → ∀ ε : ℝ, 0 < ε → ∀ σ, ∃ g, (M.A σ).Smooth g ∧
  IsPsh (M.A σ) (F.th u σ + (M.Om σ).rsmul ε + LocPot.ofFun g)

def QPol (d : ι → Fin N → ℝ) : Prop := ∀ σ, IsPsh (M.A σ) (F.a σ) ∧
  ∃ (k : ℝ) (g : M.X σ → ℝ) (L : LocPot (M.X σ)) (s : M.X σ → M.X σ → ℂ) (n : ℕ) (m : Fin n → ℕ) (W : Fin n → Set (M.X σ)),
    0 < k ∧ (M.A σ).Smooth g ∧ IsPotential (M.A σ) L ∧ IsSection (M.A σ) L s ∧ IsSNC (M.A σ) L s m W ∧
    LeviEq (M.A σ) L ((F.th d σ + (F.a σ).rsmul (-1)).rsmul k + LocPot.ofFun g)

def Prop4 [DecidableEq ι] (w : ℝ) : Prop := 0 < w ∧ ∀ u, M.int (fun _ => F.th u) (fun _ _ => 1) = w * flagDeg ι N u

def BdDiv (d : ι → Fin N → ℝ) (σ : Fin (M.n + 1)) (L : LocPot (M.X σ)) (s : M.X σ → M.X σ → ℂ) (g : M.X σ → ℝ) : Prop :=
  (M.A σ).Smooth g ∧ IsPotential (M.A σ) L ∧ IsSection (M.A σ) L s ∧
  (∃ (n : ℕ) (m : Fin n → ℕ) (W : Fin n → Set (M.X σ)), IsSNC (M.A σ) L s m W ∧ (∀ i, 1 ≤ m i) ∧ ⋃ i, W i = M.Z σ) ∧
  LeviEq (M.A σ) L (F.th d σ + (F.a σ).rsmul (-1) + LocPot.ofFun g)

def QPolBd (d : ι → Fin N → ℝ) : Prop := ∀ σ, IsPsh (M.A σ) (F.a σ) ∧
  (∃ c : ℝ, 0 < c ∧ IsPsh (M.A σ) (F.a σ + (M.Om σ).rsmul (-c))) ∧ ∃ L s g, F.BdDiv d σ L s g

omit [Fintype ι] in

theorem QPolBd.qPol {F : An M ι N} {d : ι → Fin N → ℝ} (h : F.QPolBd d) : F.QPol d := fun σ => by
  obtain ⟨h₁, -, L, s, g, h₂, h₃, h₄, ⟨n, m, W, h₅, -⟩, h₆⟩ := h σ
  refine ⟨h₁, 1, g, L, s, n, m, W, one_pos, h₂, h₃, h₄, h₅, fun j y hy w => (h₆ j y hy w).trans ?_⟩
  exact congrArg (levi · y w) (funext fun _ => congrArg (· + _) (one_mul _).symm)

def Size : Prop :=
  (∀ σ x, x ∉ M.Z σ → IsLinearMap ℝ fun u => F.ph u σ x) ∧ (∀ u σ, (M.A σ).SmoothOn (M.Z σ)ᶜ (F.ph u σ)) ∧
  (∀ u, Dom u → ∀ σ, PshOff (M.A σ) (M.Z σ) (F.th u σ + LocPot.ofFun (F.ph u σ))) ∧
  ∃ C : ℝ, ∀ u σ x, x ∉ M.Z σ → |F.ph u σ x| ≤ C * ‖u‖ * Real.log (M.r σ x) ∧
    ∀ R : ℝ, 2 ≤ R → |F.phR R u σ x| ≤ C * ‖u‖ * Real.log (M.r σ x)

def InR : Prop := ∀ σ, ∃ (b : LocPot (M.X σ)) (p : M.X σ → ℝ), IsPoin (M.A σ) (M.Z σ) (M.r σ) b p ∧ ∃ C : ℝ,
  ∀ u, ∀ R : ℝ, 2 ≤ R → (M.A σ).Smooth (F.phR R u σ) ∧
    (DomL j u → PshOff (M.A σ) (M.Z σ)
      (F.th u σ + LocPot.ofFun (F.phR R u σ) + (b + LocPot.ofFun p).rsmul (C * ‖u‖))) ∧
    ∀ x, x ∉ M.Z σ → (R ^ 3 ≤ M.r σ x → F.phR R u σ x = 0) ∧
      (M.r σ x ≤ Real.sqrt R → |F.phR R u σ x - F.ph u σ x| ≤ C * ‖u‖ / R)

def InS : Prop := ∃ s₀ : ℝ, 0 < s₀ ∧ ∃ C : ℝ, ∀ u, Dom u → ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ l : ℝ, l = (s ^ 2)⁻¹ → ∀ σ,
  (M.A σ).Smooth (F.phS u s σ) ∧
  IsPsh (M.A σ) (F.th u σ + LocPot.ofFun (F.phS u s σ) + (M.Om σ).rsmul (C * ‖u‖ * (Real.log l / l))) ∧
  ∀ x, (-(C * ‖u‖ * Real.log l) - C * ‖u‖ ≤ F.phS u s σ x ∧ F.phS u s σ x ≤ C * ‖u‖) ∧
    (x ∉ M.Z σ → F.ph u σ x ≤ F.phS u s σ x ∧
      (M.r σ x ≤ l → F.phS u s σ x ≤ F.ph u σ x + C * ‖u‖ * Real.exp (-l / 3) + C * ‖u‖ * (Real.log l / l)) ∧
      F.phS u s σ x ≤ F.ph u σ x + C * ‖u‖ * Real.exp (-l / 3) + C * ‖u‖ * (Real.log l / l) * M.r σ x)

def SecCmp (d : ι → Fin N → ℝ) : Prop := ∀ σ L t g, F.BdDiv d σ L t g → ∀ Λ : ℝ, ∃ s₀ : ℝ, 0 < s₀ ∧ ∃ C : ℝ,
  ∀ u, ‖u‖ ≤ Λ → ∀ s : ℝ, 0 < s → s ≤ s₀ → Dom (u - s • d) → ∀ x, x ∉ M.Z σ →
    s * (logNormSec L t x + g x) + F.phS (u - s • d) s σ x - F.ph u σ x ≤ C * s

end An

variable {D : D7} (Y : ShimX D.what₂.Tau)

structure Real0 where

  M : Y.Comp → Man (dimY Y)

  F : ∀ c, An (M c) D.what₂.Tau Y.N

  K : ℝ → ∀ c, Calc (M c)

  L : ∀ B c, Wt Y →ₗ[ℝ] (K B c).V

  a : ∀ B c, (K B c).V
  th_pot : ∀ c u σ, IsPotential ((M c).A σ) ((F c).th u σ)
  a_pot : ∀ c σ, IsPotential ((M c).A σ) ((F c).a σ)
  c1_L : ∀ B c u σ, LeviEq ((M c).A σ) ((K B c).c1 (L B c u) σ) ((F c).th u σ)
  firstChern_leviEq_constant : ∀ B c σ, LeviEq ((M c).A σ) ((K B c).c1 (a B c) σ) ((F c).a σ)

variable {Y} (T : Real0 Y) (A : SlopeTestRemainingChoices Y)

def Real0.fR (B : ℝ) (c : Y.Comp) (u : Wt Y) (s R : ℝ) : ℝ :=
  (T.K B c).top (T.L B c u + s • T.a B c + (T.K B c).ar ((T.F c).phR R u))

def TieDeg : Prop := ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, Real.exp 2 ≤ R → ∀ u : Wt Y,
  Y.arDeg (setB Y B) R (linRoot u ^ (dimY Y + 1)) = ∑ c, T.fR B c u 0 R

def Real0.Conv : Prop := ∀ B : ℝ, 2 ≤ B → ∀ c (u : Wt Y) (s : ℝ), ∃ a, Tendsto (T.fR B c u s) atTop (𝓝 a)

def TieLim : Prop := ∀ B : ℝ, 2 ≤ B → ∀ c, (A.Ps B c).IsHomogeneous (dimY Y + 1) ∧
  ∀ (u : Wt Y) (s a : ℝ), Tendsto (T.fR B c u s) atTop (𝓝 a) → evS Y (A.Ps B c) u s = a

def TiePs : Prop := ∀ B : ℝ, 2 ≤ B → ∀ c, (A.Ps B c).totalDegree ≤ dimY Y + 1 ∧
  ∀ (u : Wt Y) (s : ℝ), Tendsto (T.fR B c u s) atTop (𝓝 (evS Y (A.Ps B c) u s))

variable {T A} in

theorem TieLim.tiePs (h : TieLim T A) (hc : T.Conv) : TiePs T A := fun B hB c =>
  ⟨(h B hB c).1.totalDegree_le, fun u s => by
    obtain ⟨a, ha⟩ := hc B hB c u s
    rwa [(h B hB c).2 u s a ha]⟩

variable {T A} in

theorem TiePs.conv (h : TiePs T A) : T.Conv := fun B hB c u s => ⟨_, (h B hB c).2 u s⟩

def TieM : Prop := ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt Y) (s : ℚ), IsRat Y u → 0 < s →
  (∀ c, Y.geoC (Y.Mbar B u s) c = (T.M c).int (fun _ => (T.F c).form (A.sh u s) s 0) (fun _ _ => 1)) ∧
  (Dominant Y (A.sh u s) → (∀ c, (T.M c).Smooth ((T.F c).phS (A.sh u s) s)) →
    (∀ c, Y.arSelfC (Y.Mbar B u s) c =
      (T.K B c).top (T.L B c (A.sh u s) + (s : ℝ) • T.a B c + (T.K B c).ar ((T.F c).phS (A.sh u s) s))) ∧
    (Y.semipos (Y.Mbar B u s) ↔
      ∀ c σ, IsPsh ((T.M c).A σ) ((T.F c).form (A.sh u s) s ((T.F c).phS (A.sh u s) s) σ)))

def VertBd : Prop := ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ c (u : Wt Y), Dominant Y u → ‖u‖ ≤ 1 → ∀ s ∈ Set.Icc (0 : ℝ) 1,
  ∀ R : ℝ, Real.exp 2 ≤ R → |T.fR B c u s R - T.fR 2 c u s R| ≤ C * Real.log B

def NefGlue : Prop := ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt Y) (s : ℚ), IsRat Y u → 0 < s →
  (∀ p ∈ setB Y B, NefHT Y p (A.sh u s)) → (∀ p : ℕ, p.Prime → p ∉ setB Y B → NefDR Y p (A.sh u s)) →
  Y.nefFib (Y.Mbar B u s)

variable (Y) in

structure Ht where

  h0 : Wt Y → Y.Pt → ℝ

  hH : Wt Y → Y.Pt → ℝ

  hA : Y.Pt → ℝ

  int : Set Y.Pt

  falt : Y.Pt → ℝ

variable (H : Ht Y)

structure Real0.Pts where

  d : Y.Pt → ℕ

  conj : ∀ (c : Y.Comp) (y : Y.Pt) (σ : Fin ((T.M c).n + 1)), Fin (d y + 1) → (T.M c).X σ

  ht : ∀ (B : ℝ) (c : Y.Comp), Y.Pt → (T.K B c).V →ₗ[ℝ] ℝ

variable {T} (P : T.Pts)

def Real0.Pts.mean (c : Y.Comp) (y : Y.Pt) (g : (T.M c).Fun) : ℝ :=
  (T.M c).κ * ∑ σ, (∑ i, g σ (P.conj c y σ i)) / ((P.d y : ℝ) + 1)

theorem Real0.Pts.mean_le {c : Y.Comp} {y : Y.Pt} {g g' : (T.M c).Fun}
    (h : ∀ σ i, g σ (P.conj c y σ i) ≤ g' σ (P.conj c y σ i)) : P.mean c y g ≤ P.mean c y g' :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ =>
    div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => h σ i) (by positivity)) (T.M c).κ_pos.le

theorem Real0.Pts.mean_const (c : Y.Comp) (y : Y.Pt) (a : ℝ) : P.mean c y (fun _ _ => a) = a := by
  simp only [Real0.Pts.mean, (T.M c).κ_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

def HtTie : Prop :=
  (∀ B y g, (T.M (Y.compPt y)).Smooth g → P.ht B _ y ((T.K B (Y.compPt y)).ar g) = P.mean _ y g) ∧
  (∀ y, IsLinearMap ℝ fun u => H.h0 u y) ∧
  (∀ y, y ∈ H.int ↔ ∀ σ i, P.conj (Y.compPt y) y σ i ∉ (T.M _).Z σ) ∧
  (∀ u, ∀ y ∈ H.int, H.hH u y = H.h0 u y + P.mean (Y.compPt y) y ((T.F _).ph u)) ∧
  ∀ B : ℝ, 2 ≤ B → (∀ y, H.hA y = P.ht B (Y.compPt y) y (T.a B _)) ∧
    ∀ (u : Wt Y) (s : ℚ), IsRat Y u → 0 < s → Dominant Y (A.sh u s) →
      (∀ c, (T.M c).Smooth ((T.F c).phS (A.sh u s) s)) → ∀ y, A.ht (Y.Mbar B u s) y = P.ht B (Y.compPt y) y
        (T.L B _ (A.sh u s) + (s : ℝ) • T.a B _ + (T.K B _).ar ((T.F _).phS (A.sh u s) s))

def LatCmp : Prop := ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt Y) y,
  |P.ht B (Y.compPt y) y (T.L B _ u) - H.h0 u y| ≤ C * ‖u‖ * Real.log B

variable (Y) in

def midWt : Wt Y := fun _ i => if (i : ℕ) < Y.j then 1 else 0

example (τ : D.what₂.Tau) : gap Y (midWt Y) τ = 1 := by
  have := Y.j_pos
  simp [gap, midWt, show Y.j - 1 < Y.j by omega]

def HtFalt : Prop := ∃ C : ℝ, ∀ y ∈ H.int, |H.hH (midWt Y) y - H.falt y / 2| ≤ C

variable (T) in

def Real0.gen (B : ℝ) (c : Y.Comp) (m : ℕ) : Option (D.what₂.Tau × Fin Y.N) → (T.K B c).V :=
  fun o => o.elim ((m : ℝ) • T.a B c) fun x => T.L B c (Pi.single x.1 (Pi.single x.2 1))

def HtCmp : Prop := ∃ s₀ : ℝ, 0 < s₀ ∧ ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt Y) (s : ℚ), IsRat Y u → ‖u‖ ≤ 1 → 0 < s →
  (s : ℝ) ≤ s₀ → Dominant Y (A.sh u s) → ∀ y,
    H.h0 (A.sh u s) y + s * H.hA y - C * Real.log (B / s) ≤ A.ht (Y.Mbar B u s) y ∧
    A.ht (Y.Mbar B u s) y ≤ H.h0 (A.sh u s) y + s * H.hA y + C * Real.log B ∧
    (y ∈ H.int → H.hH (A.sh u s) y + s * H.hA y - C * Real.log B ≤ A.ht (Y.Mbar B u s) y)

def HtInt : Prop := ∃ C : ℝ, ∀ u : Wt Y, Dominant Y u → ‖u‖ ≤ 2 → ∀ g : ℝ, 0 ≤ g → (∀ τ, g ≤ gap Y u τ) → ∀ y ∈ H.int,
  g / 2 * max (H.falt y) 0 - C * Real.log (2 + max (H.falt y) 0) - C ≤ H.hH u y

def HtBd : Prop := ∃ C : ℝ, 1 ≤ C ∧ (∀ y, -C ≤ H.hA y) ∧ ∀ u : Wt Y, Dominant Y u → ‖u‖ ≤ 2 → ∀ y, y ∉ H.int →
  -(C * Real.log (2 + C + H.hA y)) - C ≤ H.h0 u y

def HtUp : Prop := ∀ c, ∃ Z, A.dense c Z ∧ ∃ C : ℝ, ∀ y ∈ Z, |H.hA y| ≤ C ∧ ∀ u : Wt Y, |H.h0 u y| ≤ C * ‖u‖

end GlobalTheory.Mean4O
