import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators

theorem typeIdeal_ne (D : D7) :
    Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
  rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
  exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

def typePlaces (D : D7) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (Ideal.finite_factors (typeIdeal_ne D)).toFinset

theorem mem_typePlaces (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    v ∈ typePlaces D ↔ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  rw [typePlaces, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]

abbrev Eig (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

def LowGaps (D : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (j : ℕ) (h : j + 1 < D.R.m),
    4 * (D.R.N D.R.m : ℚ) ^ 3 + 2 * (D.R.t : ℚ) + 6 ≤ (D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def InFirstRow {Pg : Finset (Pl D.host.E)} {r : ℕ} (PP : Pg) (g : G0 Pg r) : Prop :=
  (∀ PP' : Pg, PP' ≠ PP → g PP' = 1) ∧
    ∀ a b : Fin r, 0 < (a : ℕ) → (g PP : Matrix (Fin r) (Fin r) (kP PP.1)) a b = (1 : Matrix (Fin r) (Fin r) (kP PP.1)) a b

open Classical in

def GoodTypes (R : RealDat D A Ks) : Prop :=
  ∀ χ ∈ A.X, IsAbsIrrChar χ ∧ ∀ (PP : R.Pg) (j : Fin D.R.m) (s : ℤˣ),
    ∑ g ∈ Finset.univ.filter (fun g : G => InFirstRow PP (R.eG g)),
      (((R.chi ((j : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP))) ^ (s : ℤ) : ℂˣ) : ℂ) * D.what₂.embLL (χ g) = 0

def TwistOffDatum (R : RealDat D A Ks) : Prop :=
  ∀ t, ∀ PP ∈ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

def partE (R : RealDat D A Ks) (c : Eig D) : Submodule ℂ R.HE.H :=
  (partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (typePlaces D) c ⊓
    R.EEat R.triv).comap R.HE.e

def partW (R : RealDat D A Ks) (i : Fin D.R.m) (c : Eig D) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv))
      (typePlaces D) c ⊓ R.Wat i (sg0 D A) R.triv).comap (R.HW i (sg0 D A)).e

def dnUp (R : RealDat D A Ks) (t : T) : R.HE.H →ₗ[ℂ] R.HE.H := R.Th t ∘ₗ LinearMap.adjoint (R.Th t)

def IsLam (R : RealDat D A Ks) (lam : T → ℕ → Eig D → ℝ) : Prop :=
  ∀ (i : Fin D.R.m) (t : T), Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (partW R i) (lam t ((i : ℕ) + 1))

def Concl (R : RealDat D A Ks) : Prop :=
  ∃ lam : T → ℕ → Eig D → ℝ, (∀ t j c, 0 < lam t j c) ∧ IsLam R lam ∧ Lift.ThmB D.R.m (dnUp R) (partE R) lam

def ThmBAt (R : RealDat D A Ks) (F : Face D A) : Prop :=
  LowGaps D → R.toLevCh.Is A.μ0 → TwistOffDatum R → GoodTypes R →
    R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → R.IsThP → Concl R

theorem Concl.scalar_pos {R : RealDat D A Ks} (h : Concl R) (t : T) (c : Eig D) :
    ∃ l : ℝ, 0 < l ∧ ∀ x ∈ partE R c, dnUp R t x = (l : ℂ) • x := by
  obtain ⟨lam, hpos, -, κ, hκ, hK⟩ := h
  exact ⟨_, mul_pos hκ (Finset.prod_pos fun j _ => hpos t j c), hK t c⟩

theorem Concl.of_match {R : RealDat D A Ks} (h : Concl R) (hm : ∀ c, partE R c ≠ ⊥ → ∀ i, partW R i c ≠ ⊥) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ lam, IsLam R lam → Lift.IsKap D.R.m (dnUp R) (partE R) lam κ := by
  obtain ⟨lam, -, hl, κ, hκ, hK⟩ := h
  refine ⟨κ, hκ, fun lam' hl' t c x hx => ?_⟩
  by_cases h0 : partE R c = ⊥
  · rw [h0, Submodule.mem_bot] at hx
    rw [hx, map_zero, smul_zero]
  · rw [hK t c x hx]
    congr 3
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    have := Lift.IsLamP.unique (hl ⟨j - 1, by omega⟩ t) (hl' ⟨j - 1, by omega⟩ t) (hm c h0 _)
    rwa [show j - 1 + 1 = j by omega] at this

end

def ThmB : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ThmBAt R F

end GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators

end
