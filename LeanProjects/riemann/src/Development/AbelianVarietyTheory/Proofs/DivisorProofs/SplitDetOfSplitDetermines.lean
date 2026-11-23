import Mathlib
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisedDualSystem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BaseSetLabels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev IsDedekindDomain NumberField Polynomial
open scoped Pointwise

namespace GlobalTheory.PartsCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section Poly

variable {K L : Type} [Field K] [Field L]

theorem dualPoly_map (φ : K →+* L) (s : K) (p : K[X]) : (dualPoly s p).map φ = dualPoly (φ s) (p.map φ) := by
  ext i
  rw [coeff_map, coeff_dualPoly, coeff_dualPoly, natDegree_map, leadingCoeff_map, coeff_map]
  simp

theorem dualPoly_comp {a : K} (ha : a ≠ 0) (s : K) (p : K[X]) :
    dualPoly s (p.comp (C a⁻¹ * X)) = dualPoly (s * a) p := by
  have hd : (p.comp (C a⁻¹ * X)).natDegree = p.natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero ha), mul_one]
  have hl : (p.comp (C a⁻¹ * X)).leadingCoeff = p.leadingCoeff * a⁻¹ ^ p.natDegree := by
    rw [leadingCoeff, hd, comp_C_mul_X_coeff, leadingCoeff]
  ext i
  by_cases hi : i ≤ p.natDegree
  · rw [coeff_dualPoly_of_le _ _ (hd ▸ hi), coeff_dualPoly_of_le _ _ hi, hl, hd, comp_C_mul_X_coeff]
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi
    rw [hj, Nat.add_sub_cancel_left, pow_add, mul_pow]
    have h1 : a⁻¹ ^ i * a ^ i = 1 := by rw [← mul_pow, inv_mul_cancel₀ ha, one_pow]
    have h2 : a⁻¹ ^ j ≠ 0 := pow_ne_zero _ (inv_ne_zero ha)
    have h3 : (a⁻¹ ^ i)⁻¹ = a ^ i := by rw [inv_pow, inv_inv]
    rw [mul_inv, mul_inv, h3]
    field_simp
  · have hi' := not_le.1 hi
    rw [coeff_dualPoly_of_lt _ _ (hd ▸ hi'), coeff_dualPoly_of_lt _ _ hi']

theorem coeff_heckePolyOf (n q : ℕ) (a : ℕ → K) (i : ℕ) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff i =
      if i ≤ n then (-1) ^ i * (q : K) ^ (i * (i - 1) / 2) * a i else 0 := by
  unfold Formalism.L2.Col.heckePolyOf
  simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range,
    Nat.lt_succ_iff]

theorem tri_add (i j : ℕ) : (i + j) * (i + j - 1) / 2 + i * (i - 1) / 2 = j * (j - 1) / 2 + (i + j - 1) * i := by
  have h : ∀ n : ℕ, 2 * (n * (n - 1) / 2) + n = n * n := by
    intro n
    rw [Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
    cases n with
    | zero => rfl
    | succ m => simp; ring
  have h1 := h (i + j)
  have h2 := h i
  have h3 := h j
  have h4 : (i + j - 1) * i + i = (i + j) * i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have : m + 1 + j - 1 = m + j := by omega
      rw [this]; ring
  nlinarith

theorem heckePolyOf_dual {n q : ℕ} (hq : (q : K) ≠ 0) {a b : ℕ → K} (h0 : a 0 = 1)
    (h : ∀ k ≤ n, a n * b k = a (n - k)) :
    Formalism.L2.Col.heckePolyOf n q b = dualPoly ((q : K) ^ (n - 1)) (Formalism.L2.Col.heckePolyOf n q a) := by
  have hn : a n ≠ 0 := by
    have := h n le_rfl
    rw [Nat.sub_self, h0] at this
    exact left_ne_zero_of_mul_eq_one this
  have htop : (Formalism.L2.Col.heckePolyOf n q a).coeff n ≠ 0 := by
    rw [coeff_heckePolyOf, if_pos le_rfl]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) (pow_ne_zero _ hq)) hn
  have hd : (Formalism.L2.Col.heckePolyOf n q a).natDegree = n :=
    le_antisymm (natDegree_le_iff_coeff_eq_zero.2 fun i hi => by rw [coeff_heckePolyOf, if_neg (not_le.2 hi)])
      (le_natDegree_of_ne_zero htop)
  ext i
  by_cases hi : i ≤ n
  · rw [coeff_dualPoly_of_le _ _ (by rw [hd]; exact hi), leadingCoeff, hd, eq_inv_mul_iff_mul_eq₀ htop,
      coeff_heckePolyOf, coeff_heckePolyOf, coeff_heckePolyOf, if_pos le_rfl, if_pos hi, if_pos (Nat.sub_le _ _),
      ← h i hi]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Nat.add_sub_cancel_left, ← pow_mul]
    have e := congrArg (fun m => (q : K) ^ m) (tri_add i j)
    simp only [pow_add] at e
    have e2 : ((-1 : K) ^ i) * (-1) ^ i = 1 := by rw [← mul_pow]; simp
    rw [pow_add]
    linear_combination ((-1 : K) ^ j * a (i + j) * b i * ((-1) ^ i * (-1) ^ i)) * e +
      ((-1 : K) ^ j * a (i + j) * b i * ((q : K) ^ (j * (j - 1) / 2) * (q : K) ^ ((i + j - 1) * i))) * e2
  · rw [coeff_dualPoly_of_lt _ _ (by rw [hd]; exact not_le.1 hi), coeff_heckePolyOf, if_neg hi]

end Poly

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem mem_ok_iff {R : RealDat D A Ks} {F : Face D A} (h : R.Char F) (P : Pl0) :
    P ∈ A.ok A.μ0 ↔ Formalism.IndefR.Bridge.SplitOff (R.pl P) (R.Sb : Set (Pl D.host.E)) := by
  obtain ⟨_, _, _, ht⟩ := h.fam.tie
  have hQ : R.Q A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
    refine (h.lev.Q_ram A.μ0 PP).2 (Or.inl hP) ?_
    rw [h.lev.xi_base]
    intro x _
    rfl
  rw [ht.ok, hQ, Finset.coe_empty, Set.union_empty]

theorem q_ne_zero {s : ℕ} (h : A.fam.Ok s) {P : Pl0} (hP : P ∈ A.ok A.μ0) : A.q P ≠ 0 :=
  ((h.what₂ A.μ0).q_pos ⟨P, hP⟩).ne'

theorem polW_eq (p : Pl0 → D.what₂.LL[X]) {P : Pl0} (hq : A.q P ≠ 0) :
    RealDat.polW (A := A) p P = dualPoly ((A.q P : ℂ) ^ (D.R.r - 1)) (RealDat.polE (A := A) p P) := by
  unfold RealDat.polW RealDat.polE
  rw [dualPoly_comp (pow_ne_zero _ (Nat.cast_ne_zero.2 hq)), dualPoly_map, map_pow, map_natCast, pow_add]

theorem polE_coeff_zero {R : RealDat D A Ks} {F : Face D A} (h : R.Char F) (p : A.fam.base.Ix) (P : Pl0) :
    (RealDat.polE (A := A) p.1 P).coeff 0 = 1 := by
  unfold RealDat.polE
  rw [comp_C_mul_X_coeff, coeff_map, A.const_of (fun P => (h.fam.degR A.μ0 P).1) p.1 p.2 P]
  simp

def DualPol (R : RealDat D A Ks) (c : PolarisedDualSystem.Sys D) : Prop :=
  ∀ P ∈ A.ok A.μ0, (PolarisedDualSystem.polAt R (PolarisedDualSystem.dualSys c) P).coeff 0 = 1 ∧
    PolarisedDualSystem.polAt R c P = dualPoly ((A.q P : ℂ) ^ (D.R.r - 1)) (PolarisedDualSystem.polAt R (PolarisedDualSystem.dualSys c) P)

def CentralRel (R : RealDat D A Ks) (c : PolarisedDualSystem.Sys D) : Prop :=
  ∀ P ∈ A.ok A.μ0, c (R.pl P) (splitLab D.R.r 0) = 1 ∧ ∀ k ≤ D.R.r,
    c (R.pl P) (splitLab D.R.r D.R.r) * c (R.pl P) (dualLab (splitLab D.R.r k)) = c (R.pl P) (splitLab D.R.r (D.R.r - k))

section Label

variable {R : RealDat D A Ks} {F : Face D A} {s : ℕ} (hs : A.fam.Ok s) (h : R.Char F)
include hs h

variable {X : DivX D} {E : EigIdx D X} {sys : E.Pi → PolarisedDualSystem.Sys D} {jE : D.what₂.EE →ₗ[ℂ] R.HE.H}
  {jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H}

end Label

def SameIndex (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ c, PolarisedDualSystem.Occ R c ↔ ∃ i, BaseSetLabels.OccW R (PolarisedDualSystem.badF R) i (BaseSetLabels.conjugateBaseLevel R F) c

section Ties

variable {R : RealDat D A Ks} {F : Face D A} {X : DivX D} {E : EigIdx D X} {sys : E.Pi → PolarisedDualSystem.Sys D}
  {jE : D.what₂.EE →ₗ[ℂ] R.HE.H} {jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H}

end Ties

def PartsStAt (R : RealDat D A Ks) (F : Face D A) {X : DivX D} (E : EigIdx D X) : Prop :=
  ∀ (s : ℕ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (eig : E.Pi → BaseSetLabels.Eig D) (jE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    (jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H),
    A.fam.Ok s → R.Char F → BaseSetLabels.Tied R F S E eig jE jW → BaseSetLabels.PartsAt R E eig jE jW

def Bridge (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ s : ℕ, A.fam.Ok s → R.Char F → SameIndex R F ∧ ∀ c, PolarisedDualSystem.Occ R c → CentralRel R c

def SplitDetRow (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ s : ℕ, A.fam.Ok s → R.Char F → PolarisedDualSystem.SplitDet R

def TieExists (R : RealDat D A Ks) (F : Face D A) {X : DivX D} (E : EigIdx D X) : Prop :=
  ∃ S eig jE jW, BaseSetLabels.Tied R F S E eig jE jW

section Main

variable {R : RealDat D A Ks} {F : Face D A} {X : DivX D} {E : EigIdx D X}

end Main

end GlobalTheory.PartsCompare

end
