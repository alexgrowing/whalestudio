import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IopNorm

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable {D : Car} {N N' : ℕ}

def Good (D : Car) (w : ℂ) : Prop :=
  ∃ a b : ℤ, Even (a - b) ∧ w = (((a : ℝ) / Real.sqrt D.host.d : ℝ) : ℂ) + (b : ℂ) * Complex.I

theorem good_zero : Good D 0 := ⟨0, 0, by simp, by simp⟩

theorem good_add {u v : ℂ} (hu : Good D u) (hv : Good D v) : Good D (u + v) := by
  obtain ⟨a, b, hab, rfl⟩ := hu
  obtain ⟨a', b', hab', rfl⟩ := hv
  refine ⟨a + a', b + b', ?_, ?_⟩
  · have e : a + a' - (b + b') = (a - b) + (a' - b') := by ring
    rw [e]; exact hab.add hab'
  · push_cast; ring

theorem good_neg {u : ℂ} (hu : Good D u) : Good D (-u) := by
  obtain ⟨a, b, hab, rfl⟩ := hu
  refine ⟨-a, -b, ?_, ?_⟩
  · rw [show -a - -b = -(a - b) by ring]; exact hab.neg
  · push_cast; ring

theorem Hf_zero_left (T : Tor D) (y : VC D N N') : Hf D T 0 y = 0 := by simp [Hf]

theorem Hf_zero_right (T : Tor D) (x : VC D N N') : Hf D T x 0 = 0 := by simp [Hf]

theorem Hf_neg_left (T : Tor D) (x y : VC D N N') : Hf D T (-x) y = -Hf D T x y := by
  have h := Hf_add_left T x (-x) y
  rw [add_neg_cancel, Hf_zero_left] at h
  linear_combination -h

theorem Hf_neg_right (T : Tor D) (x y : VC D N N') : Hf D T x (-y) = -Hf D T x y := by
  have h := Hf_add_right T x y (-y)
  rw [add_neg_cancel, Hf_zero_right] at h
  linear_combination -h

theorem Hf_smul (T : Tor D) (u u' : ℂ) (x y : VC D N N') :
    Hf D T (u • x) (u' • y) = u * starRingEnd ℂ u' * Hf D T x y := by
  unfold Hf
  rw [mul_div_assoc']
  congr 1
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem HfInt_closure (T : Tor D) (S : Set (VC D N N'))
    (h : ∀ x ∈ S, ∀ y ∈ S, Good D (Hf D T x y)) : HfInt T (AddSubgroup.closure S) := by
  have h1 : ∀ x ∈ AddSubgroup.closure S, ∀ y ∈ S, Good D (Hf D T x y) := by
    intro x hx y hy
    induction hx using AddSubgroup.closure_induction with
    | mem x hx => exact h x hx y hy
    | zero => rw [Hf_zero_left]; exact good_zero
    | add x x' _ _ h1 h2 => rw [Hf_add_left]; exact good_add h1 h2
    | neg x _ h1 => rw [Hf_neg_left]; exact good_neg h1
  intro x hx y hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy => exact h1 x hx y hy
  | zero => rw [Hf_zero_right]; exact good_zero
  | add y y' _ _ h1 h2 => rw [Hf_add_right]; exact good_add h1 h2
  | neg y _ h1 => rw [Hf_neg_right]; exact good_neg h1

theorem HfInt_mono (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hle : La₁ ≤ La₂)
    (h : HfInt T La₂) : HfInt T La₁ :=
  fun x hx y hy => h x (hle hx) y (hle hy)

def genLa (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Set (VC D N N') :=
  {z | ∃ c ∈ cc, ∃ A ∈ YYl D L L',
    z = (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • embV D (tor0 D cc δ) A}

theorem La_le_gen (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    La D (tor0 D cc δ) L L' ≤ AddSubgroup.closure (genLa D cc δ L L') := by
  unfold La
  rw [AddSubgroup.closure_le]
  rintro z ⟨w, hw, A, hA, rfl⟩
  change w ∈ lamOf D cc δ at hw
  unfold lamOf at hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨c, hc, A, hA, rfl⟩
  | zero => rw [zero_smul]; exact AddSubgroup.zero_mem _
  | add w w' _ _ h1 h2 => rw [add_smul]; exact AddSubgroup.add_mem _ h1 h2
  | neg w _ h1 => rw [neg_smul]; exact AddSubgroup.neg_mem _ h1

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def HfGenRec : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 →
    ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      ∀ c ∈ cc, ∀ c' ∈ cc, ∀ A ∈ YYl D L L', ∀ B ∈ YYl D L L',
        Good D (δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) *
          starRingEnd ℂ (δ * D.host.φ₀ (((c' : D.host.K) : D.host.E))) *
          Hf D (tor0 D cc δ) (embV D (tor0 D cc δ) A) (embV D (tor0 D cc δ) B))

theorem HfIntRec_of_gen (h : HfGenRec) : HfIntRec := by
  intro D cc hcc δ hδ h0 N N' L L' hA
  refine HfInt_mono _ (La_le_gen cc δ L L') (HfInt_closure _ _ ?_)
  rintro x ⟨c, hc, A, hA', rfl⟩ y ⟨c', hc', B, hB', rfl⟩
  rw [Hf_smul]
  exact h D cc hcc δ hδ h0 N N' L L' hA c hc c' hc' A hA' B hB'

theorem LinkThIndep_of_gen (hA : HfGenRec) (hB : SelfDualRec) : LinkThIndep :=
  LinkThIndep_of_parts (HfIntRec_of_gen hA) hB

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
