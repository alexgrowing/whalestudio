import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRamifiedPlacesHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumChar

open Formalism.L2.JoinChr

theorem locE_sum {D : D7} {ι : Type} (s : Finset ι) (f : ι → AE D)
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) (k : D.host.E) :
    locE D (∑ i ∈ s, f i) k = ∏ i ∈ s, locE D (f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [locE]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      ← ih fun i hi j hj hij => hf i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    have h0 : f a * ∑ i ∈ s, f i = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i hi => hf a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    unfold locE
    linear_combination (-(incA D k - 1) * (incA D k - 1)) * h0

theorem char_eq_prod : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (eQ : AE D), IsIdemSum eQ Q → ∀ (k : D.host.Eˣ) (y : (AE D)ˣ), (y : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (k : D.host.E) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → ((c y : Circle) : ℂ) = ∏ P ∈ Q, ((ψ.locK (conjPl P) k : ℂˣ) : ℂ) := by
  intro D Q eQ h k y hy c ψ hψ
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  have hIP : ∀ P ∈ Q, Formalism.L2.NTheta.IsIdemAt (cA D (es P)) (conjPl P) := fun P hP =>
    GlobalTheory.MovedIdem.isIdemAt_conj (hes P hP) fun _ => Iff.rfl
  let g : Pl D.host.E → AE D := fun P => if P ∈ Q then cA D (es P) else 0
  have hg : ∀ P, g P * g P = g P := fun P => by
    by_cases hP : P ∈ Q
    · simp only [g, if_pos hP]; exact (hIP P hP).1.1
    · simp only [g, if_neg hP, mul_zero]
  have horth : ∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → g P * g P' = 0 := fun P hP P' hP' hne => by
    simp only [g, if_pos hP, if_pos hP', ← map_mul]
    rw [idem_orth (idemAt_split (hes P hP)) (hes P hP) (hes P' hP') hne, map_zero]
  have hsum : cA D (∑ P ∈ Q, es P) = ∑ P ∈ Q, g P := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun P hP => by simp only [g, if_pos hP]
  have hy' : y = ∏ P ∈ Q, locU (hg P) k := by
    apply Units.ext
    rw [hy, Units.coe_prod, hsum, locE_sum Q g horth]
    rfl
  rw [hy', map_prod]
  have hcoe : ∀ (s : Finset (Pl D.host.E)) (u : Pl D.host.E → Circle),
      (((∏ P ∈ s, u P : Circle)) : ℂ) = ∏ P ∈ s, ((u P : Circle) : ℂ) := fun s u =>
    map_prod Circle.coeHom u s
  rw [hcoe]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hpl : IsPlIdem D (g P) (conjPl P) := by
    simp only [g, if_pos hP]; exact GlobalTheory.HeckeDetChar.isPlIdem (hIP P hP)
  exact hψ.2 (conjPl P) (g P) hpl k (locU (hg P) k) (locU_val _ _)

end GlobalTheory.IdemSumChar
