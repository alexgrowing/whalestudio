import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.Resid

open GlobalTheory.Mem.SymFrame

variable {D : D7}

theorem rank_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  unfold Ranks.r Ranks.rS
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

def posE (D : D7) (a : Fin D.R.rS) : Fin D.R.r := ⟨a.1, by have := rank_eq D; omega⟩

def posB (D : D7) (i : Fin D.R.k) : Fin D.R.r := ⟨D.R.rS + i.1, by have := rank_eq D; omega⟩

def posN (D : D7) (a : Fin D.R.rS) : Fin D.R.r :=
  ⟨if a.1 + 1 < D.R.rS then a.1 + 1 else D.R.rS + D.R.k, by have := rank_eq D; split_ifs <;> omega⟩

theorem symVec_posN (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.rS) :
    symVec X w (posN D a) = nxt X.e0 X.z0 a := by
  unfold symVec GlobalTheory.SeeConjRead.flagV posN nxt
  by_cases h : a.1 + 1 < D.R.rS
  · simp [h]
  · have h2 : ¬ (D.R.rS + D.R.k < D.R.rS) := by omega
    simp [h]

theorem symVec_posB (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : EwAt X w) (i : Fin D.R.k) :
    symVec X w (posB D i) = X.bw i := by
  unfold symVec GlobalTheory.SeeConjRead.flagV posB epsW
  have h1 : ¬ (D.R.rS + i.1 < D.R.rS) := by omega
  have h2 : D.R.rS + i.1 < D.R.rS + D.R.k := by omega
  simp [h1, h2, hw]

theorem dual_row (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hN : IsMatIn X w u x N)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (i₀ : Fin D.R.r)
    (hd : ∀ j, hA X.B.I y (u j) - (if j = i₀ then 1 else 0) ∈ wInt X w) (i : Fin D.R.r) :
    hA X.B.I y (X.B.I.fmat x *ᵥ u i) - (((N i₀ i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈
      wInt X w := by
  have h := hA_isMatIn X w hN hy i
  have hs : (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I y (u j) - (if j = i₀ then 1 else 0))) ∈ wInt X w := by
    refine Submodule.sum_mem _ fun j _ => ?_
    exact (wInt X w).smul_mem
      (⟨_, natCast_mem _ (N j i).val⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (hd j)
  have e : (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I y (u j) - (if j = i₀ then 1 else 0))) =
      (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I y (u j)) -
        (((N i₀ i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [e] at hs
  have := add_mem h hs
  convert this using 1
  abel

theorem natCast_g_mem (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ((D.host.g k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
  refine Submodule.subset_span ⟨(D.host.g k : 𝓞 X.B.I.E), ⟨_, hg, ?_⟩, ?_⟩
  · simp
  · simp

theorem one_sub_ew_mem (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) (hw : EwAt X w) : 1 - X.ew ∈ wInt X w := by
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have h1 := hA_mem_wInt X w hz (hw X.z0 hz)
  rw [hA_smul_right'] at h1
  have h2 := wInt_of_zmod X k hg X.formsAtZero.1
  have hint : 1 - X.ew ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := sub_mem (one_mem _) X.ew_int
  have h3 : (1 - X.ew) * (hA X.B.I X.z0 X.z0 + 1) ∈ wInt X w :=
    (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) h2
  have := sub_mem h3 h1
  convert this using 1
  ring

end GlobalTheory.Mem.SymChar.Resid
