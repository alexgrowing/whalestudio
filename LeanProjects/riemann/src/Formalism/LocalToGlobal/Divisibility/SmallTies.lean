import Mathlib
import Formalism.LocalToGlobal.Divisibility.LinkDef
import Formalism.LocalToGlobal.Divisibility.ConstantGeTwentyEight
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.LocalToGlobal.GlobalTheory.FamRowsP
import Formalism.LocalRingCardinality.DataParams₂

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions

section Weights

variable {D : D7}

theorem lw_plEq (w : D.what₂.places.Pl) : SizeData₂.lwP w = Formalism.DivisionValues.lw (D.plEq w) := by
  rfl

theorem ramw_plEq (w : D.what₂.places.Pl) : ((D.what₂.places.ramIdx w : ℕ) : ℝ) = ((ramw (D.plEq w) : ℤ) : ℝ) := by
  rw [← lf_eW_eq_ramw, D.ram_eq w, Int.cast_natCast]
  rfl

end Weights

section Fo

variable {D : D7} {Bs : DefBase D.what₂.LL} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}

def FTie (L : SizeData₂ D) (N : IndefNum Bs) (eJ : Bs.J ≃ Fin D.R.m) : Prop :=
  ∀ y j, N.F0 y j = L.F ((eJ j).1 + 1) (D.plEq.symm y)

theorem fTie_num_iff (L : SizeData₂ D) (Z : IndefScale Bs) (C CH : ℝ) (eJ : Bs.J ≃ Fin D.R.m) :
    FTie L (Z.num C CH) eJ ↔ ∀ y j, Z.F0 y j = L.F ((eJ j).1 + 1) (D.plEq.symm y) := Iff.rfl

theorem sum_lifts_eJ (eJ : Bs.J ≃ Fin D.R.m) (f : ℕ → ℝ) :
    ∑ j ∈ SizeData₂.lifts D, f j = ∑ j : Bs.J, f ((eJ j).1 + 1) := by
  rw [Equiv.sum_comp eJ (fun i : Fin D.R.m => f (i.1 + 1)), Fin.sum_univ_eq_sum_range (fun i => f (i + 1)),
    Finset.range_eq_Ico, Finset.sum_Ico_add']
  unfold SizeData₂.lifts
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

theorem two_sumTw_eq_Fo (L : SizeData₂ D) (S0 : IndefSide Df0 N) (hU : S0.toIndefData.Untwisted N) (eJ : Bs.J ≃ Fin D.R.m)
    (hF : FTie L N eJ) :
    2 * (∑ j, ∑ y ∈ S0.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)) = L.Fo := by
  classical
  have hF' : ∀ y j, N.F0 y j = L.F ((eJ j).1 + 1) (D.plEq.symm y) := hF
  unfold SizeData₂.Fo
  rw [sum_lifts_eJ eJ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∑ y ∈ S0.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)
      = ∑ y ∈ S0.Tw ∪ L.supp.map D.plEq.toEmbedding, lw y * ((ramw y : ℝ) * N.F0 y j) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro y _ hy
    rw [(hU y hy j).2, mul_zero, mul_zero]
  have h2 : ∑ y ∈ L.supp.map D.plEq.toEmbedding, 2 * (lw y * ((ramw y : ℝ) * N.F0 y j))
      = ∑ y ∈ S0.Tw ∪ L.supp.map D.plEq.toEmbedding, 2 * (lw y * ((ramw y : ℝ) * N.F0 y j)) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro y _ hy'
    have hw : D.plEq.symm y ∉ L.supp := by
      intro hw
      apply hy'
      rw [Finset.mem_map]
      exact ⟨_, hw, by simp⟩
    rw [hF', L.F_supp _ _ hw, mul_zero, mul_zero, mul_zero]
  have h3 : ∑ w ∈ L.supp, SizeData₂.sz w (L.F ((eJ j).1 + 1) w)
      = ∑ y ∈ L.supp.map D.plEq.toEmbedding, 2 * (lw y * ((ramw y : ℝ) * N.F0 y j)) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Equiv.coe_toEmbedding]
    rw [hF', Equiv.symm_apply_apply, SizeData₂.sz, lw_plEq, ramw_plEq]
    ring
  rw [h1, h3, h2, Finset.mul_sum]

theorem two_FoOf_eq_Fo (L : SizeData₂ D) (P : IndefCore Df0 Df1 Dc Sp N) (eJ : Bs.J ≃ Fin D.R.m) (hF : FTie L N eJ) :
    2 * FoOf P = L.Fo := by
  unfold FoOf
  exact two_sumTw_eq_Fo L P.base P.extra.untw eJ hF

theorem two_FoOfR_eq_Fo (L : SizeData₂ D) (P : IndefCoreR Df0 Df1 Dc Sp N) (eJ : Bs.J ≃ Fin D.R.m) (hF : FTie L N eJ) :
    2 * FoOfR P = L.Fo := by
  unfold FoOfR
  exact two_sumTw_eq_Fo L P.base P.extra.untw eJ hF

theorem foTie_pkg {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (L : SizeData₂ D) (A : FamIn D.what₂.LL G Pl0 T m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (Cp CHp : ℝ)
    (Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) Cp CHp) (eJ : A.fam.base.J ≃ Fin D.R.m)
    (hF : FTie L ((Zsc Pk.Zs).num Cp CHp) eJ) : 2 * FoOf Pk.core = L.Fo := two_FoOf_eq_Fo L Pk.core eJ hF

theorem foTie_pkgR {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (L : SizeData₂ D) (A : FamIn D.what₂.LL G Pl0 T m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (cf : ConvFace A.fam.base) (Cp CHp : ℝ)
    (Pk : IndefPkgR A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cf Cp CHp) (eJ : A.fam.base.J ≃ Fin D.R.m)
    (hF : FTie L ((Zsc Pk.Zs).num Cp CHp) eJ) : 2 * FoOfR Pk.core = L.Fo := two_FoOfR_eq_Fo L Pk.core eJ hF

end Fo

section Sg

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

theorem sg_fin_sgD (C : Formalism.L2.Col.ColObj K I) (u : I) :
    (Function.support (shiftZ (Formalism.L2.GlobalTheoryTheory.FamRows.sgD C u))).Finite := Formalism.L2.GlobalTheoryTheory.FamRows.flD_support_finite C u

end Sg

section Mu1

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

theorem package_column_tuple_eq (A : FamIn D.what₂.LL G Pl0 T m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (Cp CHp : ℝ)
    (Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) Cp CHp) :
    Pk.core.cols.toIndefData.μ = Pk.core.base.toIndefData.μ := column_tuple_of_level_link Pk.core.extra.level

theorem package_column_tuple_eq_of_conventions (A : FamIn D.what₂.LL G Pl0 T m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (cf : ConvFace A.fam.base) (Cp CHp : ℝ)
    (Pk : IndefPkgR A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cf Cp CHp) :
    Pk.core.cols.toIndefData.μ = Pk.core.base.toIndefData.μ := column_tuple_of_level_link Pk.core.extra.level

end Mu1

end Formalism.L2.DIV

end
