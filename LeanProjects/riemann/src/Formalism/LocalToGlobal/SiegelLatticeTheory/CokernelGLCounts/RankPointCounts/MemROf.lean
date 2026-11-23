import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SgnConjIntUp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityUnderRingMap.MemIntegerOfIsIntegralMap

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Split

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem comp_mem {x : (D.s.atP p).Ep} (hx : x ∈ (Z.M p).L.O) :
    (g.e x).1 ∈ 𝒪[(D.s.atP p).Fp] ∧ (g.e x).2 ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(Z.M p).L.O_def] at hx
  have h := hx.map (g.e.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])
  have h1 := h.map ((AlgHom.fst (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).restrictScalars 𝒪[(D.s.atP p).Fp])
  have h2 := h.map ((AlgHom.snd (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).restrictScalars 𝒪[(D.s.atP p).Fp])
  exact ⟨PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral h1, PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral h2⟩

theorem mem_R_of (hs : (Z.M p).split = some g) {x : (D.s.atP p).Ep}
    (h1 : (g.e x).1 ∈ 𝒪[(D.s.atP p).Fp]) (h2 : (g.e x).2 ∈ 𝒪[(D.s.atP p).Fp])
    (h3 : ∃ o ∈ 𝒪[(D.s.atP p).Fp], (g.e x).1 - (g.e x).2 = (g.q : (D.s.atP p).Fp) * o) : x ∈ (Z.M p).R := by
  unfold Formalism.MainNotions.S.Loc.Model.R
  rw [hs]
  simp only [Subring.mem_comap, Subring.mem_map]
  refine ⟨(⟨(g.e x).1, h1⟩, ⟨(g.e x).2, h2⟩), ?_, ?_⟩
  · simp only [RingHom.mem_eqLocus, RingHom.comp_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    obtain ⟨o, ho, he⟩ := h3
    refine ⟨⟨o, ho⟩, ?_⟩
    apply Subtype.ext
    show o * (g.q : (D.s.atP p).Fp) = (g.e x).1 - (g.e x).2
    rw [he, mul_comm]
  · rfl

def emap (Y : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => g.e.symm ((g.e (Y a b)).1 / (g.q : (D.s.atP p).Fp), -((g.e (Y b a)).2 / (g.q : (D.s.atP p).Fp)))

def lmat (l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => g.e.symm ((g.e (l a b)).1, (g.e (ρ b a)).2)

theorem emap_mul (l Y ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) :
    emap Z p g (l * Y * ρ) = lmat Z p g l ρ * emap Z p g Y * lmat Z p g ρ l := by
  ext a b
  apply g.e.injective
  simp only [emap, lmat, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, AlgEquiv.apply_symm_apply]
  ext
  · simp only [Prod.fst_sum, Prod.fst_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  · simp only [Prod.snd_sum, Prod.snd_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_div, neg_div,
      ← Finset.sum_neg_distrib, mul_neg, neg_mul]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_)
    ring

end Split

end Formalism.L2.SG.Pf.FibQ
