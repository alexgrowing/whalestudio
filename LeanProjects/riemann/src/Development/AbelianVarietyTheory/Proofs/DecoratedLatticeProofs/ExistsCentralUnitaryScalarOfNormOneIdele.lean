import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

section Scal

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def scalGL (c c' : A) (h : c * c' = 1) : GL n A where
  val := c • (1 : Matrix n n A)
  inv := c' • (1 : Matrix n n A)
  val_inv := by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, h, one_smul]
  inv_val := by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_comm, h, one_smul]

theorem scalGL_mem (σ : A →+* A) (J : Matrix n n A) (c : A) (h : c * σ c = 1) :
    scalGL (n := n) c (σ c) h ∈ Formalism.UG.UJ σ J := by
  show Formalism.UG.cT σ (c • (1 : Matrix n n A)) * J * (c • (1 : Matrix n n A)) = J
  have hm : Formalism.UG.cT σ (c • (1 : Matrix n n A)) = σ c • (1 : Matrix n n A) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h1 : j = i
    · subst h1; simp
    · rw [if_neg h1, if_neg (Ne.symm h1)]; simp
  rw [hm, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, h, one_smul]

end Scal

variable {D : D7}

def scalGA (S : HSp D) (c : AE D) (hc : c * cA D c = 1) : GA D S :=
  ⟨scalGL c (cA D c) hc, by exact scalGL_mem _ _ c hc⟩

theorem mt_scalGA (S : HSp D) (c : AE D) (hc : c * cA D c = 1) :
    Formalism.L2.Theta.mt S (scalGA S c hc) = c • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := rfl

theorem scalGA_mem_center (S : HSp D) (c : AE D) (hc : c * cA D c = 1) :
    scalGA S c hc ∈ Subgroup.center (GA D S) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply GlobalTheory.FinPlLoc.mt_inj
  rw [GlobalTheory.FinPlLoc.mt_mul, GlobalTheory.FinPlLoc.mt_mul, mt_scalGA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul]

theorem scalGA_mem_grpAt (S : HSp D) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (hc : NormOneAt v c) :
    scalGA S c hc.1 ∈ grpAt S (· = v) := by
  unfold grpAt
  rw [GlobalTheory.FinPlLoc.mem_congGrp]
  intro i j
  rw [mt_scalGA, Matrix.smul_apply, smul_eq_mul, ← sub_one_mul]
  exact Ideal.mul_mem_right _ _ hc.2

theorem exists_cenAt_scalar : ∀ (D : D7) (S : HSp D) (v : GlobalTheory.FinPl.Pl D) (c : AE D), NormOneAt v c → ∃ z : GA D S, CenAt S v z ∧ Formalism.L2.Theta.mt S z = c • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  intro D S v c hc
  exact ⟨scalGA S c hc.1, ⟨scalGA_mem_grpAt S v c hc, scalGA_mem_center S c hc.1⟩, mt_scalGA S c hc.1⟩

end GlobalTheory.Core.Mi.LatMatch
