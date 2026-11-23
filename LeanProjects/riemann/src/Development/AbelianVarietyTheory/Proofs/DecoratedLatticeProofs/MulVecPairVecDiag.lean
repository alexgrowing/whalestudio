import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.Dich

open Matrix

section Mat

variable {A B : Type} [CommRing A] [CommRing B] {n : ℕ}

def diagSnd (M : Matrix (Fin (n + n)) (Fin (n + n)) A) : Matrix (Fin n) (Fin n) A :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ + (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

theorem mulVec_pairVec_diag (M : Matrix (Fin (n + n)) (Fin (n + n)) A) (x : Fin n → A) :
    M *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv (leviMat finSumFinEquiv M *ᵥ x) (diagSnd M *ᵥ x) := by
  rw [mulVec_pairVec, leviMat, diagSnd, add_mulVec, add_mulVec]

theorem diagSnd_map (f : A →+* B) (M : Matrix (Fin (n + n)) (Fin (n + n)) A) :
    diagSnd (M.map f) = (diagSnd M).map f := by
  ext i j; simp [diagSnd, toBlocks₂₁, toBlocks₂₂]

theorem isotropic_diag {σ : A →+* A} {J : Matrix (Fin n) (Fin n) A} {M : Matrix (Fin (n + n)) (Fin (n + n)) A}
    (hM : Formalism.UG.cT σ M * dblGram finSumFinEquiv J * M = dblGram finSumFinEquiv J) :
    Formalism.UG.cT σ (leviMat finSumFinEquiv M) * J * leviMat finSumFinEquiv M =
      Formalism.UG.cT σ (diagSnd M) * J * diagSnd M := by
  have h1 : Formalism.UG.cT σ (M.submatrix finSumFinEquiv finSumFinEquiv) * fromBlocks J 0 0 (-J) *
      M.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks J 0 0 (-J) := by
    rw [← submatrix_blkMat finSumFinEquiv,
      show Formalism.UG.cT σ (M.submatrix finSumFinEquiv finSumFinEquiv) =
        (Formalism.UG.cT σ M).submatrix finSumFinEquiv finSumFinEquiv from rfl, submatrix_mul_equiv, submatrix_mul_equiv]
    exact congrArg (fun X => X.submatrix finSumFinEquiv finSumFinEquiv) hM
  rw [← fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)] at h1
  simp only [Formalism.UG.cT, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, fromBlocks_inj] at h1
  obtain ⟨h11, h12, h21, h22⟩ := h1
  simp only [Formalism.UG.cT, leviMat, diagSnd, Matrix.map_add _ (map_add σ), transpose_add, Matrix.add_mul, Matrix.mul_add]
  set a := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
  set b := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂
  set c := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁
  set d := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂
  rw [← sub_eq_zero]
  have := congrArg₂ (fun a b => a + b) (congrArg₂ (fun a b => a + b) h11 h12) (congrArg₂ (fun a b => a + b) h21 h22)
  simp only [add_zero, add_neg_cancel] at this
  rw [← sub_eq_zero] at this
  rw [← this]
  abel

end Mat

section Rat

open Formalism.BasicNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_rat (W : HSp D) {γ : GA D W} (hγ : γ ∈ GQ W) :
    ∃ g : GL (Fin W.rank) D.host.E, g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram ∧
      (matHom W γ).1 = g.1.map (incA D) ∧ (matHom W γ⁻¹).1 = (g⁻¹).1.map (incA D) := by
  obtain ⟨g, hg, e⟩ := hγ
  have e' : matHom W γ = Formalism.UG.bc (incA D) g := e.symm
  refine ⟨g, hg, congrArg Units.val e', ?_⟩
  rw [map_inv, e', ← map_inv]
  rfl

theorem exists_of_rat (W : HSp D) {g : GL (Fin W.rank) D.host.E}
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    ∃ δ ∈ GQ W, (matHom W δ).1 = g.1.map (incA D) := by
  have hm : Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
    have hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E)).map (incA D) := by
      ext i j; simp [Formalism.UG.cT, sigR, inclR]
    have hg' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) * W.gram *
        (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) *
      W.gram.map (incA D) * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) = W.gram.map (incA D)
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']
  exact ⟨⟨_, hm⟩, ⟨g, hg, rfl⟩, rfl⟩

end Rat

end GlobalTheory.Core.Rk.Dich
