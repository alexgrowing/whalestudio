import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlLastRowEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicBetaSurjective

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirSeq

section Alg

variable {k : Type} [Field k]

theorem mul_colMat_of_mem {n : ℕ} (h : GL (Fin (n + 1)) k) (hh : h ∈ Mir k n) (v : Fin n → k) :
    (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * colMat k n v =
      colMat k n ((blockMat k n (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).mulVec v) := by
  have hl := (mem_Mir_iff k h).1 hh
  ext i j
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases with
    | last =>
      have e : ∀ l : Fin n, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.castSucc l) = 0 := by
        intro l
        rw [hl]
        simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
      simp [colMat, mul_apply, Fin.sum_univ_castSucc, e]
    | cast i =>
      simp [colMat, mul_apply, Fin.sum_univ_castSucc, mulVec, dotProduct, blockMat]
  · simp [colMat, mul_apply, hj]

theorem colMat_mul_of_mem {n : ℕ} (h : GL (Fin (n + 1)) k) (hh : h ∈ Mir k n) (w : Fin n → k) :
    colMat k n w * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = colMat k n w := by
  have hl := (mem_Mir_iff k h).1 hh
  ext i j
  have e : (colMat k n w * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) i j =
      colMat k n w i (Fin.last n) * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j := by
    rw [mul_apply, Finset.sum_eq_single (Fin.last n)]
    · intro l _ hlne
      simp [colMat, hlne]
    · simp
  rw [e, hl]
  by_cases hj : j = Fin.last n
  · subst hj
    simp [colMat, eLast]
  · simp [colMat, eLast, hj]

theorem conj_mem_MirUin {n : ℕ} (h : Mir k n) (u : MirUin k n) : h * (u : Mir k n) * h⁻¹ ∈ MirUin k n := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  show (h : GL (Fin (n + 1)) k) * ((u : Mir k n) : GL (Fin (n + 1)) k) * (h : GL (Fin (n + 1)) k)⁻¹ ∈ MirU k n
  rw [hv']
  refine ⟨Multiplicative.ofAdd ((blockMat k n ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).mulVec
    v.toAdd), ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  ext1
  rw [Units.val_mul, Units.val_mul]
  show (1 + colMat k n _) * _ = _ * (1 + colMat k n v.toAdd)
  rw [add_mul, mul_add, one_mul, mul_one, colMat_mul_of_mem _ h.2, mul_colMat_of_mem _ h.2]
  simp

end Alg

section Seq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cInd_ext {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    {H : Subgroup G} {σ : Representation ℂ H W} {F F' : cIndSpace H σ} (h : ∀ g, F.1.1.1 g = F'.1.1.1 g) : F = F' :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

section Beta

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle) {n : ℕ}
  (τ : Representation ℂ (Mir k (n + 1)) V)

theorem betaFun_add (a b : V) (g : Mir k (n + 1)) :
    betaFun ψ τ (a + b) g = betaFun ψ τ a g + betaFun ψ τ b g := by
  simp only [betaFun, map_add, Submodule.Quotient.mk_add]

theorem betaFun_smul (c : ℂ) (a : V) (g : Mir k (n + 1)) :
    betaFun ψ τ (c • a) g = c • betaFun ψ τ a g := by
  simp only [betaFun, map_smul, Submodule.Quotient.mk_smul]

end Beta

variable (hI : BetaInd k) (hS : BetaSmooth k) (hC : BetaCompact k)

include hI hS in
theorem betaFun_mem_smooth (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V) (hτ : IsSmooth τ) (v : V) :
    (⟨betaFun ψ τ v, hI ψ n V τ v⟩ : indSpace (Q k n) (qRep k ψ (phiMinus k ψ τ))) ∈
      smoothPart (ind (Q k n) (qRep k ψ (phiMinus k ψ τ))) := by
  have e : {g : Mir k (n + 1) | ind (Q k n) (qRep k ψ (phiMinus k ψ τ)) g ⟨betaFun ψ τ v, hI ψ n V τ v⟩ =
      ⟨betaFun ψ τ v, hI ψ n V τ v⟩} = {g | ∀ x, betaFun ψ τ v (x * g) = betaFun ψ τ v x} := by
    ext g
    exact Subtype.ext_iff.trans funext_iff
  show IsOpen {g : Mir k (n + 1) | ind (Q k n) (qRep k ψ (phiMinus k ψ τ)) g ⟨betaFun ψ τ v, hI ψ n V τ v⟩ =
      ⟨betaFun ψ τ v, hI ψ n V τ v⟩}
  rw [e]
  exact hS ψ n V τ hτ v

def betaMap (ψ : AddChar k Circle) (hc : Continuous ψ) (hne : ψ ≠ 1) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V) (hτ : IsSmooth τ) :
    twKer τ (MirUin k (n + 1)) 1 →ₗ[ℂ] cIndSpace (Q k n) (qRep k ψ (phiMinus k ψ τ)) where
  toFun v := ⟨⟨⟨betaFun ψ τ v, hI ψ n V τ v⟩, betaFun_mem_smooth hI hS ψ τ hτ v⟩, hC ψ hc hne n V τ hτ v v.2⟩
  map_add' a b := cInd_ext fun g => betaFun_add ψ τ (a : V) (b : V) g
  map_smul' c a := cInd_ext fun g => betaFun_smul ψ τ c (a : V) g

end Seq

end GlobalTheory.CompanionTheory.BZMirSeq

end
