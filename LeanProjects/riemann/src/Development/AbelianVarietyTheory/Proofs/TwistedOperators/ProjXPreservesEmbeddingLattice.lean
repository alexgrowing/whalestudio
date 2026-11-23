import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory

theorem projX_embedding_lattice : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e * d.qX) *ᵥ v ∈ a.lat Λ 𝔟 := by
  intro D A B B₀ c ρ a d hA Λ 𝔟 v hv
  obtain ⟨hc, he, s, he'⟩ := hA
  obtain ⟨y, hy, u, hu, rfl⟩ := hv
  have hGh : B.gramᴴ = B.gram := GlobalTheory.MixModel.gram_conjTranspose B
  have hperp : (frameMat B A a.ι)ᴴ * B.gram * a.a = 0 := a.perp
  have hgram : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  set N : Matrix (Fin c) (Fin c) D.host.E := antiDiagonalSignGramMatrix c (-1) with hN
  have hK : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have := congrArg Matrix.conjTranspose hperp
    simpa [Matrix.conjTranspose_mul, hGh, Matrix.mul_assoc] using this
  have hρc : ρ ≤ c := by omega
  let P : Matrix (Fin c) (Fin ρ) D.host.E := fun q p => if q = (Fin.castLE hρc p).rev then s p else 0
  let Q : Matrix (Fin c) (Fin ρ) D.host.E := fun q p => if q = Fin.castLE hρc p then (-D.host.xi0) ^ (p.1 + 1) else 0
  have heP : d.e' = a.a * P := by
    rw [he']; ext i p; rw [Matrix.mul_apply]; simp [colsOf, P, mul_comm]
  have heQ : d.e = a.a * Q := by
    rw [he]; ext i p; rw [Matrix.mul_apply]; simp [colsOf, Q, mul_comm]
  have hPN : ∀ p q, (Pᴴ * N) p q = if q = Fin.castLE hρc p then star (s p) else 0 := by
    intro p q
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    simp only [P, apply_ite star, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := p.2; have := q.2
    simp only [hN, antiDiagonalSignGramMatrix, Fin.ext_iff, Fin.val_rev, Fin.val_castLE]
    split_ifs <;> first | (exfalso; omega) | ring
  have hdiag : ∀ p : Fin ρ, star (s p) * (-D.host.xi0) ^ (p.1 + 1) = 1 := by
    intro p
    have h1 := d.e'e
    rw [heP, heQ, Matrix.conjTranspose_mul] at h1
    have h2 : Pᴴ * a.aᴴ * B.gram * (a.a * Q) = Pᴴ * N * Q := by
      rw [← hgram]; simp only [Matrix.mul_assoc]
    rw [h2] at h1
    have h3 := congrFun (congrFun h1 p) p
    rw [Matrix.mul_apply] at h3
    simp only [hPN, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Q, Matrix.one_apply_eq] at h3
    simpa using h3
  have hqX : d.qX = Pᴴ * a.aᴴ * B.gram := by
    rw [HypDec.qX, heP, Matrix.conjTranspose_mul]
  have ht : d.qX *ᵥ (frameMat B A a.ι *ᵥ y + a.a *ᵥ u) = (Pᴴ * N) *ᵥ u := by
    have h1 : Pᴴ * a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
      calc _ = Pᴴ * (a.aᴴ * B.gram * frameMat B A a.ι) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hK, Matrix.mul_zero]
    have h2 : Pᴴ * a.aᴴ * B.gram * a.a = Pᴴ * N := by
      rw [← hgram]; simp only [Matrix.mul_assoc]
    rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hqX, h1, h2, zero_mulVec, zero_add]
  have hu' : ∀ q : Fin c, (Q *ᵥ ((Pᴴ * N) *ᵥ u)) q = if q.1 < ρ then u q else 0 := by
    intro q
    simp only [mulVec, dotProduct, hPN, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Q]
    split_ifs with hq
    · rw [Finset.sum_eq_single ⟨q.1, hq⟩]
      · have e1 : q = Fin.castLE hρc ⟨q.1, hq⟩ := Fin.ext rfl
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [← mul_assoc, mul_comm ((-D.host.xi0) ^ _), hdiag, one_mul, if_pos e1, ← e1]
      · intro b _ hb
        rw [if_neg]
        intro e; apply hb; ext; simp only [Fin.ext_iff, Fin.val_castLE, Fin.val_mk] at e ⊢; omega
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro e; apply hq; rw [e]; simp
  refine ⟨0, Λ.zero_mem, Q *ᵥ ((Pᴴ * N) *ᵥ u), fun q => ?_, ?_⟩
  · rw [hu']; split_ifs
    · exact hu q
    · exact (𝔟 q).val.zero_mem
  · rw [mulVec_zero, zero_add, ← mulVec_mulVec, ht, heQ, ← mulVec_mulVec]

end GlobalTheory
