import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecPairVecDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFrameStabiliserNormalisesUnipotentRadica
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

noncomputable section
namespace GlobalTheory.FrameNorm

open Formalism.L2.Theta (mt)

local infixl:70 " ⋆ₘ " => HMul.hMul

set_option maxHeartbeats 1600000 in

theorem norm : ∀ (D : D7) (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), ∀ δ ∈ GQ V,
    ∀ δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, (matHom V δ).1 = δ₀.map (incA D) →
    ∀ G : Matrix (Fin r) (Fin r) D.host.E, IsUnit G → δ₀ * C = C * G → ∀ n ∈ NI V C, δ * n * δ⁻¹ ∈ NI V C := by
  intro D V r C δ hδ δ₀ hδ₀ G hG hC
  obtain ⟨g, hg, e1, e2⟩ := exists_rat V hδ
  have hg0 : (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = δ₀ := by
    apply Matrix.map_injective (GlobalTheory.FrameStab.incA_injective D)
    exact e1.symm.trans hδ₀
  obtain ⟨σ, hσ⟩ : ∃ σ : D.host.E →+* D.host.E, σ = (D.sp.cm.sig : D.host.E →+* D.host.E) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = V.gram := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin r) (Fin V.rank) D.host.E, P = Formalism.UG.cT σ C * J := ⟨_, rfl⟩
  obtain ⟨δi, hδi⟩ : ∃ δi : Matrix (Fin V.rank) (Fin V.rank) D.host.E, δi = (g⁻¹ : GL (Fin V.rank) D.host.E).1 :=
    ⟨_, rfl⟩
  have hδδi : δ₀ * δi = 1 := by rw [← hg0, hδi]; exact Units.mul_inv g
  have hδiδ : δi * δ₀ = 1 := by rw [← hg0, hδi]; exact Units.inv_mul g
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hGGi : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hdet
  have hGiG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  have hU : Formalism.UG.cT σ δ₀ * J * δ₀ = J := by rw [← hg0, hσ, hJ]; exact hg
  have hiC : δi * C = C * G⁻¹ := by
    calc δi * C = δi * (C * G * G⁻¹) := by rw [Matrix.mul_assoc C, hGGi, Matrix.mul_one]
      _ = δi * (δ₀ * C) * G⁻¹ := by rw [← hC]; simp only [Matrix.mul_assoc]
      _ = C * G⁻¹ := by rw [← Matrix.mul_assoc δi, hδiδ, Matrix.one_mul]
  have hc1 : Formalism.UG.cT σ δi * Formalism.UG.cT σ δ₀ = 1 := by
    rw [← Formalism.UG.cT_mul, hδδi]; simp [Formalism.UG.cT]
  have hcG : Formalism.UG.cT σ G * Formalism.UG.cT σ G⁻¹ = 1 := by
    rw [← Formalism.UG.cT_mul, hGiG]; simp [Formalism.UG.cT]
  have hJδ : J * δ₀ = Formalism.UG.cT σ δi * J := by
    calc J * δ₀ = Formalism.UG.cT σ δi * Formalism.UG.cT σ δ₀ * J * δ₀ := by rw [hc1, Matrix.one_mul]
      _ = Formalism.UG.cT σ δi * (Formalism.UG.cT σ δ₀ * J * δ₀) := by simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ δi * J := by rw [hU]
  have hPδ : P * δ₀ = Formalism.UG.cT σ G⁻¹ * P := by
    calc P * δ₀ = Formalism.UG.cT σ C * (J * δ₀) := by rw [hP, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ (δi * C) * J := by rw [hJδ, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ G⁻¹ * P := by rw [hiC, Formalism.UG.cT_mul, hP, Matrix.mul_assoc]
  have hPδi : P * δi = Formalism.UG.cT σ G * P := by
    calc P * δi = Formalism.UG.cT σ G * Formalism.UG.cT σ G⁻¹ * P * δi := by rw [hcG, Matrix.one_mul]
      _ = Formalism.UG.cT σ G * (P * δ₀) * δi := by rw [hPδ]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ G * P := by simp only [Matrix.mul_assoc, hδδi, Matrix.mul_one]

  have hΔ : mt V δ = δ₀.map (incA D) := hδ₀
  have hΔi : mt V δ⁻¹ = δi.map (incA D) := by rw [hδi]; exact e2
  have hΓiL : mt V δ⁻¹ ⋆ₘ C.map (incA D) = C.map (incA D) ⋆ₘ (G⁻¹).map (incA D) := by
    rw [hΔi, ← Matrix.map_mul, hiC, Matrix.map_mul]
  have hPΓ : P.map (incA D) ⋆ₘ mt V δ = (Formalism.UG.cT σ G⁻¹).map (incA D) ⋆ₘ P.map (incA D) := by
    rw [hΔ, ← Matrix.map_mul, hPδ, Matrix.map_mul]
  have key : NI V C ≤ (NI V C).comap (MulAut.conj δ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun m hm => ?_
    have h1 : (mt V m - 1) ⋆ₘ C.map (incA D) = 0 := hm.1
    have h2 : P.map (incA D) ⋆ₘ (mt V m - 1) = 0 := by
      have := hm.2.1
      rw [hP, hσ, hJ]; exact this
    have h3 : ∀ x : Fin V.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin r → AE D,
        (mt V m - 1) *ᵥ (fun i => incA D (x i)) = C.map (incA D) *ᵥ a := by
      rw [hP, hσ, hJ]; exact hm.2.2
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨?_, ?_, ?_⟩
    · show (mt V (δ * m * δ⁻¹) - 1) ⋆ₘ C.map (incA D) = 0
      rw [GlobalTheory.FrameStab.mt_conj_sub_one]
      simp only [Matrix.mul_assoc]
      rw [hΓiL, ← Matrix.mul_assoc (mt V m - 1), h1, Matrix.zero_mul, Matrix.mul_zero]
    · have c2 : P.map (incA D) ⋆ₘ (mt V (δ * m * δ⁻¹) - 1) = 0 := by
        rw [GlobalTheory.FrameStab.mt_conj_sub_one]
        simp only [← Matrix.mul_assoc]
        rw [hPΓ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (P.map (incA D)) (mt V m - 1), h2, Matrix.zero_mul, Matrix.mul_zero]
      rw [hP, hσ, hJ] at c2; exact c2
    · intro x hx
      rw [← hJ, ← hσ, ← hP] at hx
      have hy : P *ᵥ (δi *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, hPδi, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      obtain ⟨a, ha⟩ := h3 _ hy
      refine ⟨G.map (incA D) *ᵥ a, ?_⟩
      have hxi : mt V δ⁻¹ *ᵥ (fun i => incA D (x i)) = fun i => incA D ((δi *ᵥ x) i) := by
        rw [hΔi]; funext i; exact (RingHom.map_mulVec (incA D) δi x i).symm
      show (mt V (δ * m * δ⁻¹) - 1) *ᵥ (fun i => incA D (x i)) = C.map (incA D) *ᵥ (G.map (incA D) *ᵥ a)
      rw [GlobalTheory.FrameStab.mt_conj_sub_one, ← Matrix.mulVec_mulVec, hxi, ← Matrix.mulVec_mulVec, ha,
        Matrix.mulVec_mulVec, hΔ, ← Matrix.map_mul, hC, Matrix.map_mul, Matrix.mulVec_mulVec]
  intro n hn
  exact key hn

end GlobalTheory.FrameNorm
