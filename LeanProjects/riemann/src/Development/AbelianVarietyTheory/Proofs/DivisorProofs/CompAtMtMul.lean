import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace

namespace GlobalTheory.UnitaryChar

section Mat

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : ℕ}

theorem root {S A : Matrix (Fin n) (Fin n) ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hA : A.PosSemidef)
    (h : A * S * A = S) : ∃ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ R * R = A ∧ R * S * R = S := by
  obtain ⟨R, hR, hRR, hu⟩ : ∃ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ R * R = A ∧
      ∀ T : Matrix (Fin n) (Fin n) ℂ, T.PosSemidef → T * T = A → R = T :=
    ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef, CFC.sqrt_mul_sqrt_self A hA.nonneg,
      fun T hT e => CFC.sqrt_unique e hT.nonneg⟩
  have a1 : R * (R * (S * A * S)) = 1 := by
    rw [← Matrix.mul_assoc, hRR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, h1]
  have a2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (Matrix.isUnit_det_of_right_inverse a1)
  have a3 : R⁻¹ * R⁻¹ = S * A * S := by
    calc R⁻¹ * R⁻¹ = R⁻¹ * R⁻¹ * (R * (R * (S * A * S))) := by rw [a1, Matrix.mul_one]
      _ = R⁻¹ * (R⁻¹ * R) * R * (S * A * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [a2, Matrix.mul_one, a2, Matrix.one_mul]
  have a4 : R = S * R⁻¹ * S := by
    refine hu _ ?_ ?_
    · have := hR.inv.conjTranspose_mul_mul_same S
      rwa [h2] at this
    · calc S * R⁻¹ * S * (S * R⁻¹ * S) = S * (R⁻¹ * (S * S) * R⁻¹) * S := by simp only [Matrix.mul_assoc]
        _ = (S * S) * A * (S * S) := by rw [h1, Matrix.mul_one, a3, ← h1]; simp only [Matrix.mul_assoc]
        _ = A := by rw [h1, Matrix.mul_one, Matrix.one_mul]
  refine ⟨R, hR, hRR, ?_⟩
  calc R * S * R = S * R⁻¹ * S * S * R := by rw [← a4]
    _ = S * (R⁻¹ * (S * S) * R) := by simp only [Matrix.mul_assoc]
    _ = S := by rw [h1, Matrix.mul_one, a2, Matrix.mul_one]

theorem polar_std {S U : Matrix (Fin n) (Fin n) ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hU : Uᴴ * S * U = S) :
    ∃ K Q : Matrix (Fin n) (Fin n) ℂ, Kᴴ * S * K = S ∧ S * K = K * S ∧ Qᴴ * S * Q = S ∧ S * Q * S * Q = 1 ∧
      U = K * Q * Q := by
  have hS : ∀ X : Matrix (Fin n) (Fin n) ℂ, S * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have b1 : (S * Uᴴ * S) * U = 1 := by
    rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hU, h1]
  have b2 : U * S * Uᴴ = S := by
    have := congrArg (· * S) (mul_eq_one_comm.1 b1)
    simpa only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.one_mul] using this
  obtain ⟨P, hP, hPP, hPS⟩ := root h1 h2 (Matrix.posSemidef_conjTranspose_mul_self U) (by
    calc Uᴴ * U * S * (Uᴴ * U) = Uᴴ * (U * S * Uᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = S := by rw [b2, hU])
  obtain ⟨Q, hQ, hQQ, hQS⟩ := root h1 h2 hP hPS
  have hP' : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (S * (P * X)) = S * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPS]
  have c0 : (U * (S * P * S))ᴴ = S * P * S * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, h2, hP.isHermitian.eq, Matrix.mul_assoc]
  have c1 : (U * (S * P * S))ᴴ * S * (U * (S * P * S)) = S := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * S * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [hU]; simp only [Matrix.mul_assoc, hS, hP']
  have c2 : (U * (S * P * S))ᴴ * (U * (S * P * S)) = 1 := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hPP]; simp only [Matrix.mul_assoc, hS, hP', h1]
  refine ⟨U * (S * P * S), Q, c1, ?_, by rw [hQ.isHermitian.eq, hQS], ?_, ?_⟩
  · generalize U * (S * P * S) = K at c1 c2
    calc S * K = (K * Kᴴ) * S * K := by rw [mul_eq_one_comm.1 c2, Matrix.one_mul]
      _ = K * (Kᴴ * S * K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [c1]
  · rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hQS, h1]
  · rw [Matrix.mul_assoc _ Q, hQQ, Matrix.mul_assoc, Matrix.mul_assoc S, Matrix.mul_assoc S, hPS, h1, Matrix.mul_one]

theorem polar {G s u : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.IndefR.Datum.IsCartanInv G s) (hu : uᴴ * G * u = G) :
    ∃ k q : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G ∧ s * k = k * s ∧ qᴴ * G * q = G ∧ s * q * s * q = 1 ∧
      u = k * q * q := by
  obtain ⟨h1, h2, h3⟩ := h
  have hG : Gᴴ = G := by
    have e : sᴴ * Gᴴ = G * s := by rw [← Matrix.conjTranspose_mul, h3.isHermitian.eq]
    have e1 : sᴴ * sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    rw [← Matrix.one_mul Gᴴ, ← e1, Matrix.mul_assoc, e, ← Matrix.mul_assoc, h2]
  obtain ⟨B, hB, hBB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ, Bᴴ = B ∧ B * B = G * s :=
    ⟨CFC.sqrt (G * s), (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ h3.posSemidef.nonneg⟩
  have hd : IsUnit B.det := by
    have : IsUnit (B * B).det := by rw [hBB]; exact (Matrix.isUnit_iff_isUnit_det _).1 h3.isUnit
    rw [Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨C, hC, i1, i2⟩ : ∃ C : Matrix (Fin n) (Fin n) ℂ, Cᴴ = C ∧ B * C = 1 ∧ C * B = 1 :=
    ⟨B⁻¹, by rw [Matrix.conjTranspose_nonsing_inv, hB], Matrix.mul_nonsing_inv B hd, Matrix.nonsing_inv_mul B hd⟩
  have j1 : ∀ X : Matrix (Fin n) (Fin n) ℂ, B * (C * X) = X := fun X => by
    rw [← Matrix.mul_assoc, i1, Matrix.one_mul]
  have j2 : ∀ X : Matrix (Fin n) (Fin n) ℂ, C * (B * X) = X := fun X => by
    rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  obtain ⟨S, hs, hGS⟩ : ∃ S : Matrix (Fin n) (Fin n) ℂ, s = C * S * B ∧ G = B * S * B :=
    ⟨B * s * C, by simp only [Matrix.mul_assoc, j2, i2, Matrix.mul_one], by
      simp only [Matrix.mul_assoc, i2, Matrix.mul_one]
      rw [← Matrix.mul_assoc, hBB, Matrix.mul_assoc, h1, Matrix.mul_one]⟩
  have hS : S = C * G * C := by rw [hGS]; simp only [Matrix.mul_assoc, j2, i1, Matrix.mul_one]
  have s1 : S * S = 1 := by
    have := congrArg (fun X => B * X * C) h1
    simpa only [hs, Matrix.mul_assoc, j1, i1, Matrix.mul_one] using this
  have s2 : Sᴴ = S := by
    rw [hS]; simp only [Matrix.conjTranspose_mul, hC, hG, Matrix.mul_assoc]
  have tr : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * S * X = S → (C * X * B)ᴴ * G * (C * X * B) = G := fun X hX => by
    calc _ = B * (Xᴴ * S * X) * B := by
          rw [hGS]; simp only [Matrix.conjTranspose_mul, hC, hB, Matrix.mul_assoc, j1, j2]
      _ = G := by rw [hX, hGS]
  obtain ⟨K, Q, k1, k2, q1, q2, e⟩ := polar_std (U := B * u * C) s1 s2 (by
    calc _ = C * (uᴴ * (B * S * B) * u) * C := by
          simp only [Matrix.conjTranspose_mul, hC, hB, Matrix.mul_assoc]
      _ = S := by rw [← hGS, hu, ← hS])
  refine ⟨C * K * B, C * Q * B, tr K k1, ?_, tr Q q1, ?_, ?_⟩
  · have := congrArg (fun X => C * X * B) k2
    simpa only [hs, Matrix.mul_assoc, j1] using this
  · have := congrArg (fun X => C * X * B) q2
    simpa only [hs, Matrix.mul_assoc, j1, Matrix.one_mul, i2] using this
  · have := congrArg (fun X => C * X * B) e
    simpa only [Matrix.mul_assoc, j1, j2, i2, Matrix.mul_one] using this

end Mat

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem compAt_mt_mul {D : D7} (θ : InfFam D) (W : HSp D) (τ : D.what₂.Tau) (g g' : GA D W) :
    compAt θ τ (Formalism.L2.Theta.mt W (g * g')) =
      compAt θ τ (Formalism.L2.Theta.mt W g) * compAt θ τ (Formalism.L2.Theta.mt W g') :=
  Matrix.map_mul (L := Formalism.L2.Theta.mt W g) (M := Formalism.L2.Theta.mt W g') (f := (θ τ).comp (infPart D))

theorem compAt_mt_one {D : D7} (θ : InfFam D) (W : HSp D) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 :=
  Matrix.map_one (f := (θ τ).comp (infPart D)) (map_zero _) (map_one _)

theorem ext_real {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) {g g' : GA D W} (hg : g ∈ GinfC W)
    (hg' : g' ∈ GinfC W) (h : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W g) = compAt θ τ (Formalism.L2.Theta.mt W g')) :
    g = g' := by
  refine mul_inv_eq_one.1 ((GlobalTheory.UnitarySplit.real_finite_split D W).2.2.1 _ (mul_mem hg (inv_mem hg'))
    ((GlobalTheory.SmoothForms.RealPts.glue θ hθ W).1 _ fun τ => ?_))
  show compAt θ τ (Formalism.L2.Theta.mt W (g * g'⁻¹)) = 1
  rw [compAt_mt_mul, h, ← compAt_mt_mul, mul_inv_cancel, compAt_mt_one]

theorem char_eq_one : ∀ (D : D7) (θ : InfFam D) (W : HSp D), IsInfFam θ → ∀ (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) → ∀ c : GA D W → ℂ, (∀ u ∈ GinfC W, ∀ u' ∈ GinfC W, c (u * u') = c u * c u') → (∀ u ∈ GinfC W, (∀ τ, s τ * compAt θ τ (Formalism.L2.Theta.mt W u) = compAt θ τ (Formalism.L2.Theta.mt W u) * s τ) → c u = 1) → ∀ u ∈ GinfC W, c u = 1 := by
  intro D θ W hθ s hs c hm hK u hu
  have gl : ∀ x : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ τ, (x τ)ᴴ * gramAt D W τ * x τ = gramAt D W τ) →
      ∃ g ∈ GinfC W, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W g) = x τ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ W).2
  choose k q k1 k2 q1 q2 e using fun τ => polar (u := compAt θ τ (Formalism.L2.Theta.mt W u)) (hs τ)
    (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W u τ)
  obtain ⟨k', hk, ek⟩ := gl k k1
  obtain ⟨q', hq, eq⟩ := gl q q1
  obtain ⟨σ, hσ, eσ⟩ := gl s fun τ => (hs τ).2.1
  have ck : c k' = 1 := hK _ hk fun τ => by rw [ek, k2]
  have cσ : c σ = 1 := hK _ hσ fun τ => by rw [eσ]
  have c1 : c 1 = 1 := hK _ (one_mem _) fun τ => by rw [compAt_mt_one, Matrix.mul_one, Matrix.one_mul]
  have e1 : u = k' * q' * q' := ext_real hθ W hu (mul_mem (mul_mem hk hq) hq) fun τ => by
    rw [compAt_mt_mul, compAt_mt_mul, ek, eq, e]
  have e2 : σ * q' * σ * q' = 1 := ext_real hθ W (mul_mem (mul_mem (mul_mem hσ hq) hσ) hq) (one_mem _) fun τ => by
    rw [compAt_mt_mul, compAt_mt_mul, compAt_mt_mul, eσ, eq, q2, compAt_mt_one]
  rw [← e2, hm _ (mul_mem (mul_mem hσ hq) hσ) _ hq, hm _ (mul_mem hσ hq) _ hσ, hm _ hσ _ hq, cσ, one_mul,
    mul_one] at c1
  rw [e1, hm _ (mul_mem hk hq) _ hq, hm _ hk _ hq, ck, one_mul, c1]

end GlobalTheory.UnitaryChar
