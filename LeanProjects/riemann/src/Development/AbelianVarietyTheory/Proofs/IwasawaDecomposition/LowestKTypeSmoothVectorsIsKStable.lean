import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat

noncomputable section

open Matrix
open scoped ContDiff

namespace GlobalTheory.SmoothLowKStable

open Formalism.MainNotions.S GlobalTheory.GardingVec

theorem list_prod_conj {n : ℕ} {g h : Matrix (Fin n) (Fin n) ℂ} (hgh : g * h = 1)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : l.prod * g = g * (l.map fun x => h * x * g).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc, ih]
    simp only [← Matrix.mul_assoc, hgh, Matrix.one_mul]

theorem smoothVec_apply {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hmul : ∀ g ∈ UJset ε, ∀ h ∈ UJset ε, σ (g * h) = σ g * σ h) {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ UJset ε) {v : H}
    (hv : Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v) :
    Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) (σ k v) := by
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hd
  have hk' : kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε := hk
  set g := P⁻¹ * k * P with hg
  have hPg : P * g = k * P := by rw [hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hgG : gᴴ * G * g = G := by
    calc gᴴ * G * g = (P * g)ᴴ * Formalism.REAL.Jm ε * (P * g) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * (kᴴ * Formalism.REAL.Jm ε * k) * P := by rw [hPg]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hk', h]
  have hgu : IsUnit g := by
    have : IsUnit (gᴴ * G * g).det := by rw [hgG]; exact (Matrix.isUnit_iff_isUnit_det G).1 hG
    rw [Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_of_mul_isUnit_right this)
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hgu
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgd
  have hGg : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← hgG]
    rw [Matrix.mul_assoc, hgg, Matrix.mul_one]
  have hGg' : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← hgG]
    rw [Matrix.mul_assoc gᴴ, ← Matrix.mul_assoc, ← conjTranspose_mul, hgg, conjTranspose_one, Matrix.one_mul]
  intro m Xs hX
  have hY : ∀ i, (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g) = 0 := fun i => by
    have hXi : (Xs i)ᴴ * G + G * Xs i = 0 := hX i
    calc (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g)
        = gᴴ * (Xs i)ᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * Xs i * g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * ((Xs i)ᴴ * G + G * Xs i) * g := by
          rw [hGg, hGg']; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hXi]; simp
  have hs := hv m (fun i => g⁻¹ * Xs i * g) hY
  have hmem : ∀ (Ys : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ i, (Ys i)ᴴ * G + G * Ys i = 0) → ∀ t : Fin m → ℝ,
      P * (List.ofFn fun i => NormedSpace.exp (t i • Ys i)).prod * P⁻¹ ∈ UJset ε := fun Ys hYs t => by
    refine conj_mem hP h (list_prod_mem _ fun g hg => ?_)
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_mem hG (hYs i) _
  have key : ∀ t : Fin m → ℝ,
      σ (P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) (σ k v)
        = σ k (σ (P * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod * P⁻¹) v) := fun t => by
    have e1 : (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g)))
        = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun x => g⁻¹ * x * g := by
      rw [List.map_ofFn]
      congr 1
      funext i
      rw [Function.comp_apply, ← Matrix.exp_conj' _ _ hgu, Matrix.mul_smul, Matrix.smul_mul]
    have e2 := list_prod_conj hgg (List.ofFn fun i => NormedSpace.exp (t i • Xs i))
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← hmul _ (hmem Xs hX t) _ hk,
      ← hmul _ hk _ (hmem _ hY t), e1]
    congr 2
    have e3 : P⁻¹ * k = g * P⁻¹ := by rw [hg, Matrix.mul_assoc _ P, hPP, Matrix.mul_one]
    rw [Matrix.mul_assoc _ P⁻¹, e3, ← Matrix.mul_assoc, Matrix.mul_assoc P, e2]
    simp only [← Matrix.mul_assoc, hPg]
  have := ((σ k).restrictScalars ℝ).contDiff.comp hs
  refine (funext key : _ = _) ▸ this

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isKStableOn_lowKSub_inf_sm (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (τ : D.what₂.Tau) : IsKStableOn (M.ε τ) (M.σ τ) (lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ⊓ M.sm τ) := by
  intro k hk w hw
  have hkU : k ∈ UJset (M.ε τ) := by
    show kᴴ * Formalism.REAL.Jm _ * k = Formalism.REAL.Jm _
    have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · have : lowKSub (M.ε τ) (M.lam τ) (M.σ τ)
        ≤ (lowKSub (M.ε τ) (M.lam τ) (M.σ τ)).comap (M.σ τ k : _ →ₗ[ℂ] _) :=
      sSup_le fun T hT v hv => (le_sSup hT : T ≤ _) (hT.2.1 k hk v hv)
    exact this hw.1
  · have : M.sm τ ≤ (M.sm τ).comap (M.σ τ k : _ →ₗ[ℂ] _) :=
      Submodule.span_le.2 fun v hv => Submodule.subset_span
        (smoothVec_apply (M.ds τ).2.2.1.1.2 (M.fr_unit τ) (M.fr_gram τ) hkU hv)
    exact this hw.2

end GlobalTheory.SmoothLowKStable

end
