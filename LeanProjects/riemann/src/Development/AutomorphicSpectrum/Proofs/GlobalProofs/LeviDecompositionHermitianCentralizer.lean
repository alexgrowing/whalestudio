import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLevi
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.RealPtExHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanUnitaryElementLiftStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryElementPrescribedBlocksStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExtendByZeroApplyOfNeStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsOrthogonalHermitianSubspaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

theorem eichler_frame : ∀ {n m : ℕ} (ε : Fin n → Bool) (G Q : Matrix (Fin n) (Fin n) ℂ) (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m)),
    IsUnit Q → Qᴴ * Formalism.REAL.Jm ε * Q = G → xᴴ * G * x = 0 → xᴴ * G * y = 1 →
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * G ∈ Formalism.QuantumDeterminants.UH G ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => y j i)),
        Formalism.REAL.Jm ε *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => y j i)) := by
  intro n m ε G Q x y A hQ hG hxx hxy
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hd
  have h2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hd
  have ex : ∀ z : Matrix (Fin n) (Fin m) ℂ, xᴴ * G * z = (Q * x)ᴴ * Formalism.REAL.Jm ε * (Q * z) := fun z => by
    rw [← hG, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  obtain ⟨u, w, hu, hw, hux, hN, hJ⟩ := GlobalTheory.T.unitary_element_prescribed_blocks ε (Q * x) (Q * y) A (by rw [← ex, hxx]) (by rw [← ex, hxy])
  refine ⟨u * Q, Q⁻¹ * w, fun i v hi => ?_, fun v i hi => ?_, fun i j hj => ?_, ?_⟩
  · simp [Matrix.mul_apply, hu i _ hi]
  · simp [Matrix.mul_apply, hw _ i hi]
  · rw [Matrix.mul_assoc]; exact hux i j hj
  have key : Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G) = (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) * Q := by
    rw [← hG, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q⁻¹, h1, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · show _ = _
    have e : (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)ᴴ * G * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G) =
        (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G))ᴴ * Formalism.REAL.Jm ε * (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)) := by
      rw [← hG, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e, key, Matrix.conjTranspose_mul]
    have hN' : _ = _ := hN
    calc Qᴴ * (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * ((1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) * Q)
        = Qᴴ * ((1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)) * Q := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hN', ← hG, Matrix.mul_assoc]
  · have cx : ∀ z : Matrix (Fin n) (Fin m) ℂ, ∀ i : A, (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)) *ᵥ (fun j => z j i) =
        (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => (Q * z) j i := fun z i => by
      rw [key, ← Matrix.mulVec_mulVec]
      congr 1
    simp only [cx]
    exact hJ

theorem iwasawa_adapted : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (b : GA D V), ∃ n ∈ unip D.sp.cm.sig V.gram X T, ∃ mm ∈ levi D.sp.cm.sig V.gram X Y T, ∃ b₀ : GA D V, b = n * mm * b₀ ∧ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) := by
  intro D θ hθ V ε fr hfr m X Y hW T b
  classical
  have hQ := isFrameFam_mul_infMat_inv D θ hθ V ε fr hfr b
  let Q : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹
  let x : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ := fun τ => X.map (tauE D τ)
  let y : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ := fun τ => Y.map (tauE D τ)
  have hmap : ∀ τ (Z Z' : Matrix (Fin V.rank) (Fin m) D.host.E), (Z.map (tauE D τ))ᴴ * gramAt D V τ * Z'.map (tauE D τ) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * V.gram * Z').map (tauE D τ) := by
    intro τ Z Z'
    have e : (Z.map (tauE D τ))ᴴ = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z).map (tauE D τ) := by
      ext i j
      simp [Formalism.UG.cT, GlobalTheory.Mem.Isom.tauE_sig]
    rw [e, gramAt, Matrix.map_mul, Matrix.map_mul]
  have hxx : ∀ τ, (x τ)ᴴ * gramAt D V τ * x τ = 0 := fun τ => by
    rw [hmap, hW.xx]; exact Matrix.map_zero _ (map_zero _)
  have hxy : ∀ τ, (x τ)ᴴ * gramAt D V τ * y τ = 1 := fun τ => by
    rw [hmap, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
  choose u w hu hw hux hN hJ using fun τ =>
    eichler_frame (ε τ) (gramAt D V τ) (Q τ) (x τ) (y τ) (upTo T) (hQ τ).1 (hQ τ).2 (hxx τ) (hxy τ)
  obtain ⟨g, hg, U, W, hU, hW', hUX, hgM⟩ := GlobalTheory.T.archimedean_unitary_element_lift D θ hθ V X u w hN
  have hgu : g ∈ unip D.sp.cm.sig V.gram X T :=
    GlobalTheory.T.unitary_adelic_unipotent_lift D.sp.cm.sig V.gram X T g U W hW.xx (fun i v hi => hU i v fun τ => hu τ i v hi)
      (fun v i hi => hW' v i fun τ => hw τ v i hi) (fun i j hj => hUX i j fun τ => hux τ i j hj) hgM
  refine ⟨g, hgu, 1, one_mem _, g⁻¹ * b, by rw [mul_one, mul_inv_cancel_left], fun τ => ?_⟩
  have e1 : (infMat D.sp.cm.sig V.gram (θ τ) (g⁻¹ * b))⁻¹ =
      (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) g := by
    rw [Formalism.L2.Fam.ThC.infMat_mul, Matrix.mul_inv_rev]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Formalism.L2.Fam.ThC.infMat_mul, mul_inv_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have e2 : fr τ * (infMat D.sp.cm.sig V.gram (θ τ) (g⁻¹ * b))⁻¹ =
      fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ * (1 + x τ * u τ + w τ * (x τ)ᴴ * gramAt D V τ) := by
    rw [e1, hg τ, ← Matrix.mul_assoc]
  obtain ⟨k, S, hk⟩ := GlobalTheory.T.involution_stable_subspace_coordinate (ε τ) _ (hJ τ)
  refine ⟨k, S, ?_⟩
  beta_reduce
  rw [e2]
  exact hk

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
