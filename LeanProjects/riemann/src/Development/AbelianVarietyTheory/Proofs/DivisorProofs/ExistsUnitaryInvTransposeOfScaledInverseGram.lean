import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLEpsPairMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SiegelThetaInvT

private theorem invTranspose_abstract {E A n : Type} [Field E] [CommRing A] [Fintype n] [DecidableEq n]
    (ι : E →+* A) (c : A →+* A) (G J : Matrix n n E) (hG : G.det ≠ 0) (x : E) (hx : x ≠ 0) (ξ : A)
    (hξ : ξ • J.map ι = (x • G⁻¹).map ι) (M N : Matrix n n A) (hMN : M * N = 1) (hNM : N * M = 1)
    (hb : Mᵀ * J.map ι * M.map c = J.map ι) :
    (Nᵀ.map c)ᵀ * G.map ι * Nᵀ = G.map ι := by
  have hdet : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have hKG : G⁻¹.map ι * G.map ι = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hGK : G.map ι * G⁻¹.map ι = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hsm : (x • G⁻¹).map ι = ι x • G⁻¹.map ι := by
    ext i j
    simp [smul_eq_mul, map_mul]
  have hd : ι x⁻¹ * ι x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  generalize G⁻¹.map ι = K at hKG hGK hsm
  generalize G.map ι = G' at hKG hGK ⊢
  have h1 : ι x • (Mᵀ * K * M.map c) = ι x • K := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← hsm, ← hξ, Matrix.mul_smul, Matrix.smul_mul, hb]
  have h2 : Mᵀ * K * M.map c = K := by
    have := congrArg (fun X => ι x⁻¹ • X) h1
    simpa only [smul_smul, hd, one_smul] using this
  have hcNM : N.map c * M.map c = 1 := by
    rw [← Matrix.map_mul, hNM]
    exact Matrix.map_one _ (map_zero c) (map_one c)
  have hX : N.map c * G' * Nᵀ * K = 1 := by
    calc N.map c * G' * Nᵀ * K = N.map c * G' * Nᵀ * (Mᵀ * K * M.map c) := by rw [h2]
      _ = N.map c * G' * ((M * N)ᵀ * K) * M.map c := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = N.map c * M.map c := by
          rw [hMN, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_assoc (N.map c), hGK, Matrix.mul_one]
      _ = 1 := hcNM
  have hT : (Nᵀ.map c)ᵀ = N.map c := rfl
  rw [hT]
  calc N.map c * G' * Nᵀ = N.map c * G' * Nᵀ * (K * G') := by rw [hKG, Matrix.mul_one]
    _ = G' := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]

private def invT {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] (m : GL n A) : GL n A :=
  ⟨(m⁻¹).1ᵀ, m.1ᵀ, by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

private theorem sigR_eq_cA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (x : AF F ⊗[F] E) : sigR (AF F) σ x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem invT_mem_HR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {r : ℕ}
    (G J : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (x : E) (hx : x ≠ 0) (ξ : AF F ⊗[F] E)
    (hξ : ξ • incM F J = incM F (x • G⁻¹))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (incM F J)) :
    ∃ g : HR (AF F) σ G, g.1.1 = (b⁻¹).1.1ᵀ := by
  obtain ⟨m, hm⟩ := b
  have hb : m.1ᵀ * incM F J * m.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = incM F J := hm
  have hc : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ : AF F ⊗[F] E → AF F ⊗[F] E) = sigR (AF F) σ :=
    funext fun y => (sigR_eq_cA σ y).symm
  rw [hc] at hb
  have key := invTranspose_abstract (inclR (F := F) (AF F)) (sigR (AF F) σ) G J hG x hx ξ hξ m.1 (m⁻¹).1
    (Units.mul_inv m) (Units.inv_mul m) hb
  exact ⟨⟨invT m, key⟩, rfl⟩

theorem _root_.GlobalTheory.T.exists_unitary_invTranspose_of_scaledInverseGram : ∀ (D : D7) (V : HSp D) (J : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), ξ • incM D.host.F J = incM D.host.F (D.host.xi0 • V.gram⁻¹) →
    ∀ b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F J),
      ∃ g : GA D V, Formalism.L2.Theta.mt V g = (b⁻¹).1.1ᵀ := by
  intro D V J ξ hξ b
  obtain ⟨g, hg⟩ := invT_mem_HR D.sp.cm.sig V.gram J (GlobalTheory.Doubling.isHermND_gram V).2 D.host.xi0
    (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) ξ hξ b
  exact ⟨g, hg⟩

end GlobalTheory.SiegelThetaInvT
