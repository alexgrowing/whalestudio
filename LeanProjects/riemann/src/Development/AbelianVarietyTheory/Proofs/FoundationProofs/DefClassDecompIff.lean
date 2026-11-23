import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.DoubleCosetDecomposition
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LeftInvOfUnitary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsOpenStabilizerCompletedLatticeAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

noncomputable section

namespace GlobalTheory.DecompCompare

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Group

variable {G : Type} [Group G] (Γ K : Subgroup G)

end Group

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def stabEquiv (K : Subgroup (HA (AF F) σ J)) (g : HA (AF F) σ J) :
    stabAt σ J K g ≃ Unfold.stab (ratPts σ J) K g where
  toFun γ := ⟨⟨γ.1, ((mem_stabAt σ J K g γ.1).1 γ.2).1⟩, by
    have h := ((mem_stabAt σ J K g γ.1).1 γ.2).2
    rw [mul_assoc] at h
    exact h⟩
  invFun γ := ⟨γ.1.1, (mem_stabAt σ J K g γ.1.1).2 ⟨γ.1.2, by
    rw [mul_assoc]
    exact γ.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Stab

theorem frame_inv {n P Q : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G P Q)
    {A : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ} (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) :
    ∃ L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ, L * A = 1 ∧ A * L = 1 := by
  obtain ⟨A₀, L₀, h0, hl, hr⟩ := GlobalTheory.VolPairExists.exists_frame h
  obtain ⟨e, -⟩ := h
  have h1 : (L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * Aᴴ * Formalism.UG.Jpq P Q) * A = 1 := by
    calc (L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * Aᴴ * Formalism.UG.Jpq P Q) * A
        = L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) := by simp only [Matrix.mul_assoc]
      _ = L₀ * Formalism.UG.Jpq P Q * (A₀ * L₀)ᴴ * Formalism.UG.Jpq P Q * A₀ := by
          rw [hA, ← h0, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = L₀ * (Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q) * A₀ := by
          rw [hr, Matrix.conjTranspose_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [GlobalTheory.VolPairExists.jpq_mul_self, Matrix.mul_one, hl]
  exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_equiv e).1 h1⟩

variable (D : D7)

theorem KSub_eq (W : HSpace D.host.E) (hW : W.SigOK) {P Q : ℕ} (hs : ∀ τ, W.sig τ = (P, Q))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ))
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ)
    (hA : ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) :
    KSub D W P Q θ A = levelW D.sp.cm W := by
  ext h
  refine ⟨fun hh => hh.1, fun hh => ⟨hh, fun ρ => ?_⟩⟩
  have hsig : Formalism.UG.HasSignature (W.gram.map (embOf D ρ)) P Q := by
    have := hW (embOf D ρ)
    rwa [hs] at this
  obtain ⟨L, hl, hr⟩ := frame_inv hsig (hA ρ)
  have hu : (infMat D.sp.cm.sig W.gram (θ ρ) h)ᴴ * W.gram.map (embOf D ρ) * infMat D.sp.cm.sig W.gram (θ ρ) h =
      W.gram.map (embOf D ρ) := GlobalTheory.FockCompare.RealAction.infMat_mem_UH (D := D) (θ := θ) hθ W h ρ
  refine ⟨GlobalTheory.VolPairExists.mkU _ (GlobalTheory.VolPairExists.conj_unitary (hA ρ) hr hu), Set.mem_univ _, ?_⟩
  rw [GlobalTheory.VolPairExists.mat_mkU, Matrix.mul_assoc, hl, Matrix.mul_one]

theorem exists_data (W : HSpace D.host.E) (hW : W.SigOK) {P Q : ℕ} (hs : ∀ τ, W.sig τ = (P, Q)) :
    (∃ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) ∧
    ∃ A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ,
      ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ) := by
  refine ⟨GlobalTheory.DualPairCompare.exists_infFam D, ?_⟩
  have hsig : ∀ ρ, Formalism.UG.HasSignature (W.gram.map (embOf D ρ)) P Q := fun ρ => by
    have := hW (embOf D ρ)
    rwa [hs] at this
  choose A L hA _ using fun ρ => GlobalTheory.VolPairExists.exists_frame (hsig ρ)
  exact ⟨A, hA⟩

theorem isOpen_levelW (W : HSpace D.host.E) :
    IsOpen (levelW D.sp.cm W : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) :=
  GlobalTheory.StabOpen.isOpen_stab_latHat D W

end GlobalTheory.DecompCompare
