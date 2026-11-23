import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompMemGinfC
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cusp.KinfCompact

section Mat

variable {p q n : ℕ} {A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ} {B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ}
  {G m : Matrix (Fin n) (Fin n) ℂ}

theorem Jpq_mul_self : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem inv_frame (hA : Aᴴ * Formalism.UG.Jpq p q * A = G) (h : A * B = 1) : Bᴴ * G * B = Formalism.UG.Jpq p q := by
  calc Bᴴ * G * B = (A * B)ᴴ * Formalism.UG.Jpq p q * (A * B) := by
        rw [← hA, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_block_iff (h1 : B * A = 1) (h2 : A * B = 1) :
    (∃ b : Mat p q, IsKC b ∧ b * A = A * m) ↔ Formalism.UG.Jpq p q * (A * m * B) = A * m * B * Formalism.UG.Jpq p q := by
  constructor
  · rintro ⟨b, hb, e⟩
    have : A * m * B = b := by rw [← e, Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [this]
    exact (LocWeil.CompactPart.isKC_iff b).1 hb
  · intro h
    exact ⟨A * m * B, (LocWeil.CompactPart.isKC_iff _).2 h, by rw [Matrix.mul_assoc, h1, Matrix.mul_one]⟩

theorem norm_entry_le (hA : Aᴴ * Formalism.UG.Jpq p q * A = G) (h1 : B * A = 1) (h2 : A * B = 1) (hm : mᴴ * G * m = G)
    (h : Formalism.UG.Jpq p q * (A * m * B) = A * m * B * Formalism.UG.Jpq p q) (i j : Fin n) :
    ‖m i j‖ ≤ ∑ c, ∑ a, ‖B i a‖ * ‖A c j‖ := by
  set b := A * m * B with hb
  have e1 : bᴴ * Formalism.UG.Jpq p q * b = Formalism.UG.Jpq p q := by
    calc _ = Bᴴ * (mᴴ * (Aᴴ * Formalism.UG.Jpq p q * A) * m) * B := by
          rw [hb, conjTranspose_mul, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hA, hm, inv_frame hA h2]
  have e2 : bᴴ * b = 1 := by
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc] at e1
    rw [← Matrix.mul_one (bᴴ * b), ← Jpq_mul_self, ← Matrix.mul_assoc, e1]
  have hU : b ∈ Matrix.unitaryGroup (Fin p ⊕ Fin q) ℂ := Matrix.mem_unitaryGroup_iff'.2 e2
  have e3 : m = B * b * A := by
    rw [hb]; simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [e3, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul, ← Finset.sum_mul, Matrix.mul_apply]
  refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)) (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (entry_norm_bound_of_unitary hU a c)

end Mat

variable {D : D7}

theorem isClosed_realPts (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  have : T2Space (Af D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GinfC V : Set (GA D V)) = {g | (finHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  exact isClosed_eq (GlobalTheory.Member.continuous_finHom_val D V) continuous_const

theorem continuous_realMat {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    Continuous fun h => infMat D.sp.cm.sig V.gram (θ τ) h := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have e : θ τ = θ₀ (tauE D τ) := SmoothForms.RealPts.infEmb_unique _ _ _ (hθ τ) (hθ₀ _)
  rw [e]
  exact ((GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1 (tauE D τ)).2.2.2.1

theorem isCompact_Kinf_and_conj : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), V.SigOK → ∀ A : CptF V, IsCartanFrame V A → IsCompact (Kinf θ V A : Set (GA D V)) ∧ ∀ A' : CptF V, IsCartanFrame V A' → ∃ g ∈ GinfC V, ∀ k, k ∈ Kinf θ V A' ↔ g * k * g⁻¹ ∈ Kinf θ V A := by
  intro D θ hθ V hV A hA
  choose B h1 h2 using fun τ => LocWeil.CompactPart.exists_inv hV (hA τ)
  refine ⟨?_, fun A' hA' => ?_⟩
  · obtain ⟨R, hR⟩ := Finite.bddAbove_range fun x : D.what₂.Tau × Fin V.rank × Fin V.rank =>
      ∑ c, ∑ a, ‖B x.1 x.2.1 a‖ * ‖A x.1 c x.2.2‖
    obtain ⟨K, hK, hKm⟩ := StabCompact.exists_compact_stab D V θ hθ R
    refine hK.of_isClosed_subset ?_ fun k hk => hKm k (fun y => ?_) fun τ i j => ?_
    · have e : (Kinf θ V A : Set (GA D V)) = (GinfC V : Set (GA D V)) ∩ ⋂ τ,
          {k | Formalism.UG.Jpq _ _ * (A τ * infMat D.sp.cm.sig V.gram (θ τ) k * B τ) =
            A τ * infMat D.sp.cm.sig V.gram (θ τ) k * B τ * Formalism.UG.Jpq _ _} := by
        ext k
        rw [Set.mem_inter_iff, Set.mem_iInter]
        exact and_congr_right fun _ => forall_congr' fun τ => exists_block_iff (h1 τ) (h2 τ)
      rw [e]
      refine (isClosed_realPts V).inter (isClosed_iInter fun τ => ?_)
      have hc := (continuous_const (y := A τ)).matrix_mul (continuous_realMat hθ V τ) |>.matrix_mul
        (continuous_const (y := B τ))
      exact isClosed_eq (continuous_const.matrix_mul hc) (hc.matrix_mul continuous_const)
    · have ha' : finHom V k = 1 := hk.1
      rw [SmoothForms.RealPts.finMat_eq V, ha', Units.val_one, Matrix.one_mulVec]
    · exact (norm_entry_le (hA τ) (h1 τ) (h2 τ) (FockCompare.RealAction.infMat_mem_UH hθ V k τ)
        ((exists_block_iff (h1 τ) (h2 τ)).1 (hk.2 τ)) i j).trans (hR ⟨(τ, i, j), rfl⟩)
  · obtain ⟨g, hg, hu⟩ := (SmoothForms.RealPts.glue θ hθ V).2 (fun τ => B τ * A' τ) fun τ => by
      change (B τ * A' τ)ᴴ * gramAt D V τ * (B τ * A' τ) = gramAt D V τ
      calc _ = (A' τ)ᴴ * ((B τ)ᴴ * gramAt D V τ * B τ) * A' τ := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [inv_frame (hA τ) (h2 τ), hA' τ]
    refine ⟨g, hg, fun k => and_congr ?_ (forall_congr' fun τ => exists_congr fun b => and_congr_right fun _ => ?_)⟩
    · rw [mul_mem_cancel_right (inv_mem hg), mul_mem_cancel_left hg]
    · have e0 : A τ * infMat D.sp.cm.sig V.gram (θ τ) g = A' τ := by
        rw [hu, ← Matrix.mul_assoc, h2, Matrix.one_mul]
      have e1 : infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) g = 1 := by
        rw [← SmoothForms.HeightCoset.infMat_mul', inv_mul_cancel, SmoothForms.HeightCoset.infMat_one']
      have e2 := mul_eq_one_comm.1 e1
      rw [SmoothForms.HeightCoset.infMat_mul', SmoothForms.HeightCoset.infMat_mul', ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, e0]
      constructor
      · intro h
        rw [← h, ← e0, Matrix.mul_assoc, Matrix.mul_assoc, e2, Matrix.mul_one]
      · intro h
        rw [← e0, ← Matrix.mul_assoc, h, Matrix.mul_assoc _ _ (infMat _ _ _ g), e1, Matrix.mul_one, e0]

end GlobalTheory.Cusp.KinfCompact

end
