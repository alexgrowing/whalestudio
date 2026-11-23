import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameOrthogonalDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedHermitianNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedWittFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedLocalLatticeMembershipStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedLatticeIsLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedLatticeSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedLatticeSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedArchimedeanGlExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanGlAdelicApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSumNormSumEqualStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisRestrict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sum_sig_mulVec {A : Type} [CommRing A] (s : A →+* A) {p q : ℕ} (M : Matrix (Fin p) (Fin q) A) (u : Fin q → A) :
    ∑ i, s ((M *ᵥ u) i) * (M *ᵥ u) i = (fun j => s (u j)) ⬝ᵥ ((Formalism.UG.cT s M * M) *ᵥ u) := by
  have h1 : (fun i => s ((M *ᵥ u) i)) = M.map s *ᵥ fun j => s (u j) := funext fun i => RingHom.map_mulVec s M u i
  change (fun i => s ((M *ᵥ u) i)) ⬝ᵥ (M *ᵥ u) = _
  rw [h1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec]
  simp only [Formalism.UG.cT, Matrix.vecMul_transpose]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec]

theorem compFin_adVec' (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {k : ℕ} (z : Fin k → E) (i : Fin k) :
    compFin F E v (GlobalTheory.EisMidHt.adVec F z i) = inclR (F := F) (Fv F v) (z i) := by
  show compFin F E v ((1 : AF F) ⊗ₜ[F] z i) = (1 : Fv F v) ⊗ₜ[F] z i
  simp [compFin, Algebra.TensorProduct.map_tmul]

theorem compInf_adVec' (w : InfinitePlace F) {k : ℕ} (z : Fin k → E) (i : Fin k) :
    compInf F E w (GlobalTheory.EisMidHt.adVec F z i) = inclR (F := F) w.Completion (z i) := by
  show compInf F E w ((1 : AF F) ⊗ₜ[F] z i) = (1 : w.Completion) ⊗ₜ[F] z i
  simp [compInf, Algebra.TensorProduct.map_tmul]

theorem restrict_adapted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1 + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → IsHermND σ J → IsWittFrame σ J X Y →
    GlobalTheory.EisLine.IsAdapted σ J X Y L a →
    ∃ (m : ℕ) (ι : (Fin m → E) →ₗ[E] (Fin n → E)) (J₀ : Matrix (Fin m) (Fin m) E)
      (X₀ Y₀ : Matrix (Fin m) (Fin (r + 1)) E) (L₀ : Submodule (𝓞 E) (Fin m → E)) (a₀ : GL (Fin m) (AF F ⊗[F] E)),
      m + 2 = n ∧ IsHermND σ J₀ ∧ IsWittFrame σ J₀ X₀ Y₀ ∧ GlobalTheory.EisLine.IsAdapted σ J₀ X₀ Y₀ L₀ a₀ ∧
      (∀ u v, hE σ J₀ u v = hE σ J (ι u) (ι v)) ∧
      (∀ z, hE σ J (GlobalTheory.EisMidHt.firstColumn X) z = 0 → hE σ J (GlobalTheory.EisMidHt.firstColumn Y) z = 0 → ∃ u, ι u = z) ∧
      ∀ u, GlobalTheory.EisMidHt.ht L₀ a₀ (GlobalTheory.EisMidHt.adVec F u) = GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (ι u)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a hσ _ hJ hW hA
  have hI := GlobalTheory.T.restricted_archimedean_gl_exists F E σ n J (r + 1) X Y hσ hJ hW L a hA
  choose g hg1 hg2 hg3 using hI
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.T.archimedean_gl_adelic_approximation F E (dim σ J X Y) g
  have hinv : ∀ w, Formalism.UG.bc (compInf F E w) a₀⁻¹ = (g w)⁻¹ := fun w => by rw [map_inv, ha₀]
  refine ⟨dim σ J X Y, ι σ J X Y, J0 σ J X Y, X0 σ J X Y, Y0 σ J X Y, L0 σ J X Y L, a₀,
    GlobalTheory.T.witt_frame_orthogonal_dimension F E σ n J (r + 1) X Y hσ hJ hW, GlobalTheory.T.restricted_hermitian_nondegenerate F E σ n J (r + 1) X Y hσ hJ hW,
    GlobalTheory.T.restricted_witt_frame F E σ n J (r + 1) X Y hσ hJ hW,
    ⟨GlobalTheory.T.restricted_lattice_isLattice F E σ n J (r + 1) X Y hσ hJ hW L a hA, GlobalTheory.T.restricted_lattice_self_dual F E σ n J (r + 1) X Y hσ hJ hW L a hA,
      GlobalTheory.T.restricted_lattice_split F E σ n J (r + 1) X Y hσ hJ hW L a hA, fun w => by rw [ha₀]; exact hg1 w,
      fun w => by rw [hinv]; exact hg2 w⟩,
    hE_J0 σ J X Y, fun z h1 h2 => exists_ι_eq σ J X Y ⟨h1, h2⟩, fun u => ?_⟩
  have hloc := GlobalTheory.T.restricted_local_lattice_membership F E σ n J (r + 1) X Y hσ hJ hW L a hA
  have hfin : ∀ v, GlobalTheory.EisMidHt.normFin F (L0 σ J X Y L) v (fun i => compFin F E v (GlobalTheory.EisMidHt.adVec F u i)) =
      GlobalTheory.EisMidHt.normFin F L v (fun i => compFin F E v (GlobalTheory.EisMidHt.adVec F (ι σ J X Y u) i)) := fun v => by
    have e : (fun i => compFin F E v (GlobalTheory.EisMidHt.adVec F (ι σ J X Y u) i)) =
        (P σ J X Y).map (inclR (F := F) (Fv F v)) *ᵥ (fun i => compFin F E v (GlobalTheory.EisMidHt.adVec F u i)) := by
      funext i
      simp only [compFin_adVec', ι_apply]
      exact RingHom.map_mulVec _ _ _ i
    rw [e]
    unfold GlobalTheory.EisMidHt.normFin
    congr 1
    ext c
    simp only [Set.mem_setOf_eq, hloc, Matrix.mulVec_smul]
  have hinf : ∀ w, GlobalTheory.EisMidHt.normInf a₀ w (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F u i)) =
      GlobalTheory.EisMidHt.normInf a w (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F (ι σ J X Y u) i)) := fun w => by
    have e : (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F (ι σ J X Y u) i)) =
        (P σ J X Y).map (inclR (F := F) w.Completion) *ᵥ (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F u i)) := by
      funext i
      simp only [compInf_adVec', ι_apply]
      exact RingHom.map_mulVec _ _ _ i
    rw [e]
    unfold GlobalTheory.EisMidHt.normInf
    simp only
    rw [ha₀, ← map_inv, Matrix.mulVec_mulVec]
    congr 2
    refine GlobalTheory.T.hermitian_sum_norm_sum_equal F E σ hσ w _ _ _ _ ?_
    rw [sum_sig_mulVec, sum_sig_mulVec, Formalism.UG.cT_mul, hg3 w]
    simp only [Matrix.mul_assoc]
  unfold GlobalTheory.EisMidHt.ht
  simp only [hfin, hinf]

end GlobalTheory.EisRestrict

end
