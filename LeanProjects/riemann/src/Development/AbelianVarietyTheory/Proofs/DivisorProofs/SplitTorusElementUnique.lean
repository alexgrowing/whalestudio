import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorus

theorem idelicFrameTorusElement_apply_column_decomposition {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J} (ha : IsIdTorusElt σ J X Y l a) (z : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J a).1 *ᵥ z =
      adMat F X *ᵥ (diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *ᵥ
          (adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z)) +
      adMat F Y *ᵥ (diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *ᵥ
          (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z)) +
      (z - adMat F X *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z)
         - adMat F Y *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z)) := by
  set P := adMat F (Formalism.UG.cT (σ : E →+* E) X * J)
  set Q := adMat F (Formalism.UG.cT (σ : E →+* E) Y * J)
  have mm : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E),
      adMat F A * adMat F B = adMat F (A * B) := fun A B => (Matrix.map_mul).symm
  have hPX : P * adMat F X = 0 := by rw [mm, hW.xx]; simp
  have hPY : P * adMat F Y = 1 := by rw [mm, hW.xy]; simp
  have hQX : Q * adMat F X = 1 := by rw [mm, yx h hJ hW]; simp
  have hQY : Q * adMat F Y = 0 := by rw [mm, hW.yy]; simp
  set w := z - adMat F X *ᵥ (Q *ᵥ z) - adMat F Y *ᵥ (P *ᵥ z) with hw
  have hPw : P *ᵥ w = 0 := by
    rw [hw, mulVec_sub, mulVec_sub, mulVec_mulVec (M := P) (N := adMat F X), mulVec_mulVec (M := P) (N := adMat F Y), hPX, hPY,
      zero_mulVec, one_mulVec]; simp
  have hQw : Q *ᵥ w = 0 := by
    rw [hw, mulVec_sub, mulVec_sub, mulVec_mulVec (M := Q) (N := adMat F X), mulVec_mulVec (M := Q) (N := adMat F Y), hQX, hQY,
      zero_mulVec, one_mulVec]; simp
  have hmem : w ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ := by
    refine ⟨(Submodule.mem_iInf _).2 fun i => (Submodule.mem_iInf _).2 fun _ => LinearMap.mem_ker.2 ?_,
      (Submodule.mem_iInf _).2 fun i => (Submodule.mem_iInf _).2 fun _ => LinearMap.mem_ker.2 ?_⟩
    · exact congrFun hPw i
    · exact congrFun hQw i
  have hz : z = adMat F X *ᵥ (Q *ᵥ z) + adMat F Y *ᵥ (P *ᵥ z) + w := by rw [hw]; abel
  conv_lhs => rw [hz]
  rw [mulVec_add, mulVec_add, mulVec_mulVec (N := adMat F X), mulVec_mulVec (N := adMat F Y), ha.1, ha.2.1,
    ha.2.2 w hmem, ← mulVec_mulVec, ← mulVec_mulVec]

theorem isIdTorusElt_uniq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a b : GAd σ J}, IsIdTorusElt σ J X Y l a → IsIdTorusElt σ J X Y l b → a = b := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW l a b ha hb
  apply matHom_injective (AF F) σ J
  apply Units.ext
  have hv : ∀ z, (matHom _ σ J a).1 *ᵥ z = (matHom _ σ J b).1 *ᵥ z := fun z => by
    rw [idelicFrameTorusElement_apply_column_decomposition h hJ hW ha, idelicFrameTorusElement_apply_column_decomposition h hJ hW hb]
  ext i j
  simpa [mulVec_single_one] using congrFun (hv (Pi.single j 1)) i

end GlobalTheory.IdTorus

end
