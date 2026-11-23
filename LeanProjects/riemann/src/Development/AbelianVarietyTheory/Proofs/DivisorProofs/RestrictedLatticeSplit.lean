import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisRestrictSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

omit [NumberField F] [NumberField E] in

theorem mulVec_eq_hE {k : ℕ} (M : Matrix (Fin n) (Fin k) E) (z : Fin n → E) (i : Fin k) :
    ((Formalism.UG.cT (σ : E →+* E) M * J) *ᵥ z) i = hE σ J (fun a => M a i) z := by
  rw [hE_eq_dot]
  simp only [Formalism.UG.cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum,
    Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp [mul_assoc]

omit [NumberField F] [NumberField E] in

theorem mul_apply_eq_hE {k l : ℕ} (M : Matrix (Fin n) (Fin k) E) (N : Matrix (Fin n) (Fin l) E) (i : Fin k) (j : Fin l) :
    (Formalism.UG.cT (σ : E →+* E) M * J * N) i j = hE σ J (fun a => M a i) (fun a => N a j) :=
  mulVec_eq_hE σ J M (fun a => N a j) i

variable {σ J}

theorem yx_eq_one {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} (hσ : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
  ext i j
  have h := congrArg σ (congrFun₂ hW.xy j i)
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, RingHom.coe_coe,
    sigma_sigma hσ, hJ.1, Matrix.one_apply, apply_ite σ, map_one, map_zero, Finset.sum_mul] at h ⊢
  rw [Finset.sum_comm, if_congr eq_comm rfl rfl, ← h]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem witt_frame_tail_mem_orthogonal {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hσ : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (j : Fin r) :
    (fun k => X k j.succ) ∈ V0 σ J X Y ∧ (fun k => Y k j.succ) ∈ V0 σ J X Y := by
  have yx := yx_eq_one hσ hJ hW
  have e : ∀ (M N : Matrix (Fin n) (Fin (r + 1)) E),
      hE σ J (GlobalTheory.EisMidHt.firstColumn M) (fun k => N k j.succ) = (Formalism.UG.cT (σ : E →+* E) M * J * N) 0 j.succ :=
    fun M N => (mul_apply_eq_hE σ J M N 0 j.succ).symm
  have ne : (0 : Fin (r + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  refine ⟨(mem_invariant_forms σ J X Y).2 ⟨?_, ?_⟩, (mem_invariant_forms σ J X Y).2 ⟨?_, ?_⟩⟩
  · rw [e, hW.xx]; rfl
  · rw [e, yx, Matrix.one_apply_ne ne]
  · rw [e, hW.xy, Matrix.one_apply_ne ne]
  · rw [e, hW.yy]; rfl

theorem restrictedLattice_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), GlobalTheory.EisLine.IsAdapted σ J X Y L a →
    ∀ z ∈ L0 σ J X Y L, ∀ i, ((Formalism.UG.cT (σ : E →+* E) (Y0 σ J X Y) * J0 σ J X Y) *ᵥ z) i • (X0 σ J X Y)ᵀ i ∈ L0 σ J X Y L ∧
      ((Formalism.UG.cT (σ : E →+* E) (X0 σ J X Y) * J0 σ J X Y) *ᵥ z) i • (Y0 σ J X Y)ᵀ i ∈ L0 σ J X Y L := by
  intro F E _ _ _ _ _ σ n J r X Y hσ hJ hW L a hA z hz i
  obtain ⟨hXi, hYi⟩ := witt_frame_tail_mem_orthogonal hσ hJ hW i
  have hX := ι_coordTail σ J X Y X i hXi
  have hY := ι_coordTail σ J X Y Y i hYi
  have hz' : ι σ J X Y z ∈ L := hz
  have c1 : ((Formalism.UG.cT (σ : E →+* E) (Y0 σ J X Y) * J0 σ J X Y) *ᵥ z) i =
      ((Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ ι σ J X Y z) i.succ := by
    rw [mulVec_eq_hE, mulVec_eq_hE, hE_J0]
    exact congrArg (hE σ J · _) hY
  have c2 : ((Formalism.UG.cT (σ : E →+* E) (X0 σ J X Y) * J0 σ J X Y) *ᵥ z) i =
      ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ ι σ J X Y z) i.succ := by
    rw [mulVec_eq_hE, mulVec_eq_hE, hE_J0]
    exact congrArg (hE σ J · _) hX
  obtain ⟨s1, s2⟩ := hA.split _ hz' i.succ
  refine ⟨?_, ?_⟩
  · show ι σ J X Y _ ∈ L
    rw [map_smul, c1]
    convert s1 using 2
    exact hX
  · show ι σ J X Y _ ∈ L
    rw [map_smul, c2]
    convert s2 using 2
    exact hY

end GlobalTheory.EisRestrictSplit
