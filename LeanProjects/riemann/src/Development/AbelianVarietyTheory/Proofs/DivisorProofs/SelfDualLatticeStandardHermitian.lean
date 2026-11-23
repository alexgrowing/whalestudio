import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfNormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitLength
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb.LatOnto

open GlobalTheory.InertUnitOrb.ModelOfN

theorem exists_orthonormal_mem {K : UQ} (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (h : V → V → K.E),
    (∀ y y' z, h (y + y') z = h y z + h y' z) → (∀ (a : K.E) y z, h (a • y) z = a * h y z) →
    (∀ y z, h z y = K.c (h y z)) → Module.finrank K.E V = n → ∀ L : Submodule K.O V, L.FG →
    Submodule.span K.E (L : Set V) = ⊤ → (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∃ v : Fin n → V, (∀ i, v i ∈ L) ∧ ∀ i j, h (v i) (v j) = if i = j then 1 else 0 := by
  first
  | exact @_root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal
  | exact _root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal
  | (apply _root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal ..)

end GlobalTheory.InertUnitOrb.LatOnto

namespace GlobalTheory.InertUnitOrb.LatOnto

open GlobalTheory.InertUnitOrb.ModelOfN

theorem exists_unitLat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → (∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) → ∃ q : UL n w, unitLat e B ψ q = L := by
  intro E _ _ _ _ w hns K e he hint n B ψ x hσx hH L hLat hdual
  have hadd : ∀ y y' z, B.herm x (y + y') z = B.herm x y z + B.herm x y' z := by
    intro y y' z
    simp only [InvAlg.herm, mul_add, add_mul, map_add]
  have hsmul : ∀ (a : K.E) y z, B.herm x (a • y) z = a * B.herm x y z := by
    intro a y z
    simp only [InvAlg.herm, mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have hsym : ∀ y z, B.herm x z y = K.c (B.herm x y z) := by
    intro y z
    simp only [InvAlg.herm]
    rw [← trace_sigma B, map_mul B.σ, map_mul B.σ, B.σ_σ, hσx]
    congr 1
    ring
  have hn : Module.finrank K.E B.A = n := by rw [ψ.finrank_eq, Module.finrank_fin_fun]
  obtain ⟨v, hvL, hv⟩ := exists_orthonormal_mem n B.A (B.herm x) hadd hsmul hsym hn L hLat.1 hLat.2 hdual
  obtain ⟨b, hb⟩ := exists_basis_of_orthonormal (B.herm x) hadd hsmul hn v hv
  let P : Matrix (Fin n) (Fin n) K.E := Matrix.of fun i j => ψ (v j) i
  let Pc : Matrix (Fin n) (Fin n) K.E := Formalism.UG.cT (K.c : K.E →+* K.E) P
  have hPc : ∀ i k, Pc i k = K.c (ψ (v i) k) := fun i k => rfl
  have hPP : Pc * P = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 := hH (v j) (v i)
    simp only [stdH] at h1
    simp only [hPc, P, Matrix.of_apply]
    rw [show (∑ k, K.c (ψ (v i) k) * ψ (v j) k) = ∑ k, ψ (v j) k * K.c (ψ (v i) k) from
      Finset.sum_congr rfl fun k _ => mul_comm _ _, h1, hv]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hPP' : P * Pc = 1 := mul_eq_one_comm.1 hPP
  let eh : K.E →+* w.adicCompletion E := e.toRingHom
  have hmul1 : P.map eh * Pc.map eh = 1 := by
    rw [← Matrix.map_mul, hPP', Matrix.map_one _ (map_zero eh) (map_one eh)]
  have hmul2 : Pc.map eh * P.map eh = 1 := by
    rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero eh) (map_one eh)]
  let qG : GLw n w := ⟨P.map eh, Pc.map eh, hmul1, hmul2⟩
  have hcT : Formalism.UG.cT (cj w) (P.map eh) = Pc.map eh := by
    refine Matrix.ext fun i j => ?_
    change cj w (e (ψ (v i) j)) = e (K.c (ψ (v i) j))
    exact (he _).symm
  have hqU : qG ∈ UL n w := by
    unfold UL
    rw [if_neg hns]
    show Formalism.UG.cT (cj w) (P.map eh) * 1 * P.map eh = 1
    rw [hcT, Matrix.mul_one, hmul2]
  refine ⟨⟨qG, hqU⟩, ?_⟩
  have hinv : ((((⟨qG, hqU⟩ : UL n w)⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map
      e.symm = Pc := by
    refine Matrix.ext fun i j => ?_
    show e.symm (e (Pc i j)) = Pc i j
    exact e.symm_apply_apply _
  have hcoef : ∀ y i, (Pc *ᵥ ψ y) i = B.herm x y (v i) := by
    intro y i
    rw [← hH]
    simp only [Matrix.mulVec, dotProduct, hPc, stdH]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hexp : ∀ y j, B.herm x y (v j) = b.repr y j := by
    intro y j
    conv_lhs => rw [← b.sum_repr y]
    rw [show B.herm x (∑ i, b.repr y i • b i) (v j) = ∑ i, b.repr y i * B.herm x (b i) (v j) from ?_]
    · simp only [hb, hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        have := hsmul 0 0 (v j)
        simpa using this
      | insert a s ha ih' =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsmul, ih']
  unfold unitLat
  rw [hinv]
  ext y
  show (∀ i, (Matrix.toLin' Pc (ψ y)) i ∈ (algebraMap K.O K.E).range) ↔ y ∈ L
  simp only [Matrix.toLin'_apply, hcoef]
  constructor
  · intro H
    choose a ha using H
    have hy : y = ∑ i, a i • v i := by
      conv_lhs => rw [← b.sum_repr y]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hexp, ← ha, algebraMap_smul, hb]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => L.smul_mem _ (hvL i)
  · intro hy i
    exact (hdual y).1 hy (v i) (hvL i)

end GlobalTheory.InertUnitOrb.LatOnto
