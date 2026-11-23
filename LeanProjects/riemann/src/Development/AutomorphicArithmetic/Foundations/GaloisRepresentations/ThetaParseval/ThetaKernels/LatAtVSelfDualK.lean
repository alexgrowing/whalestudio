import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PsiSympLatAtVK

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Idele WithZero
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff)
noncomputable section
namespace GlobalTheory.LatSelfDualAll
section Scalar
variable {F : Type} [Field F] [NumberField F]
end Scalar
section Lat
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Lat
end GlobalTheory.LatSelfDualAll
namespace GlobalTheory.LatSelfDualAll
section Frame
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Frame
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Gen
end GlobalTheory.LatSelfDualAll
namespace GlobalTheory.LatSelfDualAll
open GlobalTheory.InertSelfDual (exists_traceFamily det_ne_zero_of_herm det_ne_zero_of_skew decomp hTens_frame trace_expand)
theorem latAtV_selfDual_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), _root_.UpperTheory.TP.W.GoodK σ B →
    X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (z : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) z →
      (z ∈ latAtV X W v ↔ ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B n d X W r₁ s₁ r₂ s₂ hB hX hW v z hz
  constructor
  · intro hzm γ hγ
    have h := _root_.GlobalTheory.LatVacArith.psi_symp_latAtV_k σ B X W _ _ _ _ hB hX hW v (-1) 1
      (by rw [map_one]; exact one_mem _) z hzm γ hγ
    simpa using h
  · intro hψ
    haveI := hB.unram
    obtain ⟨m, s, c, hsc⟩ := exists_traceFamily (F := F) (E := E)
    obtain ⟨k, S, T, hS, hTm, -, hTS⟩ := exists_formFrame' σ X.J (det_ne_zero_of_herm σ B hX) X.L hX.lat
      (fun y hy => (hX.dual y).2 fun x hx => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]; exact RingOfIntegers.isIntegral_coe r)
    obtain ⟨k', S', T', hS', hTm', hTd', hTS'⟩ := exists_formFrame' σ W.J (det_ne_zero_of_skew σ B hW) W.L hW.lat
      (fun y hy => (hW.dual y).2 fun x hx o => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]
        exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (RingOfIntegers.isIntegral_coe r)))
    set C := incM F (X.J * S.map σ)ᵀ * z * (incM F (W.J * S'.map σ)ᵀ)ᵀ with hC
    have hCat : ∀ j l, At (evFin F v) (C j l) := fun j l u hu => by
      have hz' : u • z = 0 := hz u hu
      have h1 : u • C = incM F (X.J * S.map σ)ᵀ * (u • z) * (incM F (W.J * S'.map σ)ᵀ)ᵀ := by
        rw [hC, Matrix.mul_smul, Matrix.smul_mul]
      rw [hz', Matrix.mul_zero, Matrix.zero_mul] at h1
      have := congrFun (congrFun h1 j) l
      simpa using this
    have hint : ∀ (e : E), IsIntegral ℤ e → ∀ j l, ∀ y ∈ v.adicCompletionIntegers F,
        psiLoc B.ψ v (evFin F v (Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (σ e) * C j l)) * y) = 1 := by
      intro e hei j l
      set M := incM F (Matrix.vecMulVec (fun i => e * S i j) (fun i => S' i l)) with hM
      set t := symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z M with ht
      have hx : (fun i => e * S i j) ∈ X.L := by
        have := X.L.smul_mem (⟨e, hei⟩ : 𝓞 E) (hS j)
        convert this using 1
        ext i; first | rfl | simp [Algebra.smul_def]
      have htat : At (evFin F v) t := fun u hu => by
        have := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) u 1 z M
        rw [hz u hu, one_smul, mul_one, GlobalTheory.LatVacArith.symp_zero_left] at this
        exact this.symm
      have htC : t = -Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (σ e) * C j l) := by
        rw [ht, symp, hM, hTens_frame, neg_one_mul, map_neg]
      have key : ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v t * y) = 1 := by
        intro y hy
        have hmem : GlobalTheory.LatVac.liftV v y • M ∈ latAtV X W v :=
          AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v y, by rw [GlobalTheory.LatVac.evFin_liftV]; exact hy,
            _, hx, _, hS' l, rfl⟩
        have h1 := hψ _ hmem
        have h2 := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) 1 (GlobalTheory.LatVac.liftV v y) z M
        rw [one_smul, one_mul] at h2
        rw [h2] at h1
        have hat2 : At (evFin F v) (GlobalTheory.LatVac.liftV v y * t) := fun u hu => by
          have := htat u hu
          rw [smul_eq_mul] at this ⊢
          rw [mul_left_comm, this, mul_zero]
        rw [GlobalTheory.VacIndic.psi_of_at _ hat2, map_mul, GlobalTheory.LatVac.evFin_liftV, mul_comm] at h1
        exact h1
      intro y hy
      have := key (-y) (neg_mem hy)
      rwa [htC, map_neg, neg_mul_neg] at this
    have hσ : Function.Bijective σ := AlgHom.bijective σ
    have hint' : ∀ i j l, ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v (Algebra.trace (AF F) (AE F E)
        (inclR (F := F) (AF F) (c i : E) * C j l)) * y) = 1 := by
      intro i j l
      obtain ⟨e, he⟩ := hσ.2 (c i : E)
      have hei : IsIntegral ℤ e := by
        rw [← isIntegral_algHom_iff ((σ : E →+* E).toIntAlgHom) hσ.1]
        show IsIntegral ℤ (σ e)
        rw [he]; exact RingOfIntegers.isIntegral_coe _
      have := hint e hei j l
      rwa [he] at this
    rw [decomp T (X.J * S.map σ)ᵀ T' (W.J * S'.map σ)ᵀ hTS hTS' z, ← hC]
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.sum_mem _ fun l _ => ?_
    rw [trace_expand s c hsc (C j l), Finset.sum_smul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have hxi : (fun r => (s i : E) * T r j) ∈ X.L := by
      have := X.L.smul_mem (s i) (hTm j)
      convert this using 1
      ext r; simp [Algebra.smul_def]
    have hat : At (evFin F v) (Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (c i : E) * C j l)) := by
      intro u hu
      rw [smul_eq_mul, ← smul_eq_mul, ← map_smul, ← mul_smul_comm]
      have := hCat j l u hu
      rw [this, mul_zero, map_zero]
    have hmem := smul_mem_latAtV σ B hB.std hX hW v hat (hint' i j l) hxi (hTm' l) (hTd' l)
    convert hmem using 1
    rw [smul_assoc]
    congr 1
    ext p q
    simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, map_mul, smul_eq_mul]
    ring
end GlobalTheory.LatSelfDualAll
end
end
