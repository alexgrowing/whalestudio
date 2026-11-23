import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.LagrThetaInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev dC (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin n) R :=
  ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) R).submatrix finSumFinEquiv.symm id)

theorem dC_mul_inl {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (finSumFinEquiv (Sum.inl p)) j = a p j := by
  simp only [dC, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  simp [diagCols, Matrix.one_apply]

theorem dC_mul_inr {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (finSumFinEquiv (Sum.inr p)) j = a p j := by
  simp only [dC, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  simp [diagCols, Matrix.one_apply]

theorem dC_mul_castAdd {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (Fin.castAdd n p) j = a p j := by
  simpa using dC_mul_inl a p j

theorem dC_mul_addNat {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (p.addNat n) j = a p j := by
  simpa using dC_mul_inr a p j

theorem dC_mul_eq {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) :
    dC R n * a = Matrix.of fun i j => a (Sum.elim id id (finSumFinEquiv.symm i)) j := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with p | p
  · rw [dC_mul_inl, Matrix.of_apply, Equiv.symm_apply_apply]; rfl
  · rw [dC_mul_inr, Matrix.of_apply, Equiv.symm_apply_apply]; rfl

theorem dblG_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i k : Fin n ⊕ Fin n) :
    GlobalTheory.WeilSchrodinger.DblTargetF.dblG J (finSumFinEquiv i) (finSumFinEquiv k) = dbl J i k := by
  simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem hTens_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E)
    (a b : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) :
    hTens (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB) (dC (AF F ⊗[F] E) nT * a) (dC (AF F ⊗[F] E) nT * b) = 0 := by
  unfold hTens
  have ha : dC (AF F ⊗[F] E) nT * a = Matrix.of fun i j => a (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    dC_mul_eq a
  have hb : dC (AF F ⊗[F] E) nT * b = Matrix.of fun i j => b (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    dC_mul_eq b
  rw [ha, hb]
  simp only [← finSumFinEquiv.sum_comp, Matrix.of_apply, Equiv.symm_apply_apply, incM, Matrix.map_apply,
    Matrix.transpose_apply, dblG_apply]
  simp only [Fintype.sum_sum_type]
  simp [dbl, Finset.sum_add_distrib, Finset.sum_neg_distrib, dC_mul_castAdd, dC_mul_addNat]

end GlobalTheory.LagrThetaInv

namespace GlobalTheory.LagrThetaInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem schr_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E)
    (ξ : AF F ⊗[F] E) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ)
    (ψ : AddChar (AF F) ℂ) (a b : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) (φ : (κ → AF F) → ℂ) :
    schr ψ (co.e (dC (AF F ⊗[F] E) nT * a)) (schr ψ (co.e (dC (AF F ⊗[F] E) nT * b)) φ) =
      schr ψ (co.e (dC (AF F ⊗[F] E) nT * (a + b))) φ := by
  rw [GlobalTheory.ThetaQuasiRat.schr_schr, ← co.form, symp, hTens_dC, mul_zero, map_zero, mul_zero,
    AddChar.map_zero_eq_one, one_smul, ← map_add, Matrix.mul_add]

theorem dC_map {n : ℕ} : (dC E n).map (incAF F E) = dC (AF F ⊗[F] E) n := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with p | p <;>
    simp only [dC, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, diagCols,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply] <;> split_ifs <;> simp

theorem dC_mul_rat {nS nT : ℕ} (γ : Matrix (Fin nT) (Fin nS) E) :
    dC (AF F ⊗[F] E) nT * γ.map (incAF F E) = incM F (dC E nT * γ) := by
  rw [← dC_map, ← Matrix.map_mul]
  rfl

end GlobalTheory.LagrThetaInv

open scoped Pointwise in
open GlobalTheory.LagrThetaInv in

theorem GlobalTheory.LagrThetaInv.lagrInt_rho_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ,
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ)) = GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 _ h𝓕 u φ hφ
  change GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
      (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)) =
    GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ)
  set g : WOF F E nS nT → ℂ := fun v => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * v) with hg
  have h1 : ∀ v : WOF F E nS nT, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)
      (dC (AF F ⊗[F] E) nT * v) = g (v + u) := by
    intro v
    simp only [hg, GlobalTheory.WeilSchrodinger.thetaTr, Darboux.rho]
    rw [schr_dC]
  have h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v := by
    rintro ⟨r, γ, rfl⟩ v
    obtain ⟨y, z, hyz⟩ := hco (dC E nT * γ)
    have hr : ((incAF F E).toAddMonoidHom.mapMatrix γ : WOF F E nS nT) = γ.map (incAF F E) := rfl
    show GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * (_ + v)) = _
    simp only [hg, GlobalTheory.WeilSchrodinger.thetaTr, Darboux.rho]
    rw [← schr_dC, hr, dC_mul_rat, hyz, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hB.std.2.1 y z]
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : MeasurableAdd (WOF F E nS nT) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  haveI : MeasurableConstVAdd (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun r => (continuous_const_add (r : WOF F E nS nT)).measurable⟩
  haveI : VAddInvariantMeasure (ratLF F E nS nT) (WOF F E nS nT) ν :=
    ⟨fun r s _ => measure_preimage_add ν (r : WOF F E nS nT) s⟩
  haveI : VAddCommClass (WOF F E nS nT) (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun a r x => add_left_comm a (r : WOF F E nS nT) x⟩
  haveI : Countable (ratLF F E nS nT) := by
    haveI : Countable E := by
      haveI : FiniteDimensional ℚ E := inferInstance
      exact ((Module.finBasis ℚ E).equivFun).injective.countable
    have : Countable (Matrix (Fin nT) (Fin nS) E) := inferInstanceAs (Countable (Fin nT → Fin nS → E))
    exact (Set.countable_range ((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS))).to_subtype
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [h1]
  rw [← (measurePreserving_add_right ν u).setIntegral_image_emb (measurableEmbedding_addRight u) g 𝓕]
  have hF' : IsAddFundamentalDomain (ratLF F E nS nT) ((· + u) '' 𝓕) ν := by
    have hs : (· + u) '' 𝓕 = ((u : WOF F E nS nT) +ᵥ 𝓕 : Set (WOF F E nS nT)) := by
      rw [← Set.image_vadd]
      congr 1
      funext v
      exact add_comm v u
    rw [hs]
    exact h𝓕.vadd_of_comm (G' := WOF F E nS nT) (u : WOF F E nS nT)
  exact hF'.setIntegral_eq h𝓕 h2
