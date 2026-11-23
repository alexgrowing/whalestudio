import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormRationality
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockNormMinorProductDeltaAtEmbeddingPos
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RenamedMinors

variable {D : D7} {S T : HSp D}

def phi (C : Ctx S T) : MvPolynomial (FVar D T.rank S.rank) ℂ →ₐ[ℂ] Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank) :=
  C.toH.comp (MvPolynomial.rename fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2))

theorem phi_varF_pos (C : Ctx S T) (τ : D.what₂.Tau) (b a : ℕ) (hb : b < C.X.p0) (ha : a < S.rank) :
    phi C (varF τ b a) = MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) *
      MvPolynomial.X (C.m.e τ, Sum.inr ⟨b, hb⟩, ⟨a, ha⟩) := by
  have hr := C.hr
  have hbm : b < T.rank := by omega
  rw [varF, dif_pos ⟨hbm, ha⟩, phi, AlgHom.comp_apply, MvPolynomial.rename_X, Ctx.toH, MvPolynomial.aeval_X]
  congr 2
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  dsimp only
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [rowIdx_inr]
  simp only [revPos]
  rw [dif_pos ⟨hb, by omega⟩]

theorem phi_varF_neg (C : Ctx S T) (τ : D.what₂.Tau) (b a : ℕ) (hb : b < C.q0) (ha : a < S.rank) :
    phi C (varF τ (C.X.p0 + b) a) = MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) *
      MvPolynomial.X (C.m.e τ, Sum.inl ⟨b, hb⟩, ⟨a, ha⟩) := by
  have hr := C.hr
  have hbm : C.X.p0 + b < T.rank := by omega
  rw [varF, dif_pos ⟨hbm, ha⟩, phi, AlgHom.comp_apply, MvPolynomial.rename_X, Ctx.toH, MvPolynomial.aeval_X]
  congr 2
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  dsimp only
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [rowIdx_inl]
  simp only [revPos]
  rw [dif_neg (by simp)]

theorem phi_minorPlus (C : Ctx S T) (hle : C.X.p0 ≤ S.rank) (τ : D.what₂.Tau) (i : Fin C.X.p0) :
    phi C (minorPlus τ (i.val + 1)) = MvPolynomial.C ((((2 / fockScale D τ : ℝ) : ℂ)) ^ (i.val + 1)) *
      Harm.yMinor (C.m.e τ) i (fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)) := by
  rw [minorPlus, AlgHom.map_det, Harm.yMinor]
  have h : (phi C).mapMatrix (Matrix.of fun α β : Fin (i.val + 1) =>
      (varF τ β α : MvPolynomial (FVar D T.rank S.rank) ℂ)) =
      (MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) : Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)) • (Matrix.of fun a b : Fin (i.val + 1) =>
        (Harm.yForm (C.m.e τ) (Harm.lead i a)
          ((fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)) (Harm.lead i b)) :
            Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)))ᵀ := by
    ext α β
    have hβ : (β : ℕ) < C.X.p0 := by have := β.2; have := i.2; omega
    have hα : (α : ℕ) < S.rank := by have := α.2; have := i.2; omega
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul]
    rw [phi_varF_pos C τ β α hβ hα, Harm.yForm_single]
    rfl
  rw [h, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin, ← map_pow]

theorem phi_minorMinus (C : Ctx S T) (hn : T.rank ≤ S.rank) (τ : D.what₂.Tau) (i : Fin C.q0) : ∃ κ : ℂ,
    phi C (minorMinus τ C.X.p0 (i.val + 1)) = MvPolynomial.C κ *
      Harm.xMinor (C.m.e τ) i (fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
        have := C.hr; have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)) := by
  have hr := C.hr
  have hi := i.2
  rw [minorMinus, AlgHom.map_det, Harm.xMinor]
  have h : (phi C).mapMatrix (Matrix.of fun α β : Fin (i.val + 1) =>
      (varF τ (C.X.p0 + β) (S.rank - (i.val + 1) + α) : MvPolynomial (FVar D T.rank S.rank) ℂ)) =
      ((MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) : Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)) • (Matrix.of fun a b : Fin (i.val + 1) =>
        (Harm.xForm (C.m.e τ) (Harm.lead i a)
          ((fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
            have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)) (Harm.lead i b)) :
            Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)))ᵀ).submatrix Fin.revPerm id := by
    ext α β : 1
    have hβ : (β : ℕ) < C.q0 := by have := β.2; omega
    have hα : S.rank - (i.val + 1) + (α : ℕ) < S.rank := by have := α.2; omega
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul, Matrix.submatrix_apply, id]
    rw [phi_varF_neg C τ β _ hβ hα, Harm.xForm_single]
    have := α.2
    congr 1
    exact congrArg _ (Prod.ext rfl (Prod.ext rfl (Fin.ext (by
      simp only [Harm.lead, Fin.coe_castLE, Fin.revPerm_apply, Fin.val_rev]
      omega))))
  refine ⟨((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (i.val + 1))) : ℤ) : ℂ) *
    (((2 / fockScale D τ : ℝ) : ℂ)) ^ (i.val + 1), ?_⟩
  rw [h, Matrix.det_permute, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  simp only [map_mul, map_pow, map_intCast]
  ring

theorem prod_range_pow_eq {σ : Type} (N : ℕ) (g : ℕ → MvPolynomial σ ℂ) (h : Fin N → MvPolynomial σ ℂ) (d : ℕ → ℕ)
    (hg : ∀ i : Fin N, ∃ κ : ℂ, g i = MvPolynomial.C κ * h i) :
    ∃ κ : ℂ, ∏ i ∈ Finset.range N, g i ^ d i = MvPolynomial.C κ * ∏ i : Fin N, h i ^ d i := by
  choose κ hκ using hg
  refine ⟨∏ i : Fin N, κ i ^ d i, ?_⟩
  rw [← Fin.prod_univ_eq_prod_range (fun i => g i ^ d i), map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hκ i, mul_pow, map_pow]

theorem phi_delta (C : Ctx S T) (hn : T.rank ≤ S.rank) (ap am : D.what₂.Tau → ℕ → ℕ) : ∃ κ : ℂ,
    phi C (delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am) =
      MvPolynomial.C κ * Harm.minorProd
        (fun σ (i : Fin C.q0) => am (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.q0 then am (C.m.e.symm σ) (i + 1) else 0)
        (fun σ (i : Fin C.X.p0) => ap (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.X.p0 then ap (C.m.e.symm σ) (i + 1) else 0)
        (fun _ (a : Fin C.q0) => (Pi.single (⟨S.rank - 1 - a, by
          have := C.hr; have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ))
        (fun _ (b : Fin C.X.p0) => (Pi.single (Fin.castLE (by have := C.hr; omega) b) (1 : ℂ) : Fin S.rank → ℂ)) := by
  have hr := C.hr
  have hle : C.X.p0 ≤ S.rank := by omega
  have hτ : ∀ τ : D.what₂.Tau, ∃ κ : ℂ, phi C (deltaAt (m := T.rank) (n := S.rank) τ C.X.p0 (ap τ) C.q0 (am τ)) =
      MvPolynomial.C κ *
        ((∏ i : Fin C.q0, Harm.xMinor (C.m.e τ) i (fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
            have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)) ^
            (am τ i - if (i : ℕ) + 1 < C.q0 then am τ (i + 1) else 0)) *
          ∏ i : Fin C.X.p0, Harm.yMinor (C.m.e τ) i
            (fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)) ^
            (ap τ i - if (i : ℕ) + 1 < C.X.p0 then ap τ (i + 1) else 0)) := by
    intro τ
    rw [deltaAt, map_mul, map_prod, map_prod]
    simp only [map_pow]
    obtain ⟨κ1, h1⟩ := prod_range_pow_eq C.X.p0 (fun i => phi C (minorPlus τ (i + 1)))
      (fun i : Fin C.X.p0 => Harm.yMinor (C.m.e τ) i
        (fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)))
      (fun i => ap τ i - if i + 1 < C.X.p0 then ap τ (i + 1) else 0)
      (fun i => ⟨_, phi_minorPlus C hle τ i⟩)
    obtain ⟨κ2, h2⟩ := prod_range_pow_eq C.q0 (fun i => phi C (minorMinus τ C.X.p0 (i + 1)))
      (fun i : Fin C.q0 => Harm.xMinor (C.m.e τ) i (fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
            have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)))
      (fun i => am τ i - if i + 1 < C.q0 then am τ (i + 1) else 0)
      (fun i => phi_minorMinus C hn τ i)
    refine ⟨κ1 * κ2, ?_⟩
    rw [h1, h2, map_mul]
    ring
  choose κ hκ using hτ
  refine ⟨∏ τ, κ τ, ?_⟩
  rw [delta, map_prod, Finset.prod_congr rfl (fun τ _ => hκ τ), Finset.prod_mul_distrib, ← map_prod, Harm.minorProd]
  congr 1
  exact Fintype.prod_equiv C.m.e _ _ (fun τ => by simp only [Equiv.symm_apply_apply])

end GlobalTheory.RenamedMinors

open GlobalTheory.RenamedMinors in

theorem GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (ap am : D.what₂.Tau → ℕ → ℕ), ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ), C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ∈ Harm.rowHighest ℂ c c' ∧ C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ≠ 0 := by
  intro D S T C hn ap am
  have hr := C.hr
  obtain ⟨κ, hκ⟩ := phi_delta C hn ap am
  refine ⟨fun σ (i : Fin C.q0) => am (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.q0 then am (C.m.e.symm σ) (i + 1) else 0,
    fun σ (i : Fin C.X.p0) => ap (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.X.p0 then ap (C.m.e.symm σ) (i + 1) else 0,
    ?_, ?_⟩
  · change phi C _ ∈ _
    rw [hκ, ← MvPolynomial.smul_eq_C_mul]
    refine Submodule.smul_mem _ κ (Harm.minorProd_mem_rowHighest _ _ fun t a b => ?_)
    rw [single_dotProduct, one_mul, Pi.single_apply, if_neg]
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.coe_castLE] at h'
    have := a.2
    have := b.2
    omega
  · change phi C _ ≠ 0
    have hf : Function.Injective fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2) :=
      Function.LeftInverse.injective (g := fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2))
        fun v => by simp only [revPos_revPos]
    have hinj : Function.Injective (phi C) := C.toH_bijective.1.comp (MvPolynomial.rename_injective _ hf)
    exact (map_ne_zero_iff (phi C) hinj).2 (GlobalTheory.FockDelta.delta_ne_zero _ _ _ _ (fun _ => by omega) hn)

end
