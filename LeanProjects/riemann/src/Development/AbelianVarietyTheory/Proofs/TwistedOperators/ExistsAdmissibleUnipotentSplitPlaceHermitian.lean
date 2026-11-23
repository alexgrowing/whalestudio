import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualPairIsUnitDetBlocksStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBigCellExistsAdmissibleInverseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSelfDualLatticeSplitPlaceDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSkewElementUnitAtFinitePlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitChooseHerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def scaleSpc {d : ℕ} (V : Spc F E d) (δ : E) : Spc F E d where
  J := δ • V.J
  L := V.L
  θ := V.θ
  bas := V.bas

theorem incM_smul {d : ℕ} (δ : E) (J : Matrix (Fin d) (Fin d) E) :
    incM F (δ • J) = inclR (F := F) (AF F) δ • incM F J := by
  ext i j
  simp [incM, Matrix.map_apply, Matrix.smul_apply, map_mul]

theorem dbl_smul {d : ℕ} (c : AE F E) (X : Matrix (Fin d) (Fin d) (AE F E)) : dbl (c • X) = c • dbl X := by
  simp [dbl, Matrix.fromBlocks_smul, smul_neg]

end GlobalTheory.SplitChooseHerm

namespace GlobalTheory.SplitChooseHerm

theorem exists_admissible_unipotent_split_place_hermitian : (∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ V v,
      ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt V v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt V v) ∧
        Yᵀ * incM F V.J + incM F V.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt V v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt V v := by
  intro _ F E _ _ _ _ _ σ B d V r s hB hV v hv hψ h2 g hg
  obtain ⟨π₁, π₂, b₁, b₂, hP, S, hS, hSe⟩ := GlobalTheory.T.hermitian_selfDual_lattice_split_place_dictionary σ B V r s hB hV v hv hψ
  obtain ⟨δ, hδ, u, hu⟩ := GlobalTheory.T.exists_cmSkew_element_unit_at_finitePlace σ hB.cm v π₁ hP.2.2.1
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h0 : ((u : v.adicCompletionIntegers F) : Fv F v) = 0 := by rw [hu, map_zero, map_zero]
    exact u.ne_zero (Subtype.ext h0)
  have hcu : inclR (F := F) (AF F) δ⁻¹ * inclR (F := F) (AF F) δ = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hδ0, map_one]
  have h2' : IsUnit (2 : v.adicCompletionIntegers F) := by
    have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (2 : 𝓞 F)).2 h2
    rwa [map_ofNat] at this
  let W' : Spc F E d := scaleSpc V δ
  have hskew : ∀ i j, σ (W'.J j i) = -W'.J i j := by
    intro i j
    show σ (δ * V.J j i) = -(δ * V.J i j)
    rw [map_mul, hδ, hV.herm]
    ring
  have hS' : ∃ S' : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S'.det ∧
      S'.map (fun x => (x : Fv F v)) =
        (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W'.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
    refine ⟨(u : v.adicCompletionIntegers F) • S, ?_, ?_⟩
    · rw [Matrix.det_smul]
      exact (u.isUnit.pow _).mul hS
    · have e1 : (incM F W'.J).map π₁ = π₁ (inclR (F := F) (AF F) δ) • (incM F V.J).map π₁ := by
        show (incM F (δ • V.J)).map π₁ = _
        rw [incM_smul]
        ext i j
        simp [Matrix.map_apply, Matrix.smul_apply]
      rw [e1, Matrix.mul_smul, Matrix.smul_mul, ← hSe, ← hu]
      ext i j
      simp [Matrix.map_apply, Matrix.smul_apply]
  let g' : GlobalTheory.DblVac.UD σ W' := ⟨g.1, by
    have h := g.2
    change ((g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)))ᵀ * dbl (incM F V.J) *
      (g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F V.J) at h
    change ((g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)))ᵀ * dbl (incM F (δ • V.J)) *
      (g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F (δ • V.J))
    rw [incM_smul, dbl_smul, Matrix.mul_smul, Matrix.smul_mul, h]⟩
  have hg' : g' ∈ GlobalTheory.DblVac.KD σ W' v := hg
  obtain ⟨Y, hYat, hYlat, hYadm, M, hM, hMlat⟩ :=
    GlobalTheory.T.splitPlace_bigCell_exists_admissible_inverse_alt GlobalTheory.T.exists_dual_pair_isUnit_det_blocks' σ W' v hskew h2' π₁ π₂ b₁ b₂ hP hS' g' hg'
  refine ⟨Y, hYat, hYlat, ?_, M, hM, hMlat⟩
  change Yᵀ * incM F (δ • V.J) + incM F (δ • V.J) * Y.map (cA σ) = 0 at hYadm
  rw [incM_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_add] at hYadm
  have h3 := congrArg (fun X => inclR (F := F) (AF F) δ⁻¹ • X) hYadm
  simp only [smul_smul, hcu, one_smul, smul_zero] at h3
  exact h3

end GlobalTheory.SplitChooseHerm
