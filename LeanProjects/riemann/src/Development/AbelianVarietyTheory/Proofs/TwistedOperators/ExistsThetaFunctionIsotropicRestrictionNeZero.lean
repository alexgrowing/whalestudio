import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionEqUnitSmulOfDiagonalCoefficientEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerResNonzero

variable {D : D7}

theorem exists_right_inv {V : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hC : LinearIndependent D.host.E C.transpose) :
    ∃ N : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * N = 1 := by
  set P := adj D C * V.gram with hP
  have hinj : Function.Injective (Matrix.toLin' Pᵀ) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    rw [Matrix.toLin'_apply] at ha
    rw [Matrix.mulVec_transpose, hP, ← Matrix.vecMul_vecMul] at ha
    have hG := GlobalTheory.LatVac.gram_det_isUnit V
    have h1 : a ᵥ* adj D C = 0 := by
      have := congrArg (fun v => v ᵥ* V.gram⁻¹) ha
      simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at this
      rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one] at this
    have h2 : C *ᵥ star a = 0 := by
      have e : a ᵥ* adj D C = star (C *ᵥ star a) := by
        rw [Matrix.star_mulVec, star_star]; rfl
      rw [e] at h1
      exact star_eq_zero.1 h1
    have h3 : star a = 0 := by
      funext j
      refine Fintype.linearIndependent_iff.1 hC (star a) ?_ j
      funext i
      have := congrFun h2 i
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply, Pi.zero_apply] at this ⊢
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact star_eq_zero.1 h3
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Pᵀ) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(LinearMap.toMatrix' g)ᵀ, ?_⟩
  have e : LinearMap.toMatrix' g * Pᵀ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have := congrArg Matrix.transpose e
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem lattice_ratMx (D : D7) (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) ∧ LocallyCompactSpace (Mx D m n) ∧
    SecondCountableTopology (Mx D m n) ∧ T2Space (Mx D m n) ∧ DiscreteTopology (ratMx D m n) ∧
    ∃ K : Set (Mx D m n), IsCompact K ∧ ∀ x : Mx D m n, ∃ γ ∈ ratMx D m n, γ + x ∈ K :=
  GlobalTheory.AdelicMatrixLattice.lattice D (Examples₂.posSpace Examples₂.star_isIntegral m) (Examples₂.posSpace Examples₂.star_isIntegral n)

theorem isoPart_add' {V W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y y' : Mx D W.rank r) :
    isoPart V W C (y + y') = isoPart V W C y + isoPart V W C y' :=
  Matrix.add_mul _ _ _

theorem isoPart_zero' {V W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    isoPart V W C (0 : Mx D W.rank r) = 0 := Matrix.zero_mul _

theorem midPart_zero' {V V' W : HSp D} (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    midPart V V' W B (0 : WO V' W) = 0 := Matrix.zero_mul _

theorem isoPart_mem_iff {V W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hC : LinearIndependent D.host.E C.transpose) (y : Mx D W.rank r) :
    isoPart V W C y ∈ ratL W V ↔ y ∈ ratMx D W.rank r := by
  constructor
  · rintro ⟨Q, hQ⟩
    obtain ⟨N, hN⟩ := exists_right_inv (V := V) hC
    refine ⟨Q * N, ?_⟩
    change (Q * N).map (incA D) = y
    have hQ' : Q.map (incA D) = y * (adj D C * V.gram).map (incA D) := hQ
    rw [Matrix.map_mul, hQ', Matrix.mul_assoc, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.mul_one]
  · rintro ⟨γ₀, rfl⟩
    exact ⟨γ₀ * (adj D C * V.gram), by
      show (γ₀ * (adj D C * V.gram)).map (incA D) = _
      rw [Matrix.map_mul]; rfl⟩

theorem exists_res_ne_zero : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → (∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x') → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ f, IsThetaFunO ψ V W f ∧ res V V' W C B μ 𝓨 f ≠ 0 := by
  intro D V V' W r C B hs hF ψ hψ μ 𝓨 h
  obtain ⟨f₀, hf₀, hne₀⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ V W
  obtain ⟨x₀, hx₀⟩ : ∃ x, f₀ x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne₀ (funext hc)
  have hf₁ : IsThetaFunO ψ V W (heisO ψ V W x₀ f₀) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ x₀
  have h0 : heisO ψ V W x₀ f₀ 0 ≠ 0 := by
    simp only [heisO, zero_add, GlobalTheory.FinTranslate.symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]
    exact hx₀

  have hiso : ∀ y y' : Mx D W.rank r, symplOH V W (isoPart V W C y) (isoPart V W C y') = 0 := fun y y' => by
    have := hF y y' 0 0
    rwa [midPart_zero', add_zero, add_zero, GlobalTheory.FinTranslate.symplOH_zero_left] at this

  have hc : ∀ (g : WO V W → ℂ), IsThetaFunO ψ V W g → ∀ a ∈ ratL W V, ∀ z,
      heisO ψ V W a g z = ψ (symplO V W z a) * g z := by
    intro g hg a ha z
    have := GlobalTheory.ThetaCoefficient.char_mul_heisO hg ha 0 z
    simp only [heisO, GlobalTheory.FinTranslate.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one, one_mul] at this
    exact this.symm
  refine by_contra fun hall => ?_
  push_neg at hall
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_ratMx D W.rank r
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hcont : Continuous (isoPart V W C : Mx D W.rank r → WO V W) := continuous_id.matrix_mul continuous_const
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (Mx D W.rank r) (ratMx D W.rank r) K hK hKc
    (ratL W V) (fun a y => ψ (symplO V W (isoPart V W C y) a))
    (fun a => by
      simp only [GlobalTheory.ThetaCoefficient.symplO_eq]
      exact hψ.1.1.comp (((GlobalTheory.FinTranslate.continuous_symplOH V W _).comp hcont).add
        ((GlobalTheory.FinTranslate.continuous_symplOH V W _).comp hcont)))
    (fun a x y => by
      simp only [isoPart_add', GlobalTheory.ThetaCoefficient.symplO_eq, GlobalTheory.FinTranslate.symplOH_add_left,
        ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun a b x => by
      show ψ (symplO V W (isoPart V W C x) (a + b)) = _
      simp only [GlobalTheory.ThetaCoefficient.symplO_eq, GlobalTheory.FinTranslate.symplOH_add_right, ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun x => by
      show ψ (symplO V W (isoPart V W C x) 0) = 1
      rw [GlobalTheory.ThetaCoefficient.symplO_eq, GlobalTheory.FinTranslate.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun a x => hψ.1.2.1 _)
    (fun y => by
      rw [← isoPart_mem_iff hs.frame.2.1 y, ← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W]
      exact Subtype.forall)
    μ 𝓨 h.1 h.2.1 (fun y => heisO ψ V W x₀ f₀ (isoPart V W C y)) (hf₁.cont.comp hcont)
    (fun γ hγ y => by
      obtain ⟨γ₀, hγ₀⟩ := (isoPart_mem_iff (V := V) hs.frame.2.1 γ).2 hγ
      have e := hf₁.quasi γ₀ (isoPart V W C y)
      change ratW W V γ₀ = isoPart V W C γ at hγ₀
      rw [hγ₀, hiso, neg_zero, AddChar.map_zero_eq_one, one_mul] at e
      simp only [isoPart_add']
      exact e)
    (fun a => by
      have e := congrFun (hall _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₁ (a : WO V W))) 0
      simp only [res, midPart_zero', add_zero, Pi.zero_apply] at e
      rw [← e]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hc _ hf₁ a a.2 _).symm))
  have := congrFun key 0
  simp only [isoPart_zero', Pi.zero_apply] at this
  exact h0 this

end GlobalTheory.TowerResNonzero

end
