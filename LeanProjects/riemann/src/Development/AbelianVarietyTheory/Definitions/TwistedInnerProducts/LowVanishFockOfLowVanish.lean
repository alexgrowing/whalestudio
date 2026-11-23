import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.Size GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped ENNReal ComplexOrder

namespace GlobalTheory.ChainFr.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_sign_frame {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian) (hu : IsUnit G.det) :
    ∃ (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsUnit A ∧ Aᴴ * Formalism.REAL.Jm ε * A = G := by
  classical
  have hne : ∀ i, hG.eigenvalues i ≠ 0 := by
    intro i h0
    apply hu.ne_zero
    rw [hG.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])
  set U : Matrix (Fin n) (Fin n) ℂ := (hG.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hsp : G = U * diagonal (fun i => ((hG.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hG.spectral_theorem]
    simp [hU, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def]
  let d : Fin n → ℂ := fun i => ((Real.sqrt |hG.eigenvalues i| : ℝ) : ℂ)
  refine ⟨fun i => decide (0 < hG.eigenvalues i), diagonal d * Uᴴ, ?_, ?_⟩
  · refine IsUnit.mul ?_ ?_
    · rw [isUnit_diagonal, Pi.isUnit_iff]
      intro i
      simp [d, hne i]
    · have : Uᴴ * U = 1 := by
        rw [hU, ← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
      exact IsUnit.of_mul_eq_one _ this
  · have key : (diagonal d)ᴴ * Formalism.REAL.Jm (fun i => decide (0 < hG.eigenvalues i)) * diagonal d =
        diagonal (fun i => ((hG.eigenvalues i : ℝ) : ℂ)) := by
      rw [diagonal_conjTranspose, Formalism.REAL.Jm, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      have hs : d i * d i = ((|hG.eigenvalues i| : ℝ) : ℂ) := by
        simp only [d]; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
      have hst : star d i = d i := by simp [d]
      rw [hst]
      by_cases h : 0 < hG.eigenvalues i
      · simp only [h, decide_true, if_true, mul_one, hs, abs_of_pos h]
      · simp only [h, decide_false, Bool.false_eq_true, if_false, mul_neg, mul_one, neg_mul, hs,
          abs_of_nonpos (not_lt.1 h)]
        simp
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    conv_rhs => rw [hsp, ← key]
    simp only [Matrix.mul_assoc]

theorem nonempty_fr (V : HSp D) : Nonempty (Fr V) := by
  choose ε A hA hG using fun τ => exists_sign_frame (G := gramAt D V τ)
    (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  exact ⟨⟨ε, A, hA, hG⟩⟩

theorem isCartanInv_cart {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) (A.cart τ) := by
  have hd := (isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hJ := Formalism.REAL.Jm_mul_self (A.ε τ)
  have hJc := Formalism.REAL.Jm_conjTranspose (A.ε τ)
  have hJJ : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, Formalism.REAL.Jm (A.ε τ) * (Formalism.REAL.Jm (A.ε τ) * X) = X :=
    fun X => by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have h1 : A.fr τ * A.cart τ = Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
    simp only [Fr.cart, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have h2 : gramAt D V τ * A.cart τ = (A.fr τ)ᴴ * A.fr τ := by
    rw [← A.fr_gram τ, Matrix.mul_assoc, h1, Matrix.mul_assoc, hJJ]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fr.cart, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ, Matrix.nonsing_inv_mul _ hd]
  · rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_mul, hJc, A.fr_gram]
  · rw [h2]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 (A.fr_unit τ))

theorem exists_vac {V W : HSp D} (A : Fr V) (B : Fr W) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) :
    ∃ f, f ≠ 0 ∧ IsVacF ψ θ A B f ∧ ptF ψ θ A B f 1 = f ∧
      ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ f ∈ fockSpan ψ θ A B U := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ V W _ _ (isCartanInv_cart A) (isCartanInv_cart B) _ _
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame _) (GlobalTheory.PlaceModel.isSelfDualC_latFrame _)
  have h : IsVacF ψ θ A B f := ⟨by simpa using (hf 1).1, by simpa using (hf 1).2.2⟩
  have e : ptF ψ θ A B f 1 = f := by
    have h1 : (1 : PolF D W.rank V.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]; rfl
    unfold ptF pureTensorO pureTensorL
    rw [h1, Module.Basis.constr_basis]
    simp [opPow]
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 h.1
  exact ⟨f, f0, h, e, U, hU, Submodule.subset_span ⟨f, 1, h, hl, e.symm⟩⟩

theorem dense_hyp (V W : HSp D) : ∃ (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (f : WO V W → ℂ), IsStdChar D ψ (-1) ∧ IsInfFam θ ∧
      IsCovolOne (ratL W V) μ 𝓕 ∧ f ≠ 0 ∧ IsVacF ψ θ A B f := by
  obtain ⟨⟨θ, hθ⟩, ψ, hψ⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨A⟩ := nonempty_fr V
  obtain ⟨B⟩ := nonempty_fr W
  obtain ⟨μ, 𝓕, hm⟩ := exists_isCovolOne V W
  obtain ⟨f, f0, hf, -⟩ := exists_vac A B hψ hθ
  exact ⟨A, B, θ, ψ, μ, 𝓕, f, hψ, hθ, hm, f0, hf⟩

theorem lieFock_of_all (h : LieFockAll D) {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')
    {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ} {τ : D.what₂.Tau} {aS aT : ℚ}
    (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hS : HasInfExp D χS τ aS) (hT : HasInfExp D χT τ aT)
    (hf : IsVacVec ψ θ M M' f) : LieFock ψ θ M M' ω f τ aS aT := by
  obtain ⟨h1, h2⟩ := h V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ aS aT hθ hω hS hT (isVacF_of_isVacVec hf)
  refine ⟨fun X hX P z => ?_, h2⟩
  have := h1 X hX P z
  rw [neg_smul, ← sub_eq_add_neg] at this
  exact this

theorem compactFock_of_all (h : CompactFockAll D) {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S)
    (M' : DSModel W S') {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ} {τ : D.what₂.Tau} {aS aT : ℚ}
    (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hS : HasInfExp D χS τ aS) (hT : HasInfExp D χT τ aT)
    (hf : IsVacVec ψ θ M M' f) : CompactFock ψ θ M M' ω f τ aS aT :=
  h V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ aS aT hθ hω hS hT (isVacF_of_isVacVec hf) hf.ne

theorem lowVanishFock_of_lowVanish (h : GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.LowVanish D) : LowVanishFock D := by
  intro k i V' W M' θ ψ hθ hP hi hs ω' hω ν 𝓕 hν h𝓕 J χ F hF v A f₀ hf P
  refine h k i V' W M' θ ψ hθ hP hi hs ω' hω ν 𝓕 hν h𝓕 J χ F hF v _ ?_
  obtain ⟨χS, χT, hW, -⟩ := hω
  exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hf.1 P

theorem fockS_offdiag (τ : D.what₂.Tau) :
    fockS τ ![true, false] ![true] (Matrix.single 0 1 1) (1 : PolF D 1 2) =
      -(MvPolynomial.X (τ, 0, 0) * MvPolynomial.X (τ, 0, 1)) ∧
    fockS τ ![true, false] ![true] (Matrix.single 1 0 1) (1 : PolF D 1 2) = 0 := by
  constructor <;> simp [fockS, raiO, lowO, sgn, Fin.sum_univ_two, Matrix.single_apply]

end GlobalTheory.ChainFr.Model

end
