import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaLiftTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseGoodStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKReV

theorem nonzero_of_reG : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')), IsTriple B G X om om' →
    IsTriple B (reG G V V' W) X om om' → G.p = 0 → (∃ Φ ∈ PolData B (reG G V V' W).M, (reG G V V' W).M.I om Φ ≠ 0) →
    ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' V V' W hT hT' _ hex
  obtain ⟨Φ₀, hΦ₀, hne⟩ := hex
  by_contra hcon
  push_neg at hcon
  apply hne
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hWc := GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP
    (Or.inl (GlobalTheory.ThK.Check.conv_range hT.geo))
  have hpres := (IsUWeilPair.isUSplitting hT.weil).pres
  have hconv : ∀ Φ ∈ schA F (Fin a × Fin (a + a')), G.M.Conv om Φ := fun Ψ hΨ => (hWc.1 Ψ hΨ).1
  have hD : Dense ((G.M.Pol B.ψ B.emb : Submodule ℂ (SInf F (Fin a × Fin (a + a')))) : Set (SInf F (Fin a × Fin (a + a')))) :=
    GlobalTheory.T.polynomial_fock_dense_good F E σ B a (a + a') G.V G.W G.M _ _ _ _ hT.base hT.geo.hV hT.geo.hW
  have hgen : ∀ (f : SInf F (Fin a × Fin (a + a'))) φ, GlobalTheory.BigNZ.Fam G.M φ →
      G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = 0 := by
    intro f φ hφ
    funext h
    have hc := hWc.2 _ (hφ.sb hT.geo.hM) h
    have e := Continuous.ext_on hD hc continuous_const (fun f' hf' => by
      have hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ ∈ PolData B G.M := Submodule.subset_span ⟨f', hf', φ, hφ.1, hφ.2, rfl⟩
      exact congrFun (hcon _ hm) h)
    exact congrFun e f
  have hS : ∀ Φ ∈ PolData B (reG G V V' W).M, Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun Φ hΦ => GlobalTheory.ThK.SqIntCont.polData_le_schA hT'.geo.hM hΦ
  have key : ∀ Φ (hΦ : Φ ∈ PolData B (reG G V V' W).M), G.M.I om Φ = 0 := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, -, φ, h1, h2, rfl⟩ := hx
      exact hgen f φ ⟨h1, h2⟩
    | zero =>
      funext h
      simp [Model.I, theta, thetaSum]
    | add x y hx hy ihx ihy =>
      funext h
      have ex := congrFun ihx h
      have ey := congrFun ihy h
      simp only [Model.I, Pi.zero_apply] at ex ey ⊢
      rw [integral_congr_ae (Filter.Eventually.of_forall fun g =>
        GlobalTheory.ThK.SqIntCont.theta_add om hpres (hS x hx) (hS y hy) g h),
        integral_add (hconv _ (hS x hx) h) (hconv _ (hS y hy) h), ex, ey, add_zero]
    | smul c x hx ih =>
      funext h
      have ex := congrFun ih h
      simp only [Model.I, Pi.zero_apply] at ex ⊢
      simp only [GlobalTheory.ThK.SqIntCont.theta_smul, integral_const_mul, ex, mul_zero]
  exact key Φ₀ hΦ₀

end GlobalTheory.ThKReV
