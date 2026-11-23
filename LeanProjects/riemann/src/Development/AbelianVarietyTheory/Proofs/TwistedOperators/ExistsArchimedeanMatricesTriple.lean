import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.FockFirst

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j

  change infEmb τ (compInf F E w ((1 : AF F) ⊗ₜ[F] J i j)) = τ.1 (J i j)
  simp [compInf, infEmb_tmul]

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_

  have h0 : piInf (τ w) (z : AE F E) ≠ 0 := (z.isUnit.map (piInf (τ w))).ne_zero
  have hne : piInf (τ w) (z : AE F E) / (‖piInf (τ w) (z : AE F E)‖ : ℂ) ≠ 0 :=
    div_ne_zero h0 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0))
  rw [zpow_sub₀ hne]

end SlopeTestRemainingChoices

theorem exists_fockMap_first (hP : GlobalTheory.FunPr.Hypotheses₂) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (h : IsTriple B G X om om') :
    ∃ (A : InfinitePlace F → Matrix (Fin a) (Ix (a - G.p) G.p) ℂ)
      (Φ : Tens F (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')))
      (c : InfinitePlace F → ℂ),
      (∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w)) ∧
      (∀ w, G.V.θ w * A w = A w * Jm (a - G.p) G.p) ∧
      LinearMap.range Φ = G.M.Pol B.ψ B.emb ∧
      ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (fockAct1 (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q)) c := by
  obtain ⟨hbase, hgeo, hchars, hweil, -⟩ := h

  have hDer := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hFock := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hDer
  have hVac := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hDer
  have hPol := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws actsLaws hDer hVac
  have hFirst :=
    LieFirstPf.lieFirst_of_lieSecond (GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar hP hDer hFock hVac (GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hP hDer hVac))

  have hA : ∀ w, ∃ A : Matrix (Fin a) (Ix (a - G.p) G.p) ℂ,
      IsFrame (G.V.J.map (B.emb w).1) A ∧ G.V.θ w * A = A * Jm (a - G.p) G.p :=
    fun w => frameEx_holds _ _ _ _ _ (hgeo.hV.sig w) (hgeo.hV.cartan w)
  choose A hAf hAθ using hA
  have hC : ∀ w, ∃ C : Matrix (Fin (a + a')) (Ix (a + a' - (G.p + G.q)) (G.p + G.q)) ℂ,
      IsFrame (Complex.I • G.W.J.map (B.emb w).1) C ∧
        G.W.θ w * C = C * Jm (a + a' - (G.p + G.q)) (G.p + G.q) :=
    fun w => frameEx_holds _ _ _ _ _ (hgeo.hW.sig w) (hgeo.hW.cartan w)
  choose C hCf hCθ using hC
  have hFr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := by
    refine ⟨one_mul _, fun w => ?_, fun w => ?_⟩
    · rw [incM_map_piInf, one_smul]
      exact hAf w
    · rw [incM_map_piInf]
      exact hCf w
  obtain ⟨Φ, hΦ⟩ := hFock F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hbase.cm hbase.std hFr
  have hRange : LinearMap.range Φ = G.M.Pol B.ψ B.emb :=
    hPol F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hbase.cm hbase.std hFr hAθ hCθ hΦ

  obtain ⟨-, ⟨d', hd', hB⟩, -⟩ := hweil
  have hActs := hFirst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d' 1 Complex.I A C Φ _ _ _ hbase.cm hbase.std
    hFr hΦ hd' hB (hasExp_div B.emb hchars.expβ hchars.expα)
  exact ⟨A, Φ, _, hFr.2.1, hAθ, hRange, hActs⟩

end GlobalTheory.RealLift.FockFirst

end
