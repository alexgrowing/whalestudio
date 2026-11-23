import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLinesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolCompact

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf' {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem locFin_second (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

theorem exists_sa_of_mem_kInf (hP : GlobalTheory.FunPr.Hypotheses₂) {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hb : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hw : M.IsWeil B.ψ χX χW om) {k : UA σ W.J}
    (hk : k ∈ KInf σ W B.emb) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ f₁ ∈ M.Pol B.ψ B.emb, SA (om (1, k)) f f₁ := by
  have hfr : GlobalTheory.RealLift.FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists
  have hder : GlobalTheory.RealLift.DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl : GlobalTheory.RealLift.VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  have hfe : GlobalTheory.RealLift.FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hls : GlobalTheory.RealLift.LieScalar := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hP hder hvl
  have hpr : GlobalTheory.RealLift.PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.T.archActionReadings_compatible hder hvl
  have hkl : GlobalTheory.RealLift.KLine := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.T.unitaryLieElements_generate_oneParamLines
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf', one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf']; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hw
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _ hb.cm hb.std fr hΦ hwp.1.1
  have hadm := fun g => (hwp.isUSplitting).adm g
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ :=
    hkl F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C W.θ hb.cm hC1 hCθ k hk.1 hk.2
  have hloc := GlobalTheory.RealLift.locFin_sumPl _ _ _ (fun w => locFin_second r s r' s' (Yg w) (hKC w) (c w * (Yg w).trace))
  obtain ⟨U, -, hSA⟩ := GlobalTheory.T.weakExponential_action_on_fockVectors F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  rw [← hr] at hf ⊢
  obtain ⟨T, rfl⟩ := hf
  refine ⟨Φ (U T), LinearMap.mem_range_self Φ _, ?_⟩
  have h1 := hSA T
  rw [MonoidHom.comp_apply, hγ1] at h1
  exact h1

theorem polData_stable_kInf (hP : GlobalTheory.FunPr.Hypotheses₂) {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hb : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ) (hw : M.IsWeil B.ψ χX χW om) {k : UA σ W.J}
    (hk : k ∈ KInf σ W B.emb) {Φ : Fn F n d} (hΦ : Φ ∈ PolData B M) : om (1, k) Φ ∈ PolData B M := by
  have hle : PolData B M ≤ (PolData B M).comap (om (1, k)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, φ, hSB, hev, rfl⟩
    obtain ⟨f₁, hf₁, hsa⟩ := exists_sa_of_mem_kInf hP hb hX hW hw hk hf
    have hg := GlobalTheory.AdelicCoordSB.finprod_mem_SB F (Fin n × Fin d) φ hSB
      ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)
    have e : om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ := hsa _ hg
    change om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ PolData B M
    rw [e]
    exact Submodule.subset_span ⟨f₁, hf₁, φ, hSB, hev, rfl⟩
  exact hle hΦ

theorem polData_small_stable_kInf : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ k ∈ KInf σ G.W B.emb, ∀ Φ ∈ PolData B G.M', om' (1, k) Φ ∈ PolData B G.M' := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf h k hk Φ hΦ
  exact polData_stable_kInf hK.base h.triple.base h.triple.geo.hV' h.triple.geo.hW h.triple.geo.hM' h.triple.weil' hk hΦ

end GlobalTheory.PolCompact

end
