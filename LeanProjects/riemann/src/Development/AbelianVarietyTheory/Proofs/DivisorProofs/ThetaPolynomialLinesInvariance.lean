import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUpdate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolStabInfW

open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.PolStabInf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open scoped Classical in

theorem polStab' : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    (∀ γ ∈ Lines σ G.V', ∀ f ∈ G.M'.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a' × Fin (a + a')),
      ActsD (evI F) (fun t => om' (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ G.M'.Pol B.ψ B.emb) ∧
    (∀ k ∈ KInf σ G.V' B.emb, ∀ f ∈ G.M'.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a' × Fin (a + a')),
      Acts (evI F) (om' (k, 1)) f f₁ → f₁ ∈ G.M'.Pol B.ψ B.emb) ∧
    (∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M'.Pol B.ψ B.emb, ∃ f₁ ∈ G.M'.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin a' × Fin (a + a')),
        ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁) ∧
    (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M'.Pol B.ψ B.emb, ∃ f₁ ∈ G.M'.Pol B.ψ B.emb,
      Acts (evI F) (om' (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (1, k)) f f₂ → f₂ = f₁) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' h
  obtain ⟨hb, hg, hc, -, hw⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hV'.sig w) (hg.hV'.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V'.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V'.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hD := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD
  have hfe := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hD
  have hsec := GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar hK.base hD hfe hvl (GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hK.base hD hvl)
  have hfst := GlobalTheory.T.lieFirst_of_lieSecond' hsec
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hD hvl F E σ _ _ _ _ _ _ G.V' G.W G.M' B.ψ B.emb A C Φ hb.cm hb.std fr
    hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A C Φ _ X.α B.mα hb.cm hb.std fr hΦ hwp.1
    hc.expα
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expα hc.expβ)
  have hadm := fun g => (hwp.isUSplitting).adm g
  have hL := GlobalTheory.RealLift.actsLaws
  have mem : ∀ T, Φ T ∈ G.M'.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  have pol : ∀ f ∈ G.M'.Pol B.ψ B.emb, ∃ T, f = Φ T := fun f hf => by
    rw [← hr] at hf
    obtain ⟨T, rfl⟩ := hf
    exact ⟨T, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ h1
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨Yg, -, hY⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin a') _ _ B.emb (incM F G.V'.J) 1 A hb.cm hA1 γ hγ
    have h2 := (hL F _ (Φ T) _ f₁).1 _ (fun t => map_zero _) (hW1 γ hγ Yg hY T)
    have e := (hL F _ (Φ T) _ f₁).2.2.1 _ h2 h1
    rw [← e]
    exact mem _
  · intro k hk f hf f₁ h1
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin a') _ _
      B.emb (incM F G.V'.J) 1 A G.V'.θ hb.cm hA1 hAθ k hk.1 hk.2
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F _ _ Φ _ ((om'.comp (MonoidHom.inl _ _)).comp γ)
      (GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w => locFin_fock1 _ _ _ _ (Yg w) (hKC w) _) (fun t l hl => hadm _ l hl)
      (fun T => hW1 γ hγ Yg hgen T)
    have h2 := (hL F _ (Φ T) (Φ (U T)) f₁).2.1 _ (map_zero _) (hSA T)
    rw [MonoidHom.comp_apply, hγ1] at h2
    have e := (hL F _ (Φ T) _ f₁).2.2.2.1 _ h2 h1
    rw [← e]
    exact mem _
  · intro γ hγ f hf
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨Yg, -, hY⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ
    have h2 := (hL F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Yg hY T)
    exact ⟨_, mem _, h2, fun f₂ h3 => (hL F _ (Φ T) _ _).2.2.1 _ h3 h2⟩
  · intro k hk f hf
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ
      (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C G.W.θ hb.cm hC1 hCθ k hk.1 hk.2
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F _ _ Φ _ ((om'.comp (MonoidHom.inr _ _)).comp γ)
      (GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w => locFin_fock2 _ _ _ _ (Yg w) (hKC w) _) (fun t l hl => hadm _ l hl)
      (fun T => hW2 γ hγ Yg hgen T)
    have h2 := (hL F _ (Φ T) (Φ (U T)) (Φ (U T))).2.1 _ (map_zero _) (hSA T)
    rw [MonoidHom.comp_apply, hγ1] at h2
    exact ⟨_, mem _, h2, fun f₂ h3 => (hL F _ (Φ T) _ _).2.2.2.1 _ h3 h2⟩

end GlobalTheory.PolStabInfW

end
