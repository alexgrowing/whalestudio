import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFourierIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationRankLeDim
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFourierIdentityStatement

section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.HoweGlobal.RealTransfer
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealActs
theorem howe_real_place_transfer : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    Module.rank ℂ ↥(G.M.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobal.relInf Bs G om ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobal.relInf Bs G om ≤ N →
        (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ →
        N ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobal.relInf Bs G om ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype),
      g x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal
  have hPair := GlobalTheory.ThK.RealUniq.isPair_V hM.triple
  have PA : PolActs Bs G.M om := _root_.GlobalTheory.T.dualPair_preserves_polarization hP F E σ Bs _ _ _ _ G.M _ _ om _ _ _ _ hPair
  set P := G.M.Pol Bs.ψ Bs.emb with hPdef
  have key : ∀ N : Submodule ℂ ↥P, relInf Bs G om ≤ N → (∀ g ∈ opInf Bs G om, ∀ x ∈ N, g x ∈ N) →
      GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N.map P.subtype) := by
    intro N hrel hop
    refine ⟨Submodule.map_subtype_le _ _, ?_, ?_, ?_, ?_⟩
    · intro γ hγ f hf f₁ hA
      obtain ⟨D, hDP, hD⟩ := PA.1 γ hγ
      have e : f₁ = D f := (hD f hf f₁).1 hA
      have h1 : f₁ ∈ P := e ▸ hDP f hf
      refine ⟨⟨f₁, h1⟩, hrel (Submodule.subset_span (Or.inl ⟨γ, hγ, f, hf, hA⟩)), rfl⟩
    · intro k hk f hf f₁ hA
      obtain ⟨D, hDP, hD⟩ := PA.2.1 k hk
      have e : f₁ = D f := (hD f hf f₁).1 hA
      have h1 : f₁ ∈ P := e ▸ hDP f hf
      refine ⟨⟨f₁, h1⟩ - ⟨f, hf⟩, hrel (Submodule.subset_span (Or.inr ⟨k, hk, ⟨f, hf⟩, ⟨f₁, h1⟩, hA, rfl⟩)), rfl⟩
    · intro γ hγ f hf f₁ hA
      obtain ⟨y, hy, rfl⟩ := hf
      obtain ⟨D, hDP, hD⟩ := PA.2.2.1 γ hγ
      let g : Module.End ℂ ↥P := D.restrict hDP
      have hg : g ∈ opInf Bs G om := Or.inr ⟨γ, hγ, fun f => (hD f f.2 _).2 rfl⟩
      have e : f₁ = D y := (hD y y.2 f₁).1 hA
      exact ⟨g y, hop g hg y hy, e.symm⟩
    · intro k hk f hf f₁ hA
      obtain ⟨y, hy, rfl⟩ := hf
      obtain ⟨D, hDP, hD⟩ := PA.2.2.2 k hk
      let g : Module.End ℂ ↥P := D.restrict hDP
      have hg : g ∈ opInf Bs G om := Or.inl ⟨k, hk, fun f => (hD f f.2 _).2 rfl⟩
      have e : f₁ = D y := (hD y y.2 f₁).1 hA
      exact ⟨g y, hop g hg y hy, e.symm⟩
  have hinj : Function.Injective (Submodule.map P.subtype) :=
    Submodule.map_injective_of_injective P.injective_subtype
  have hne : ∀ N : Submodule ℂ ↥P, N ≠ ⊤ → N.map P.subtype ≠ P := by
    intro N hN h
    apply hN
    apply hinj
    rw [h, Submodule.map_subtype_top]
  refine ⟨_root_.GlobalTheory.T.polarization_rank_le_dim hP F E σ Bs _ _ _ _ G.M _ _ om _ _ _ _ hPair, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hreal.1
    refine ⟨L, fun m N hN hN' => hL m (fun i => (N i).map P.subtype)
      ((Submodule.map_strictMono_of_injective P.injective_subtype).comp hN) fun i => key _ (hN' i).1 (hN' i).2⟩
  · intro N hrel hop hN x hx
    exact hreal.2 _ (key N hrel hop) (hne N hN) x ⟨x, hx, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro x (⟨γ, hγ, f, hf, hA⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)
    · exact hM.real.quot.lie γ hγ f hf _ hA
    · show R.p (((f₁ - f : ↥P)) : SInf F _) = 0
      rw [Submodule.coe_sub, map_sub, hM.real.quot.cpt k hk f f.2 f₁ hA, sub_self]
  · intro g hg x hx
    have hx' : R.p (x : SInf F _) = 0 := hx
    show R.p ((g x : ↥P) : SInf F _) = 0
    rcases hg with ⟨k, hk, hA⟩ | ⟨γ, hγ, hA⟩
    · have := hM.real.cpt k hk x x.2 0 (G.M'.Pol Bs.ψ Bs.emb).zero_mem _ 0 (hA x)
        (GlobalTheory.ThK.RealUniq.acts_zero _) (by rw [hx', map_zero])
      rw [this, map_zero]
    · have := hM.real.lie γ hγ x x.2 0 (G.M'.Pol Bs.ψ Bs.emb).zero_mem _ 0 (hA x)
        (GlobalTheory.ThK.RealUniq.actsD_zero _) (by rw [hx', map_zero])
      rw [this, map_zero]
end GlobalTheory.HoweGlobal.RealTransfer
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_howe_transfer_real_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    Module.rank ℂ ↥(G.M.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobal.relInf Bs G om ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobal.relInf Bs G om ≤ N →
        (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ →
        N ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobal.relInf Bs G om ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype),
      g x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) := by
  first | exact @_root_.GlobalTheory.HoweGlobal.RealTransfer.howe_real_place_transfer | exact _root_.GlobalTheory.HoweGlobal.RealTransfer.howe_real_place_transfer | (intros; apply _root_.GlobalTheory.HoweGlobal.RealTransfer.howe_real_place_transfer <;> assumption)
end
