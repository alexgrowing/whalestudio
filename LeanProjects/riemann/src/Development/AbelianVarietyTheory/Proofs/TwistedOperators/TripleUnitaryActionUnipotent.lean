import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryFactorFiniteSetOfPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetAdelicUnitaryPreservesLatticeAlmostAStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupportUnitaryPointReplacesPureTensorFactoStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizersFixVacuaFixesPureTensorLeftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesVacuumFixedStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LocActV

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.WeilM

theorem finite_point_acts_placewise : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    (∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
          om (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ') ∧
    ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M'.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v) ∧
          om' (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.unramified_places_vacuum_fixed hPr F E σ B a a' G X om om' hT
  have key : ∀ {n : ℕ} (Y : Spc F E n) (M : Model σ Y G.W) (χX χW : Chr F E) (ω : Rep σ Y G.W) (r s r' s' : ℕ),
      GlobalTheory.ThK.IsPair B M χX χW ω r s r' s' →
      (∀ v ∉ S₀, ∀ k ∈ GlobalTheory.InertSph.KAt σ Y v, Acts (evFin F v) (ω (k, 1)) (M.vac v) (M.vac v)) →
      ∀ g : UA σ Y.J, (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) →
      ∀ (f : SInf F (Fin n × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ SB (Fin n × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ SB (Fin n × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = M.vac v) ∧
          (∀ v, φ' v - φ v ∈ augAt ω v) ∧ ω (g, 1) (pure f φ) = pure f φ' := by
    intro n Y M χX χW ω r s r' s' hP hsph g hg f φ hφ hvac
    classical
    obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_finset_adelicUnitary_preserves_lattice_almost_all σ Y hP.herm.lat g
    have hfin := Filter.eventually_cofinite.1 hvac
    set S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) := S₀ ∪ S₁ ∪ hfin.toFinset with hSdef
    obtain ⟨gS, k, hgk, hgS, hkS, hkI, hkL⟩ := GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces σ Y g S
    obtain ⟨φ', hφ'SB, hφ'off, hφ'aug, hφ'eq⟩ := GlobalTheory.T.finiteSupport_unitaryPoint_replaces_pureTensorFactors σ B Y G.W M χX χW ω r s r' s' hP S gS hgS f φ hφ hvac
    have hk : ω (k, 1) (pure f φ) = pure f φ := by
      refine GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor_left σ B Y G.W M χX χW ω r s r' s' hP S (fun v hv => hsph v (fun h => hv (by simp [hSdef, h])))
        k (fun u hu => by rw [hkI u hu]; exact hg u hu) hkS (fun w hw z hz => ?_) f φ hφ (fun w hw => ?_)
      · have hw1 : w ∉ S₁ := fun h => hw (by simp [hSdef, h])
        rw [(hkL w hw z hz).1, (hkL w hw z hz).2]
        exact hS₁ w hw1 z hz
      · by_contra hne
        exact hw (by simp [hSdef, hne])
    refine ⟨φ', hφ'SB, ?_, hφ'aug, ?_⟩
    · filter_upwards [hvac, S.finite_toSet.compl_mem_cofinite] with v hv hvS
      rw [hφ'off v hvS, hv]
    · have e : ((g, 1) : UA σ Y.J × UA σ G.W.J) = (gS, 1) * (k, 1) := by
        rw [hgk, Prod.mk_mul_mk, one_mul]
      rw [e, map_mul, Module.End.mul_apply, hk, hφ'eq]
  exact ⟨fun g hg f φ hφ hvac => key G.V G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) (fun v hv => (hS₀ v hv).1) g hg f φ hφ hvac,
    fun g hg f φ hφ hvac => key G.V' G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) (fun v hv => (hS₀ v hv).2) g hg f φ hφ hvac⟩

end GlobalTheory.LocActV
