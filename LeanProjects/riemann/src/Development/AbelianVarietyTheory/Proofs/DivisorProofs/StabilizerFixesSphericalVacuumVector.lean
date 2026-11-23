import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferent
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserLeftPreservesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactFixesVacuumNonsplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVPairVWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceVacuumEigenvalueOneStatement

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny

namespace GlobalTheory.UnrVacFixV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_latKAt_of_isStab {σ : E →ₐ[F] E} (B : Base F E) {n : ℕ} (X : Spc F E n) {K : Subgroup (UA σ X.J)}
    (hK : IsStab B K) (v : Pl F) {k : UA σ X.J} (hk : k ∈ KAt K (evFin F v)) : k ∈ GlobalTheory.InertSph.KAt σ X v := by
  obtain ⟨hkK, hU⟩ := hk
  have hL := ((hK k).1 hkK).2
  have hinv : mat k⁻¹ * mat k = 1 := Units.inv_mul k.1
  have hU' : At (evFin F v) (mat k⁻¹ - 1) := by
    intro u hu
    have h0 : u • (mat k - 1) = 0 := hU u hu
    have : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by
      rw [Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub]
    rw [this, smul_neg, ← Matrix.mul_smul, h0, Matrix.mul_zero, neg_zero]
  refine ⟨hU, fun z hz => ⟨?_, ?_⟩⟩
  · exact GlobalTheory.VacFixKAt.mulVec_mem_latAt X v _ hU (fun z hz => (hL z hz).1) hz
  · have hL' : ∀ z ∈ latHat X, mat k⁻¹ *ᵥ z ∈ latHat X := fun z hz => (hL z hz).2
    exact GlobalTheory.VacFixKAt.mulVec_mem_latAt X v _ hU' hL' hz

theorem vac_unique_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (θ : 𝓞 E), (θ : E) + σ θ = 1 →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • (G.M.vac v))) →
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ)) →
        ∃ c : ℂ, φ = c • G.M.vac v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v θ _ hvac φ hφ hfix
  classical
  have hat : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  let cf : latAtV G.V G.W v → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ)
  have hloc : ∀ f ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (G.M.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • f)) →
      ∀ γ : latAtV G.V G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) f = cf γ • f := by
    intro f hf h γ
    exact GlobalTheory.TensUniq.eq_of_tens_eq v f _ _ hf fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ (hat γ γ.2) f r hr).symm.trans (h γ γ.2 r hr)
  have hsd : ∀ z, z ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v) ↔
      ∀ l ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v), GlobalTheory.LatVac.psiAt B.ψ v (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1 :=
    GlobalTheory.LatVac.DualLoc.map_selfDual v G.M.co B.ψ (latAtV G.V G.W v) hat
      (fun z hz => GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B a (a + a') G.V G.W _ _ _ _ hTr.base hTr.geo.hV
        hTr.geo.hW v z hz)
  have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v),
      t • l ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v) := by
    rintro t ht _ ⟨γ, hγ, rfl⟩
    refine ⟨GlobalTheory.LatVac.liftV v t • γ, (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).2 t ht γ hγ, ?_⟩
    rw [GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hbd : ∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F := by
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V G.W v G.M.co hTr.geo.hV.lat hTr.geo.hW.lat
    exact ⟨c, hc0, by rintro _ ⟨γ, hγ, rfl⟩ i; exact (hc γ hγ i).1⟩
  have hD := GlobalTheory.T.exists_second_coordinate_of_orthogonal_selfDual v (GlobalTheory.LatVac.psiAt B.ψ v) _ hsd hst hbd
  refine GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun γ : latAtV G.V G.W v => GlobalTheory.LatVac.locCo G.M.co v γ) cf
    (fun u hu => ?_) φ (G.M.vac v) (hloc φ hφ hfix) (hloc _ (hTr.geo.hM.vac v).1 hvac) (hTr.geo.hM.vac v).2.1
  obtain ⟨y', γ, hγ, he⟩ := hD u (by
    rintro y ⟨γ, hγ, he⟩
    have h1 := hu ⟨γ, hγ⟩ (congrArg Prod.fst he)
    have h2 : (GlobalTheory.LatVac.locCo G.M.co v γ).2 = y := congrArg Prod.snd he
    simp only at h1
    rw [h2] at h1
    exact h1)
  exact ⟨⟨γ, hγ⟩, congrArg Prod.fst he⟩

theorem isUnram_of_unramified {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : Pl F) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
  intro P hP
  rw [Ideal.ramificationIdx_eq_one_iff]
  infer_instance

theorem vac_fixed_V : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {a a' : ℕ}
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ K : Subgroup (UA σ G.V.J), IsStab B K → ∀ v : Pl F, v ∉ X.T →
      ∀ k ∈ KAt K (evFin F v), Acts (evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr K hK v hv k hk
  have hk' := mem_latKAt_of_isStab B G.V hK v hk
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt (isUnram_of_unramified hTr.base.unram v) with hs | ⟨w, hw⟩
  · obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM.vac v
    obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV_pairVW F E σ B a a' G X om om' hTr v k hk'.1 _ hSB
    have h1 := GlobalTheory.VacTransportLeft.transport_left F E σ B a a' G X om om' hTr v k hk' θ hθ _ hSB φ₁ hφ₁ hvac hact
    obtain ⟨c, rfl⟩ := vac_unique_left F E σ B a a' G X om om' hTr v θ hθ hvac φ₁ hφ₁ h1
    have hc := GlobalTheory.T.split_place_vacuum_eigenvalue_one F E σ B a a' G X om om' hTr v hs hv k hk' c hact
    rwa [hc, one_smul] at hact
  · exact GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hTr v w hw hv k hk' 1 (GlobalTheory.InertSph.one_mem_KAt σ G.W v)

end GlobalTheory.UnrVacFixV
