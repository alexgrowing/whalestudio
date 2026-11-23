import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeImageOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInvariantVectorLocalSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenLatticeImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenLatticePointAtPlaceLocalIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserLeftPreservesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVPairVWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceVacuumEigenvalueOneStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SplitSphV

theorem isSplit_of_nonempty {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {v : Pl F} (hv : Nonempty (E →ₐ[F] Fv F v)) :
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v := by
  obtain ⟨τ⟩ := hv
  have hmem : ∀ ρ : E →ₐ[F] Fv F v,
      (GlobalTheory.AdelicU.splitPrime ρ).asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
    intro ρ
    have h : (GlobalTheory.AdelicU.splitPrime ρ).asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := by
      rw [GlobalTheory.AdelicU.primesOver_eq_split hcm ρ]
      exact Set.mem_insert _ _
    exact h.2.over.symm
  exact ⟨GlobalTheory.AdelicU.splitPrime τ, GlobalTheory.AdelicU.splitPrime (τ.comp σ),
    (GlobalTheory.AdelicU.splitPrime_comp_ne hcm τ).symm, hmem τ, hmem _⟩

theorem vacV_fixed_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hsp hvT k hk
  obtain ⟨hSB, hne, θ, hθ, hfix⟩ := hT.geo.hM.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV_pairVW F E σ B a a' G X om om' hT v k hk.1 _ hSB
  have hfix₁ := GlobalTheory.VacTransportLeft.transport_left F E σ B a a' G X om om' hT v k hk θ hθ _ hSB φ₁ hφ₁ hfix hact
  set Λ := latAtV G.V G.W v with hΛ
  set co := G.M.co with hco
  have hAt : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  let χ : Matrix (Fin a) (Fin (a + a')) (AE F E) → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ)
  have toSchr : ∀ f : (Fin a × Fin (a + a') → Fv F v) → ℂ, f ∈ SB _ →
      (∀ γ ∈ Λ, Acts (evFin F v) (co.rho B.ψ γ) f (χ γ • f)) →
      ∀ γ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo co v γ) f = χ γ • f := by
    intro f hf hA γ hγ
    obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v f hf
    funext ξ
    have key := GlobalTheory.LatVac.heis_at_local_identity v co B.ψ γ f (χ γ) (hAt γ hγ) (hA γ hγ) r hr x₀ hx₀ ξ
    rw [← invOf_eq_inv] at key
    exact key
  have hB := hT.base
  obtain ⟨hop, hcpt⟩ := GlobalTheory.LatOpenCptAny.main σ B G.V G.W _ _ _ _ hT.geo.hV hT.geo.hW co v
  obtain ⟨c, hc⟩ := GlobalTheory.HeisUniqLoc.eigen_unique v (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v) (GlobalTheory.LatVac.locCo co v) Λ hop hcpt
    (fun w hw => GlobalTheory.LatSelfDualCo.latAtV_selfDual_locCo F E σ B a (a + a') G.V G.W _ _ _ _ hB hT.geo.hV hT.geo.hW co v w hw)
    χ (G.M.vac v) φ₁ hne (toSchr _ hSB hfix) (toSchr _ hφ₁ hfix₁)
  rw [hc] at hact
  have h1 := GlobalTheory.T.split_place_vacuum_eigenvalue_one F E σ B a a' G X om om' hT v (isSplit_of_nonempty hB.cm hsp) hvT k hk c hact
  rw [h1, one_smul] at hact
  exact hact

end GlobalTheory.SplitSphV
