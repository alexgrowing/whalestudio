import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAutFormUCoef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightModuleFiniteContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepDualPairingStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightModuleInvariantPairingStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanRhoKInfU
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepWeightEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AutRec

theorem continuous_coord_emb {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    Continuous (coord (E := E) τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

theorem continuous_cEmb_emb {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (τ : E →+* ℂ) :
    Continuous (cEmb (E := E) (n := n) τ) :=
  (Continuous.units_map _ (continuous_id.matrix_map (continuous_coord_emb τ))).comp GlobalTheory.DefU.continuous_cInf

theorem exists_autRep_of_vecFun : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ), (∀ u v, star (B u v) = B v u) → (∀ v, 0 ≤ (B v v).re) → (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : ι → (E →+* ℂ)) (mu : ι → ℕ → ℕ) (sh : ι → ℤ), Function.Injective (fun τ => InfinitePlace.mk (σ τ)) → (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res n (mu τ))) → ∀ F : UA E n → NablaT ℂ n mu, F ≠ 0 → (∀ y ∈ infU E n, ∀ g, F (g * y) = F g) → (∀ γ ∈ ratU E n, ∀ g, F (γ * g) = wtOp ℂ n mu sh (fun τ => cEmb (σ τ) γ) (F g)) → (∀ᶠ y in 𝓝 (1 : UA E n), ∀ g, F (g * y) = F g) → ∃ π, IsAutRepU π ∧ (∀ τ, ∃ lam : DomWeight n, (∀ a, lam.w a = (mu τ a : ℤ) + sh τ) ∧ HasWeightAt π (σ τ) lam ∧ HasWeightAt π (ComplexEmbedding.conjugate (σ τ)) lam.dual) ∧ ∃ φ ∈ π, φ ≠ 0 ∧ ∀ (κ : Type) (R : Finset κ) (s : κ → UA E n) (c : ℂ), (∀ i ∈ R, s i ∈ finU E n) → (∀ g, ∑ i ∈ R, F (g * s i) = c • F g) → ∑ i ∈ R, RU E n (s i) φ = c • φ := by
  intro E _ _ _ n B hB1 hB2 hB3 hB4 ι _ _ σ mu sh hσ hanti F hF hinf hrat hsm
  let lam : ι → DomWeight n := fun τ =>
    ⟨fun a => (mu τ a : ℤ) + sh τ, fun a b hab => by
      have h := hanti τ hab
      simp only [Formalism.CohomologicalDescent.LD.res] at h
      dsimp only
      exact Int.add_le_add_right (Int.ofNat_le.2 h) _⟩
  have hlam : ∀ τ a, (lam τ).w a = (mu τ a : ℤ) + sh τ := fun _ _ => rfl
  obtain ⟨-, hNfin, hcont⟩ := GlobalTheory.T.weight_module_finite_continuous n ι mu sh
  haveI := hNfin
  obtain ⟨P, hPsep, hPinv⟩ := GlobalTheory.T.weight_module_invariant_pairing n ι mu sh lam hlam
  obtain ⟨hVfin, hspan⟩ := GlobalTheory.RealSpan.span_rhoK_infU E n ι σ lam hσ
  haveI := hVfin
  let c : UA E n →* (ι → GL (Fin n) ℂ) := MonoidHom.pi fun τ => cEmb (σ τ)
  let R : UA E n →* Module.End ℂ (NablaT ℂ n mu) := (wtHom ℂ n mu sh).comp c
  have hRfin : ∀ k ∈ finU E n, R k = 1 := by
    intro k hk
    have h1 : c k = 1 := funext fun τ => by
      change Matrix.GeneralLinearGroup.map (coord (σ τ)) (cInf k) = 1
      rw [MonoidHom.mem_ker.1 hk, map_one]
    change wtHom ℂ n mu sh (c k) = 1
    rw [h1, map_one]
  have hc : Continuous c := continuous_pi fun τ => continuous_cEmb_emb (σ τ)
  have hRc : ∀ (u : NablaT ℂ n mu) (ℓ : Module.Dual ℂ (NablaT ℂ n mu)), Continuous fun g => ℓ (R g u) :=
    fun u ℓ => (hcont u ℓ).comp hc
  have hratR : ∀ γ ∈ ratU E n, ∀ g, F (γ * g) = R γ (F g) := hrat
  have hRR : ∀ g (u : NablaT ℂ n mu), R g (R g⁻¹ u) = u := fun g u => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] (UA E n → ℂ) :=
    { toFun := fun v g => P v (R g⁻¹ (F g))
      map_add' := fun v w => by funext g; simp
      map_smul' := fun a v => by funext g; simp }
  have hfv : ∀ v g, f v g = P v (R g⁻¹ (F g)) := fun _ _ => rfl
  have haut : ∀ v, IsAutFormU (f v) := fun v =>
    GlobalTheory.EquivCoef.isAutFormU_coef E n _ R F hRfin hRc hinf hratR hsm (P v)
  let ρ : Representation ℂ (infU E n) (Formalism.L2.DIV.VV ℂ lam) :=
    (Formalism.L2.DIV.rhoK (K := ℂ) lam).comp (c.comp (infU E n).subtype)
  have hequiv : ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v) := by
    intro x v
    funext g
    rw [RU_apply, hfv, hfv, hinf x x.2 g]
    have e : wtOp ℂ n mu sh (c x) (R (g * x)⁻¹ (F g)) = R g⁻¹ (F g) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply]
      exact hRR (x : UA E n) _
    rw [← e]
    exact hPinv (c x) v _
  have hf0 : f ≠ 0 := by
    intro h0
    apply hF
    funext g
    by_contra hne
    have hne' : R g⁻¹ (F g) ≠ 0 := by
      intro h
      have h2 := hRR g (F g)
      rw [h, map_zero] at h2
      exact hne h2.symm
    obtain ⟨v, hv⟩ := hPsep _ hne'
    exact hv (by rw [← hfv, h0]; rfl)
  obtain ⟨π, hπ, f', hf'0, hf'π, hf'eq, hf'hk⟩ :=
    GlobalTheory.T.automorphic_rep_dual_pairing E n B hB1 hB2 hB3 hB4 (Formalism.L2.DIV.VV ℂ lam) ρ hspan f hf0 haut hequiv
  have hwt := GlobalTheory.T.automorphic_rep_weight_embedding E n ι σ lam hσ π hπ f' hf'0 hf'π hf'eq
  obtain ⟨v0, hv0⟩ : ∃ v, f' v ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hf'0 (LinearMap.ext h)
  refine ⟨π, hπ, fun τ => ⟨lam τ, fun a => rfl, hwt τ⟩, f' v0, hf'π v0, hv0, ?_⟩
  intro κ Rs s cc hs hsum
  refine hf'hk κ Rs s cc hs ?_ v0
  intro v
  funext g
  rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change ∑ i ∈ Rs, P v (R (g * s i)⁻¹ (F (g * s i))) = cc * P v (R g⁻¹ (F g))
  have e : ∀ i ∈ Rs, R (g * s i)⁻¹ = R g⁻¹ := fun i hi => by
    rw [mul_inv_rev, map_mul, hRfin _ ((finU E n).inv_mem (hs i hi)), one_mul]
  calc ∑ i ∈ Rs, P v (R (g * s i)⁻¹ (F (g * s i))) = ∑ i ∈ Rs, P v (R g⁻¹ (F (g * s i))) :=
        Finset.sum_congr rfl fun i hi => by rw [e i hi]
    _ = P v (R g⁻¹ (∑ i ∈ Rs, F (g * s i))) := by rw [map_sum, map_sum]
    _ = cc * P v (R g⁻¹ (F g)) := by rw [hsum g, map_smul, map_smul, smul_eq_mul]

end GlobalTheory.AutRec

end
