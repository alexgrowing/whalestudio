import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFiniteDimensionalFinitePartsWeilTrans
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepresentationPairContinuous

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
noncomputable section
namespace GlobalTheory.WeilContF
end GlobalTheory.WeilContF
namespace GlobalTheory.WeilContF
theorem exists_local_finite_parts_F_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ p0, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        om p Φ = ∑ i, pureA F (f i) (g i) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ χS χT hS hT hrS hrT ω hω JA JB ξ hJA hJB κ _ co hco om hom Φ hΦ p0
  obtain ⟨pres, impl⟩ := _root_.GlobalTheory.T.weil_representation_pair_continuous F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ χS χT hS hT hrS hrT ω hω JA JB ξ hJA hJB κ co
    hco om hom
  obtain ⟨L₁, L₂, hL₁, hL₂, hinv⟩ := GlobalTheory.T.exists_openSubgroups_schroedinger_fix_continuousChar F B.ψ hB.std.1 κ Φ hΦ
  obtain ⟨N, hN, L₁', L₂', hL₁', hL₁c, hL₂', hNL⟩ := GlobalTheory.T.exists_nhds_transportedAction_finitePoint_preimage F E σ nT nS JA JB ξ κ co L₁ L₂ hL₁ hL₂ p0
  have hK := GlobalTheory.T.isCompact_annihilator_openSubgroup_finiteAdeles F B.ψ hB.std κ L₂' hL₂'
  obtain ⟨m, g, y, hg, hgy, hrep⟩ := GlobalTheory.T.periodic_adelicSchwartz_finite_coset_decomposition F κ L₁' hL₁' hL₁c _ hK
  refine ⟨N, hN, m, g, y, hg, hgy, fun p hp => ?_⟩
  have fix : ∀ x ∈ L₁', ∀ y₁ ∈ L₂', schr B.ψ (GlobalTheory.WeilCont.adeleJoin F 0 x,
      GlobalTheory.WeilCont.adeleJoin F 0 y₁) (om p Φ) = om p Φ := by
    intro x hx y₁ hy₁
    obtain ⟨x', hx', y', hy', he⟩ := hNL p hp x hx y₁ hy₁
    have := impl p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y')) Φ hΦ
    simp only [Darboux.rho, LinearEquiv.apply_symm_apply, hinv x' hx' y' hy', he] at this
    exact this.symm
  refine hrep (om p Φ) (pres p Φ hΦ) ?_ ?_
  · intro x hx z
    have := congrFun (fix x hx 0 (zero_mem _)) z
    simp only [schr, GlobalTheory.WeilContF.adeleJoin_zero_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one,
      one_mul] at this
    exact this
  · intro z hz y₁ hy₁
    have := congrFun (fix 0 (zero_mem _) y₁ hy₁) z
    simp only [schr, GlobalTheory.WeilContF.adeleJoin_zero_zero, zero_dotProduct, mul_zero, add_zero,
      GlobalTheory.WeilContF.dotProduct_adeleJoin_zero] at this
    exact (mul_eq_right₀ hz).mp this
end GlobalTheory.WeilContF
end
end
