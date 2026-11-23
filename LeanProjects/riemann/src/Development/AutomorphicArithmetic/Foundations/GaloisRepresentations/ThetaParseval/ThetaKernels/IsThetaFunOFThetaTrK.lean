import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenber
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledThetaLiftIdentity
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledThetaLiftConvergence
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledThetaLiftAutomorphy
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledThetaLiftNonvanishing

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.TransportHeisF
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem isThetaFunOF_thetaTr_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ hA hBξ κ _ co hco φ hφ
  exact
    { quasi := _root_.GlobalTheory.T.doubled_theta_lift_identity F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ hA hBξ κ co hco φ hφ
      level := _root_.GlobalTheory.T.doubled_theta_lift_convergence F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ hA hBξ κ co hco φ hφ
      cont := _root_.GlobalTheory.T.doubled_theta_lift_automorphy F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ hA hBξ κ co hco φ hφ
      smooth := _root_.GlobalTheory.T.doubled_theta_lift_nonvanishing F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ hA hBξ κ co hco φ hφ }
set_option maxHeartbeats 400000 in
theorem pres_impl_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
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
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) ∧
              ∀ p w, ∀ φ ∈ schA F κ, om p (co.rho B.ψ w φ) = co.rho B.ψ (actAB (cA σ) p w) (om p φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc χS χT hχS hχT rS rT ω hω JA JB ξ hA hBξ κ _ co hco om htr
  have hstd : IsStd B.ψ := hB.std
  have hchar : IsCharAF F B.ψ := hω.std.1
  have key : ∀ p : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB), ∃ (g : Formalism.IndefR.DatumF.GAF σ JS)
      (h : Formalism.IndefR.DatumF.GAF σ JT), Formalism.IndefR.DatumF.mtF σ JT h = p.1.1.1 ∧
        Formalism.IndefR.DatumF.mtF σ JS g = (p.2⁻¹).1.1ᵀ :=
    fun p => match_pairF σ JS JT hS.2 ξ₀ hξ₀ JA JB ξ hA hBξ p.1 p.2
  have pres : ∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ := by
    intro p φ hφ
    obtain ⟨g, h, hh, hg⟩ := key p
    exact (htr p.1 p.2 g h hh hg φ hφ).1
  refine ⟨pres, fun p w φ hφ => ?_⟩
  obtain ⟨a, b⟩ := p
  obtain ⟨g, h, hh, hg⟩ := key (a, b)
  have hs := symp_eq_symplOF (F := F) σ JS JT ξ₀ JA JB ξ hA hBξ
  have hrho : ∀ w', ∀ φ' ∈ schA F κ, co.rho B.ψ w' φ' ∈ schA F κ :=
    fun w' φ' h' => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ φ' h'
  have h1 := htr a b g h hh hg _ (hrho w φ hφ)
  have h2 := htr a b g h hh hg _ hφ
  have hF := _root_.GlobalTheory.TransportHeisF.isThetaFunOF_thetaTr_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hω.std JA JB ξ hA hBξ κ co hco φ hφ
  have E1 := hω.om_heis g h w _ hF
  have E2 := thetaTr_rhoF σ B.ψ hs co w φ
  have E3 := thetaTr_rhoF σ B.ψ hs co (actAB (cA σ) (a, b) w) (om (a, b) φ)
  have E4 := actOF_eq σ a b g h hh hg w
  have E : GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om (a, b) (co.rho B.ψ w φ)) =
      GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (actAB (cA σ) (a, b) w) (om (a, b) φ)) := by
    refine h1.2.trans ?_
    refine (congrArg (ω (g, h)) E2).trans ?_
    refine E1.trans ?_
    refine Eq.trans ?_ E3.symm
    exact congrArg₂ (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ) E4 h2.2.symm
  unfold GlobalTheory.WeilSchrodinger.thetaTr Darboux.rho at E
  refine schr_theta_inj B.ψ hchar κ _ h1.1 _ (hrho _ _ h2.1) fun v => ?_
  obtain ⟨v', rfl⟩ := co.e.surjective v
  exact congrFun E v'
end GlobalTheory.TransportHeisF
end
end
