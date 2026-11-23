import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.TargetDoubling
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace PositivityTheory.ThKW
def ThetaLiftNonvanishing : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
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
              ∃ (dd : Darboux (symp (cA σ) ξ (incM F JB) (dbl (incM F JA))) (κ ⊕ κ))
                (omd : UG (cA σ) (dbl (incM F JA)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)),
                IsDblCoord (cA σ) ξ (incM F JB) (incM F JA) (GlobalTheory.WeilSchrodinger.transD (cA σ) co) dd ∧
                IsUWeilSplit (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (dbl (incM F JA)) dd χS (diagCols (Fin nT)) omd ∧
                ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (dbl (incM F JA))),
                  gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                  ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂
def ThetaLiftConvergence : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
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
              ∃ (dd : Darboux (symp (cA σ) ξ (incM F JA) (dbl (incM F JB))) (κ ⊕ κ))
                (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)),
                IsDblCoord (cA σ) ξ (incM F JA) (incM F JB) co dd ∧
                IsUWeilSplit (cA σ) (adeleClass F) B.ψ ξ (incM F JA) (dbl (incM F JB)) dd χT (diagCols (Fin nS)) omd ∧
                ∀ (g : UG (cA σ) (incM F JB)) (gd : UG (cA σ) (dbl (incM F JB))),
                  gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                  ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open Formalism.IndefR.DatumF Sw in
set_option maxHeartbeats 400000 in
theorem dblS_of_dblT_k (H : _root_.PositivityTheory.ThKW.ThetaLiftNonvanishing) : _root_.PositivityTheory.ThKW.ThetaLiftConvergence := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ hL χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have lS := invT_mul hS
  have lT := invT_mul hT
  have hsm : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) E), incM F (ξ₀ • M) = incAF F E ξ₀ • incM F M := fun M => by
    ext i j
    exact map_mul (incAF F E) _ _
  have hB' : ξ • incM F JB = incAF F E ξ₀ • incM F JS⁻¹ := hBm.trans (hsm _)
  have hx : IsUnit (incAF F E ξ₀) := (IsUnit.mk0 _ hξ).map _
  have hd : IsUnit (incM F JS⁻¹).det := by
    have h1 : IsUnit (JS⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hS.2)
    have h2 : (incM F JS⁻¹).det = incAF F E (JS⁻¹).det := (RingHom.map_det (incAF F E) _).symm
    rw [h2]
    exact h1.map _
  have hle := ug_le (cA σ) hB' hx hd
  have hge := ug_ge (cA σ) hB' hx
  have hD := smul_dbl hB'
  have hge' := ug_ge (cA σ) hD hx
  have htr := swap_transport σ lS lT B.ψ hle co _ (castD_transD_rho _ hB' co B.ψ) hom _ (swapHom_apply hle om)
  have hrat' : ∀ x : Matrix (Fin nS) (Fin nT) E, ∃ y z : κ → F,
      (castD _ hB' (GlobalTheory.WeilSchrodinger.transD (cA σ) co)).e (incM F x) =
        (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    obtain ⟨y, z, h⟩ := hrat xᵀ
    exact ⟨y, z, (castD_transD_e _ hB' co _).trans h⟩
  have g1 : JS⁻¹ = (JS⁻¹ᵀ)ᵀ := (Matrix.transpose_transpose _).symm
  have g2 : incAF F E ξ₀ • incM F JA = incM F (ξ₀ • (JT⁻¹ᵀ)⁻¹) := by
    rw [(dual_inv lT).2, hsm, hA]
  obtain ⟨dd, omd, k1, k2, k3⟩ := H F E σ B hB nT nS JT⁻¹ᵀ JS⁻¹ᵀ (isHermND_invT hT) (isHermND_invT hS) ξ₀ hξ hσξ
    (LatH.swap hS hT hL) χT χS cT cS rT rS _ (swap_datum σ lS lT ξ₀ B.ψ hω) JS⁻¹ JA (incAF F E ξ₀) g1 g2 κ _ hrat' _ htr
  refine ⟨castD₂ _ hD dd, omd.comp (Subgroup.inclusion hge'), isDblCoord_cast₂ _ hB' co k1,
    isUWeilSplit_cast₂ _ hD hge' (isLagr_diagCols _ _) k2, fun g gd hgd φ₁ hφ₁ φ₂ hφ₂ => ?_⟩
  have k4 := k3 (Subgroup.inclusion hge g) (Subgroup.inclusion hge' gd) hgd φ₁ hφ₁ φ₂ hφ₂
  rw [swapHom_fst] at k4
  rw [MonoidHom.comp_apply]
  exact k4
end PositivityTheory.ThKW
end
end
