import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationIsoBTriplePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientTendstoZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientIdeleScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCharacterAnnihilatorCompactStatement
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct
open scoped GlobalTheory.VacAny

open GlobalTheory.VanishLoc GlobalTheory.LatVac in

theorem GlobalTheory.VanishLoc.vanish_off_compact : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ∃ C : Set (Fv F B.v₁ ⊗[F] E), IsCompact C ∧
      ∀ l : (AE F E)ˣ, compFin F E B.v₁ l.1 ∉ C →
        ev B.v₁ (locOp B.v₁ (G.M'.co.rho B.ψ (partFin B.v₁ (shiftB σ H H' l))) φ) = 0 := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC e' hE X om om' om₁ om₁' hT hT₁ ei ev hei hvac hfac φ hφ
  have hψ : Continuous B.ψ := hT.base.std.1
  have hψv : Continuous (psiAt B.ψ B.v₁) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hψ B.v₁
  have hne : psiAt B.ψ B.v₁ ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std B.v₁
  set U : Set (Fv F B.v₁ ⊗[F] E) := {t | schr (psiAt B.ψ B.v₁) (locCo G.M'.co B.v₁ (uAt H H' B.v₁ t)) φ = φ} with hUdef
  have hU : U ∈ nhds 0 := (GlobalTheory.T.local_coefficient_tendsto_zero G.M' H H' B.v₁).eventually (GlobalTheory.T.schrodinger_locally_constant B.v₁ (psiAt B.ψ B.v₁) hψv φ hφ)
  refine ⟨_, GlobalTheory.T.trace_character_annihilator_compact B.v₁ (psiAt B.ψ B.v₁) hψv hne U hU, fun l hl => ?_⟩
  simp only [Set.mem_setOf_eq, not_forall] at hl
  obtain ⟨t, ht, hne1⟩ := hl
  have ht' : schr (psiAt B.ψ B.v₁) (locCo G.M'.co B.v₁ (uAt H H' B.v₁ t)) φ = φ := ht
  rw [(locOp_rho G.M'.co hψ B.v₁ (shiftB σ H H' l) hφ).2]
  have hS : schr (psiAt B.ψ B.v₁) (locCo G.M'.co B.v₁ (shiftB σ H H' l)) φ ∈ SB _ :=
    GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ B.v₁ _ φ hφ
  have h1 := GlobalTheory.T.evaluation_iso_b_triple_pair B G G₁ H H' e' hE X om om' om₁ om₁' hT hT₁ ei ev hei hvac hfac B.v₁ (uAt H H' B.v₁ t)
    (uAt_mem_isoB H H' B.v₁ t) (at_uAt H H' B.v₁ t) _ hS
  rw [schr_comm, ht', map_smul, GlobalTheory.T.local_coefficient_idele_scaling B G G₁ H H' hC X om om' hT B.v₁ t l] at h1
  have h2 : (psiAt B.ψ B.v₁ (Algebra.trace (Fv F B.v₁) (Fv F B.v₁ ⊗[F] E) (t * compFin F E B.v₁ l.1)) - 1) •
      ev B.v₁ (schr (psiAt B.ψ B.v₁) (locCo G.M'.co B.v₁ (shiftB σ H H' l)) φ) = 0 := by
    rw [sub_smul, h1, one_smul, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne1)
