import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerPairModelGoodDescent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_pair_model_good_descent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (_hKP : KP) (B : Base F E) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ},
    IsPair B M χX χW om r s r' s' → M₁.IsGood B.ψ →
    ∀ {K : Subgroup (UA σ X.J)}, IsStab B K →
    ∀ (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ),
    (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB (Fin n × Fin d → Fv F v)).map (ev v) = SB (Fin n₁ × Fin d₁ → Fv F v)) →
    (∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (c : AE F E →ₐ[AF F] AE F E) (Z : Matrix (Fin n) (Fin d) (AE F E)) (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)),
    (∀ l, u l = c l.1 • Z) →
    ∀ (ν : Chr F E), Continuous ν → ∀ (z : ℕ) (T : Finset (Pl F)) (f : SInf F (Fin n × Fin d))
      (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) → (∀ v ∉ T, φ v = M.vac v) →
    (∀ v ∉ T, ∀ k ∈ KAt K (evFin F v), Acts (evFin F v) (om (k, 1)) (M.vac v) (M.vac v)) →
    ∀ k ∈ K, ∀ (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → AF F),
      coneInt B M om e u ν z (pure f φ) k l y =
        coneInfInt B M om ei u ν z f (compArch σ X.J k) (unitArch F E l) (fun i => evI F (y i)) *
        (∏ v ∈ T, coneFinInt B M om v (ev v) u ν z (φ v) (compAt σ X.J v k) (unitAt E v l) (fun i => evFin F v (y i))) *
        ∏ᶠ (v : Pl F) (_ : v ∉ T), coneFinInt B M om v (ev v) u ν z (M.vac v) 1 (unitAt E v l) (fun i => evFin F v (y i)) := by
  first | exact @GlobalTheory.ThK.ConeIntFac.coneInt_pure | exact GlobalTheory.ThK.ConeIntFac.coneInt_pure | (intros; apply GlobalTheory.ThK.ConeIntFac.coneInt_pure <;> assumption)
