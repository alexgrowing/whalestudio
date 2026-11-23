import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesawStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.PolDataLie

theorem snd_eq_zero_of_at {F : Type} [Field F] [NumberField F] {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) :
    (z i).2 = 0 := by
  have h0 : evI F (((0 : Ainf F), (1 : Af F)) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h1 := congrArg Prod.snd (congrFun (hz _ h0) i)
  have h2 : (1 : Af F) * (z i).2 = 0 := h1
  rwa [one_mul] at h2

theorem hasDerivAt_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ)
    {T : ℝ → ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ} {f f₁ : SInf F (Fin n × Fin d)}
    (h : ActsD (evI F) T f f₁) {φ} (hφ : GlobalTheory.BigNZ.Fam M φ) (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun t => T t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ x) 0 := by
  refine h (fun y => GlobalTheory.BigNZ.finPartFn φ fun i => (y i).2) ⟨fun y z hz => ?_, hφ.mem hM f⟩ x
  have e : (fun i => ((y + z) i).2) = fun i => (y i).2 := by
    funext i
    have : ((y + z) i).2 = (y i).2 + (z i).2 := rfl
    rw [this, snd_eq_zero_of_at hz i, add_zero]
  simp only [e]

theorem lie_deriv_polData : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∃ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, ∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' R Rf hm γ hγ Φ hΦ
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_lieDerivative_polynomialFock_seesaw B G X om om' hm.triple γ hγ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := h
    exact ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (D f) φ, Submodule.subset_span ⟨D f, (hD f hf).1, φ, h1, h2, rfl⟩, fun x =>
      hasDerivAt_pure hm.triple.geo.hM (T := fun t => om (1, γ (Multiplicative.ofAdd t))) (hD f hf).2 ⟨h1, h2⟩ x⟩
  | zero => exact ⟨0, Submodule.zero_mem _, fun x => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨Φ₁, m1, d1⟩ := h1
    obtain ⟨Ψ₁, m2, d2⟩ := h2
    refine ⟨Φ₁ + Ψ₁, Submodule.add_mem _ m1 m2, fun x => ?_⟩
    simp only [map_add, Pi.add_apply]
    exact (d1 x).add (d2 x)
  | smul c Φ _ h1 =>
    obtain ⟨Φ₁, m1, d1⟩ := h1
    refine ⟨c • Φ₁, Submodule.smul_mem _ c m1, fun x => ?_⟩
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact (d1 x).const_mul c

end GlobalTheory.PolDataLie

end
