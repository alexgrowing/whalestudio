import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineOneParameterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineIntertwinesRealSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwiningSymplecticAndGroupLawStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzUnitaryIntertwinerScalarStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzOneParameterGroupFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ArchCont

open scoped SchwartzMap

theorem lintegral_of_integral {l : Type} [Fintype l] (f g : GlobalTheory.RealWeil.Sch l)
    (h : ∫ x, ‖f x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2) : ∫⁻ x, ‖f x‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have hi : ∀ u : GlobalTheory.RealWeil.Sch l, MeasureTheory.Integrable (fun x => ‖u x‖ ^ 2) MeasureTheory.volume := fun u =>
    (u.memLp 2 MeasureTheory.volume).integrable_norm_pow two_ne_zero
  have e : ∀ u : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖u x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖u x‖ ^ 2) := fun u => by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hi u) (.of_forall fun x => by positivity)]
    congr 1
    funext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e, e, h]

theorem continuous_of_intertwine (hP : GlobalTheory.FunPr.Hypotheses₂) (l : Type) [Fintype l] [DecidableEq l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)
    (hT : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hI : ∀ t w (f f₁ : GlobalTheory.RealWeil.Sch l), ⇑f₁ = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(T t f₁) = GlobalTheory.RealWeil.rhoFun (A t w) ⇑(T t f))
    (hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) (t : ℝ) : Continuous (T t) := by
  obtain ⟨hs, -, -⟩ := GlobalTheory.T.symplectic_and_flow_of_intertwining_unitary l A T hT hT0 hI hiso
  rcases isEmpty_or_nonempty l with hl | hl
  · obtain ⟨f0, hf0⟩ := GlobalTheory.MetaplecticScalarDeriv.exists_schwartz_one l
    have hsub : ∀ x : EuclideanSpace ℝ l, x = 0 := fun x => by
      ext i
      exact isEmptyElim i
    have hdec : ∀ f : GlobalTheory.RealWeil.Sch l, f = f 0 • f0 := by
      intro f
      ext x
      rw [hsub x, SchwartzMap.smul_apply, hf0, smul_eq_mul, mul_one]
    have e : ⇑(T t) = fun f => f 0 • T t f0 := by
      funext f
      conv_lhs => rw [hdec f]
      exact map_smul _ _ _
    rw [e]
    exact (GlobalTheory.MetaplecticScalarDeriv.continuous_eval l 0).smul continuous_const
  · obtain ⟨G, _, _, _, pr, om, omS, ⟨-, hsurj, -⟩, -, h3, h4, -, -⟩ := hP.realMetaplecticRepresentation l
    obtain ⟨N, hN⟩ := GlobalTheory.exists_symplecticGroup_of_sympl l (A t) (hs t)
    obtain ⟨g, hg⟩ := hsurj N
    have hmat : ∀ w, A t ((pr g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) = w := by
      intro w
      have e : pr g * pr g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have e' : (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) * (pr g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 :=
        congrArg (fun x : Matrix.symplecticGroup l ℝ => (x : Matrix (l ⊕ l) (l ⊕ l) ℝ)) e
      rw [← hN, ← hg, Matrix.mulVec_mulVec, e', Matrix.one_mulVec]
    have hU1 : ∀ (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
        ⇑((T t ∘ₗ (omS g⁻¹ : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)) h₁) =
          GlobalTheory.RealWeil.rhoFun w ⇑((T t ∘ₗ (omS g⁻¹ : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)) h) := by
      intro w h h₁ hh
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hI t _ _ _ (GlobalTheory.MetaplecticScalarDeriv.intertwine_fun l _ (om g⁻¹) (omS g⁻¹) (h3 _) (h4 _) w h h₁ hh), hmat]
    have hU2 : ∀ h : GlobalTheory.RealWeil.Sch l,
        ∫⁻ x, ‖(T t ∘ₗ (omS g⁻¹ : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)) h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 := by
      intro h
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [lintegral_of_integral _ _ (hiso t _), GlobalTheory.MetaplecticScalarDeriv.lintegral_iso l (om g⁻¹) (omS g⁻¹) (h4 _)]
    obtain ⟨a, -, ha⟩ := GlobalTheory.T.schwartz_unitary_intertwiner_scalar hP l _ hU1 hU2
    have e : ⇑(T t) = fun f => a • omS g f := by
      funext f
      have h1 := ha (omS g f)
      have e2 : omS g⁻¹ (omS g f) = f := by
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, e2] at h1
      exact h1
    rw [e]
    exact (omS g).continuous.const_smul a

end GlobalTheory.ArchCont

namespace GlobalTheory.ArchCont

open scoped SchwartzMap RealInnerProductSpace

theorem continuous_schr (hP : GlobalTheory.FunPr.Hypotheses₂) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (P : V → V → ℝ) (hp : GlobalTheory.ArchUniq.IsPairing P)
    (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))
    (hTadd : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hTi : ∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = GlobalTheory.ArchUniq.schrF P v ⇑f →
      ⇑(T t f₁) = GlobalTheory.ArchUniq.schrF P (A t v) ⇑(T t f))
    (hTl2 : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) (t : ℝ) : Continuous (T t) := by
  obtain ⟨C, φ, hp', hq⟩ := GlobalTheory.ArchUniq.SchrTransport.coords P hp _ rfl
  have hS := GlobalTheory.ArchUniq.SchrTransport.schr_coords P C φ hp' hq
  let toE : 𝓢(V, ℂ) →L[ℂ] GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V)) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V)) →L[ℂ] 𝓢(V, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  let T' : ℝ → GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V)) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V)) :=
    fun t => toE.toLinearMap ∘ₗ T t ∘ₗ toV.toLinearMap
  let A' : ℝ → (Fin (Module.finrank ℝ V) ⊕ Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ]
      (Fin (Module.finrank ℝ V) ⊕ Fin (Module.finrank ℝ V) → ℝ) :=
    fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hT' : ∀ t h, T' t h = toE (T t (toV h)) := fun t h => rfl
  obtain ⟨k, hk, hint⟩ := GlobalTheory.ArchUniq.SchrTransport.haar_coords μ C
  have c2 : ∀ s t f, T' (s + t) f = T' s (T' t f) := by
    intro s t h
    simp only [hT', hVE, hTadd]
  have c3 : ∀ f, T' 0 f = f := by
    intro h
    simp [hT', hT0, hEV]
  have c4 : ∀ t w (f f₁ : GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V))), ⇑f₁ = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(T' t f₁) = GlobalTheory.RealWeil.rhoFun (A' t w) ⇑(T' t f) := by
    intro t w f f₁ hf
    have e1 : ⇑(toV f₁) = GlobalTheory.ArchUniq.schrF P (φ.symm w) ⇑(toV f) := by
      funext x
      have := congrFun (hS (φ.symm w) ⇑f) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hf]
      exact this.symm
    have e2 := hTi t _ _ _ e1
    rw [hT' t f₁, hT' t f, htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ, ⇑(T t (toV f)) = G ∘ ⇑C :=
      ⟨⇑(T t (toV f)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp [A']
  have c5 : ∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    intro t h
    have e := hTl2 t (toV h)
    rw [hint, hint] at e
    simp only [htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at e
    exact mul_left_cancel₀ hk.ne' e
  have hc := continuous_of_intertwine hP (Fin (Module.finrank ℝ V)) A' T' c2 c3 c4 c5 t
  have e : ⇑(T t) = fun f => toV (T' t (toE f)) := by
    funext f
    simp only [hT', hVE]
  rw [e]
  exact toV.continuous.comp (hc.comp toE.continuous)

end GlobalTheory.ArchCont

open scoped Classical in

theorem GlobalTheory.ArchCont.continuous_line : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W,
    ∀ T : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), T 0 f = f) → ∀ t, Continuous (T t) := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ T hT hadd h0 t
  obtain ⟨A, -, hA⟩ := GlobalTheory.T.archimedeanLine_intertwines_realSchrodinger M ψ χX χW om hψ hW γ hγ T hT
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  let μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) := MeasureTheory.Measure.addHaar
  have hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := fun t f =>
    GlobalTheory.T.weil_representation_integral_action M ψ χX χW om hW μ inferInstance (γ (Multiplicative.ofAdd t)) f (T t f) (hT t f)
  exact GlobalTheory.ArchCont.continuous_schr hP _ μ _ (GlobalTheory.ArchUniq.Coord.isPairing_trP (F := F) (Fin n × Fin d)) A T
    hadd h0 hA hiso t
