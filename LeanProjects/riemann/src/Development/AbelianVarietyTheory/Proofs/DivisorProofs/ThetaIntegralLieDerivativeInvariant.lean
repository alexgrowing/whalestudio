import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativePreservesPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDerivativeAlongLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineDerivativeDominatedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHaarRightInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainLineDerivativeIntegralStatement

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives

noncomputable section

namespace GlobalTheory.ThK.ZFinKill

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

local instance borelUA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

theorem theta_basic {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') {Ψ} (hΨ : Ψ ∈ GlobalTheory.ThK.PolData B G.M)
    (h : UA σ G.W.J) : Continuous (fun g => theta om Ψ g h) ∧
      (∀ δ ∈ ratU σ G.V.J, ∀ g, theta om Ψ (δ * g) h = theta om Ψ g h) ∧
      IntegrableOn (fun g => theta om Ψ g h) G.M.dom G.M.μ := by
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hS : Ψ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) := by
    refine (Submodule.span_le.2 ?_ : GlobalTheory.ThK.PolData B G.M ≤ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a'))) hΨ
    rintro Φ ⟨f, -, φ, hSB, hvac, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hvac.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2)
  obtain ⟨hc, hr, -⟩ := (GlobalTheory.T.theta_basic_properties hKP.base F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP).1 Ψ hS
  obtain ⟨hw, -⟩ := GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP
    (Or.inl (GlobalTheory.ThK.Check.conv_range hT.geo))
  refine ⟨hc.comp (Continuous.prodMk continuous_id continuous_const), fun δ hδ g => ?_, (hw Ψ hS).1 h⟩
  simpa using hr δ hδ 1 (one_mem _) g h

theorem countable_ratU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hM : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  have hGL : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E)) Units.val_injective
  have hR : Countable (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range :=
    (Set.countable_range _).to_subtype
  refine Function.Injective.countable (f := fun x : ratU σ J => (⟨x.1.1, x.2⟩ :
    (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range)) ?_
  intro x y hxy
  have h1 := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext h1)

theorem kill_one {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') {Ψ} (hΨ : Ψ ∈ GlobalTheory.ThK.PolData B G.M)
    {γ : Multiplicative ℝ →* UA σ G.V.J} (hγ : γ ∈ Lines σ G.V) :
    G.M.I om (derL om (fun t => γ (Multiplicative.ofAdd t)) Ψ) = 0 := by
  funext h
  have hΨ' := GlobalTheory.T.line_derivative_preserves_polynomial F E σ B a a' G X om om' hKP hT Ψ hΨ γ hγ
  obtain ⟨hc, hr, hi⟩ := theta_basic hKP hT hΨ h
  obtain ⟨hc', -, -⟩ := theta_basic hKP hT hΨ' h
  obtain ⟨b, hb, hbd⟩ := GlobalTheory.T.theta_along_line_le_integrableOn_bound F E σ B a a' G X om om' hKP hT _ hΨ' γ hγ h
  haveI := hT.geo.hM.haar
  haveI := GlobalTheory.T.unitary_haar_right_invariant F E σ B a G.V (a - G.p) G.p hT.base hT.geo.hV G.M.μ hT.geo.hM.haar
  haveI := countable_ratU (σ := σ) G.V.J
  show ∫ g in G.M.dom, theta om _ g h ∂G.M.μ = 0
  exact GlobalTheory.T.fundamental_domain_line_derivative_integral G.M.μ (ratU σ G.V.J) G.M.dom hT.geo.hM.dom _ _ (fun t => γ (Multiplicative.ofAdd t)) b
    (fun s t => by simp only [ofAdd_add, map_mul]) hr hc hc' hi hb
    (fun g => GlobalTheory.T.theta_derivative_along_line F E σ B a a' G X om om' hKP hT Ψ hΨ γ hγ g h) hbd

theorem kill : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ l : List (Multiplicative ℝ →* UA σ G.V.J), (∀ γ ∈ l, γ ∈ Lines σ G.V) →
      (l.map fun γ t => γ (Multiplicative.ofAdd t)).foldr (derL om) Φ ∈ GlobalTheory.ThK.PolData B G.M ∧
      (l ≠ [] → G.M.I om ((l.map fun γ t => γ (Multiplicative.ofAdd t)).foldr (derL om) Φ) = 0) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hKP hT Φ hΦ l hl
  induction l with
  | nil => exact ⟨hΦ, fun h => absurd rfl h⟩
  | cons γ l ih =>
    have ih' := (ih fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')).1
    have hγ := hl γ List.mem_cons_self
    simp only [List.map_cons, List.foldr_cons]
    exact ⟨GlobalTheory.T.line_derivative_preserves_polynomial F E σ B a a' G X om om' hKP hT _ ih' γ hγ, fun _ => kill_one hKP hT ih' hγ⟩

end GlobalTheory.ThK.ZFinKill

end
