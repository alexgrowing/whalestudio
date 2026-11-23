import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlacePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPureTensorBaseVectorAndLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniquePureTensorRestrictedFamilyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorUpdateFactorFromBaseVectorStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PlaceTensor.PureScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem wAt_zero {m n : ℕ} (p : Place D) : wAt p (0 : Mx D m n) = 0 := by
  rw [wAt_eq_smul, smul_zero]

theorem wAt_neg_wAt_self {m n : ℕ} (q : Place D) (w : Mx D m n) : wAt q (-(wAt q w)) = -(wAt q w) := by
  have hq : idem D q * idem D q = idem D q := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 q
  rw [wAt_eq_smul, wAt_eq_smul, smul_neg, smul_smul, hq]

theorem wAt_neg_wAt_ne {m n : ℕ} {p q : Place D} (hpq : p ≠ q) (w : Mx D m n) : wAt p (-(wAt q w)) = 0 := by
  have hpq' : idem D p * idem D q = 0 := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q hpq
  rw [wAt_eq_smul, wAt_eq_smul, smul_neg, smul_smul, hpq', zero_smul, neg_zero]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem ip_base (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) : ipO μ 𝓕 f₀ f₀ = 1 := by
  have hself : ipO μ 𝓕 f₀ f₀ = (nrm2 μ 𝓕 f₀ : ℂ) :=
    (GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std hb) hμ f₀ f₀ (base_theta hb) (base_theta hb)).2.2.2.2.1
  rw [hself, restrictedTensorBasePoint_norm_sq hb hμ, Complex.ofReal_one]

theorem finite_mulSupport_ip (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {x₁ x₂ : Place D → WO S T → ℂ} (h₁ : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x₁)
    (h₂ : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x₂) :
    (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite := by

  refine (h₁.2.union h₂.2).subset fun p hp => ?_
  rw [Function.mem_mulSupport] at hp
  by_contra hout
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hout
  exact hp (by rw [hout.1, hout.2]; exact ip_base hb hμ)

private theorem heisO_zero_twisted_operators (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext u
  simp [heisO, symplOH, symplO, hO]

theorem pureTensor_innerProduct_eq_finprod_local_of_finset (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (s : Finset (Place D)) :
    ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), (∀ p, p ∉ s → x₁ p = f₀) →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ →
      ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  classical
  have hθ₀ : IsThetaFunO ψ S T f₀ := base_theta hb

  have hsymm : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ipO μ 𝓕 g f = (starRingEnd ℂ) (ipO μ 𝓕 f g) :=
    fun f g hf hg => (GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std hb) hμ f g hf hg).2.1
  have hadj : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ∀ w,
      ipO μ 𝓕 (heisO ψ S T w f) g = ipO μ 𝓕 f (heisO ψ S T (-w) g) :=
    fun f g hf hg w => ((GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std hb) hμ f g hf hg).2.2.2.2.2.2.1 w).2
  induction s using Finset.induction_on with
  | empty =>

    intro x₁ x₂ f₁ f₂ hx h₁ h₂
    have hx₁ : x₁ = fun _ => f₀ := funext fun p => hx p (by simp)
    subst hx₁
    have hf₁ : f₁ = f₀ :=
      (GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ h₁.1).unique h₁
        (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ).1
    subst hf₁
    obtain ⟨hfin, hprod⟩ := h₂.2.2 0
    simp only [wAt_zero, heisO_zero_twisted_operators] at hfin hprod
    rw [hsymm f₂ f₁ h₂.2.1 hθ₀, hprod, map_finprod _ hfin]
    exact finprod_congr fun p => (hsymm (x₂ p) f₁ (h₂.1.1 p).1 hθ₀).symm
  | insert q s hq ih =>
    intro x₁ x₂ f₁ f₂ hx h₁ h₂

    have hres : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (Function.update x₁ q f₀) := by
      refine ⟨fun p => ?_, h₁.1.2.subset fun p hp => ?_⟩
      · by_cases hpq : p = q
        · subst hpq
          rw [Function.update_self]
          exact base_isLocal hb p
        · rw [Function.update_of_ne hpq]
          exact h₁.1.1 p
      · by_cases hpq : p = q
        · subst hpq
          simp at hp
        · simpa [Function.update_of_ne hpq] using hp
    have hoff : ∀ p, p ∉ s → Function.update x₁ q f₀ p = f₀ := by
      intro p hp
      by_cases hpq : p = q
      · subst hpq
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne hpq]
        exact hx p (by simp [hpq, hp])
    obtain ⟨g₁, hg₁, -⟩ := GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ hres

    obtain ⟨f', hf', hc⟩ := GlobalTheory.T.pureTensor_update_factor_from_base_vector D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ (Function.update x₁ q f₀) x₁ g₁ q hg₁
      (Function.update_self _ _ _) (fun p hp => (Function.update_of_ne hp _ _).symm) (h₁.1.1 q)
    have hf'₁ : f' = f₁ := (GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ h₁.1).unique hf' h₁
    subst hf'₁
    have hθq : IsThetaFunO ψ S T (x₂ q) := (h₂.1.1 q).1
    have key := hc f₂ (x₂ q) (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x₁ p) (x₂ p)) h₂.2.1 hθq (fun w => by
      rw [hadj g₁ f₂ hg₁.2.1 h₂.2.1]
      have hpw := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ x₂ f₂ h₂ (-(wAt q w))
      rw [ih _ _ _ _ hoff hg₁ hpw, ← mul_finprod_cond_ne q (finite_mulSupport_ip hb hμ hres hpw.1),
        Function.update_self, wAt_neg_wAt_self, ← hadj f₀ (x₂ q) hθ₀ hθq, mul_comm]
      congr 1
      refine finprod_congr fun p => finprod_congr fun hp => ?_
      rw [Function.update_of_ne hp, wAt_neg_wAt_ne hp, heisO_zero_twisted_operators])
    rw [key, mul_comm]
    exact mul_finprod_cond_ne q (finite_mulSupport_ip hb hμ h₁.1 h₂.1)

end

theorem ip_pure_eq_finprod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ → (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite ∧ ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ x₁ x₂ f₁ f₂ h₁ h₂
  refine ⟨finite_mulSupport_ip hb hμ h₁.1 h₂.1, ?_⟩

  exact pureTensor_innerProduct_eq_finprod_local_of_finset hb hμ h₁.1.2.toFinset x₁ x₂ f₁ f₂
    (fun p hp => by simpa [Set.Finite.mem_toFinset] using hp) h₁ h₂

end GlobalTheory.PlaceTensor.PureScalar

end
