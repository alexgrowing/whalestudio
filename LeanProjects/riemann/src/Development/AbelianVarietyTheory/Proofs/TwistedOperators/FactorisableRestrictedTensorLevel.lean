import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory.FixedSpan

section General

variable {ι G H : Type} {Γ Hs : ι → Type} [Group G] [∀ i, Group (Γ i)] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
  {p : ∀ i, G →* Γ i} {δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i)} {ξ : ∀ i, Hs i} {π : G →* (H →L[ℂ] H)}
  {B : (∀ i, Hs i) → H}

theorem mem_closure_span_of_orthogonal [DecidableEq ι] [CompleteSpace H] (h : IsRestrTensor p δ ξ π B)
    (U : ∀ i, Submodule ℂ (Hs i)) [∀ i, (U i).HasOrthogonalProjection] (hξ : ∀ᶠ i in cofinite, ξ i ∈ U i) (x : H)
    (hx : ∀ z, Restr ξ z → ∀ i, ∀ w ∈ (U i)ᗮ, ⟪x, B (Function.update z i w)⟫_ℂ = 0) :
    x ∈ (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ i, y i ∈ U i) ∧ z = B y}).topologicalClosure := by
  set Y := (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ i, y i ∈ U i) ∧ z = B y}).topologicalClosure with hY
  haveI : CompleteSpace Y := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨a, ha, u, hu, rfl⟩ := Y.exists_add_mem_mem_orthogonal x
  have h1 : ∀ z, Restr ξ z → ∀ i, ∀ w ∈ (U i)ᗮ, ⟪a, B (Function.update z i w)⟫_ℂ = 0 := fun z hz i w hw => by
    have : Y ≤ (ℂ ∙ B (Function.update z i w))ᗮ :=
      Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 (by
        rintro _ ⟨y, hy, hyU, rfl⟩
        refine Submodule.mem_orthogonal_singleton_iff_inner_left.2 ?_
        rw [h.inner_update hz hy, Submodule.inner_right_of_mem_orthogonal (hyU i) hw, zero_mul]))
        (Submodule.isClosed_orthogonal _)
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (this ha)
  have h2 : ∀ z, Restr ξ z → ∀ i, ∀ w ∈ (U i)ᗮ, ⟪u, B (Function.update z i w)⟫_ℂ = 0 := fun z hz i w hw => by
    have := hx z hz i w hw
    rwa [inner_add_left, h1 z hz i w hw, zero_add] at this
  have h3 : ∀ s : Finset ι, ∀ y, Restr ξ y → (∀ i ∉ s, y i ∈ U i) → ⟪u, B y⟫_ℂ = 0 := fun s => by
    induction s using Finset.induction_on with
    | empty =>
      intro y hy hyU
      exact Submodule.inner_left_of_mem_orthogonal (K := Y)
        (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, hy, fun i => hyU i (by simp), rfl⟩)) hu
    | insert i s hi ih =>
      intro y hy hyU
      obtain ⟨b, hb, c, hc, e⟩ := (U i).exists_add_mem_mem_orthogonal (y i)
      have e1 : B y = B (Function.update y i b) + B (Function.update y i c) := by
        have := h.pure_update hy i 1 b c
        rwa [one_smul, one_smul, ← e, Function.update_eq_self] at this
      rw [e1, inner_add_right, h2 y hy i c hc, add_zero]
      refine ih _ (SmallThetaModules.restr_update hy i b) fun j hj => ?_
      by_cases hji : j = i
      · subst hji; rwa [Function.update_self]
      · rw [Function.update_of_ne hji]
        exact hyU j (by simp [hji, hj])
  have h4 : u = 0 := h.ext fun y hy => by
    have hf : ({i | y i ≠ ξ i} ∪ {i | ξ i ∈ U i}ᶜ).Finite := Set.Finite.union hy hξ
    rw [inner_zero_right, inner_eq_zero_symm]
    refine h3 hf.toFinset y hy fun i hi => ?_
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff, not_or, not_not] at hi
    exact hi.1 ▸ hi.2
  rwa [h4, add_zero]

theorem exists_update_clm [DecidableEq ι] (h : IsRestrTensor p δ ξ π B) {y : ∀ i, Hs i} (hy : Restr ξ y) (v : ι) :
    ∃ T : Hs v →L[ℂ] H, ∀ w, T w = B (Function.update y v w) := by
  have hr := SmallThetaModules.restr_update hy v
  have h0 : B (Function.update y v 0) = 0 := h.ext fun z hz => by simp [h.inner_update hy hz]
  let T : Hs v →ₗ[ℂ] H :=
    { toFun := fun x => B (Function.update y v x)
      map_add' := fun a b => by simpa using h.pure_update hy v 1 a b
      map_smul' := fun c a => by simpa [h0] using h.pure_update hy v c a 0 }
  have hT : ∀ x, ‖T x‖ ≤ √‖∏ᶠ (u) (_ : u ≠ v), ⟪y u, y u⟫_ℂ‖ * ‖x‖ := fun x => by
    have e := h.inner_update hy (hr x) v x
    rw [Function.update_self, finprod_congr fun u => finprod_congr fun hu : u ≠ v => by
      rw [Function.update_of_ne hu]] at e
    have e' := congrArg norm e
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e'
    refine le_of_sq_le_sq (le_of_eq ?_) (by positivity)
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _), mul_comm]
    simpa [T] using e'
  exact ⟨T.mkContinuous _ hT, fun _ => rfl⟩

end General

def fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X] (ρ : G →* (X →L[ℂ] X))
    (K : Subgroup G) : Submodule ℂ X := ⨅ k ∈ K, LinearMap.ker ((ρ k - 1 : X →L[ℂ] X) : X →ₗ[ℂ] X)

theorem mem_fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ρ : G →* (X →L[ℂ] X)}
    {K : Subgroup G} {x : X} : x ∈ fixedSub ρ K ↔ ∀ k ∈ K, ρ k x = x := by
  simp [fixedSub, sub_eq_zero]

theorem isClosed_fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (ρ : G →* (X →L[ℂ] X)) (K : Subgroup G) : IsClosed (fixedSub ρ K : Set X) := by
  have : (fixedSub ρ K : Set X) = ⋂ k ∈ K, {x | ρ k x = x} := by
    ext x; simp [mem_fixedSub]
  rw [this]
  exact isClosed_biInter fun k _ => isClosed_eq (ρ k).continuous continuous_id

theorem inner_eq_zero_of_fixed {Γ X H : Type} [Group Γ] [TopologicalSpace Γ] [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : Γ →* (X →L[ℂ] X)} (hρ : IsUnitaryRep ρ) {τ : Γ → (H →L[ℂ] H)}
    (hτ : ∀ g a b, ⟪τ g a, τ g b⟫_ℂ = ⟪a, b⟫_ℂ) (T : X →L[ℂ] H) (hT : ∀ g w, T (ρ g w) = τ g (T w))
    {K : Subgroup Γ} {x : H} (hx : ∀ k ∈ K, τ k x = x) {w : X} (hw : w ∈ (fixedSub ρ K)ᗮ) : ⟪x, T w⟫_ℂ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left]
  refine Submodule.inner_right_of_mem_orthogonal (mem_fixedSub.2 fun k hk => ext_inner_right ℂ fun z => ?_) hw
  obtain ⟨z, rfl⟩ : ∃ z', z = ρ k z' := ⟨ρ k⁻¹ z, by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]⟩
  rw [inner_map_map hρ, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hT]
  conv_rhs => rw [← hx k hk, hτ]

theorem mem_closure_span_fixed : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GAd σ J →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (R : ∀ v, IrrU (GPl σ J v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H), IsFactorisation σ J (fun v => (R v).π) ξ π B → ∀ (Kp : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GLoc σ J v)), (∀ᶠ v in cofinite, ∀ k ∈ Kp v, (R (.inr v)).π k (ξ (.inr v)) = ξ (.inr v)) → ∀ x : H, (∀ v, ∀ k ∈ Kp v, π (emb σ J v k) x = x) → x ∈ (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ v, ∀ k ∈ Kp v, (R (.inr v)).π k (y (.inr v)) = y (.inr v)) ∧ z = B y}).topologicalClosure := by
  intro F E _ _ _ _ _ σ n J H _ _ π hπ R ξ B h Kp hξ x hx
  classical
  haveI := hπ.complete
  haveI := fun v => (R v).isIrr.complete
  let K : ∀ v, Subgroup (GPl σ J v) := fun v => match v with
    | .inl _ => ⊥
    | .inr v => Kp v
  haveI : ∀ v, CompleteSpace (fixedSub (R v).π (K v)) := fun v => (isClosed_fixedSub _ _).completeSpace_coe
  have hK : ∀ y : ∀ v, (R v).H, ∀ w, y (.inl w) ∈ fixedSub (R (.inl w)).π (K (.inl w)) := fun y w =>
    mem_fixedSub.2 fun k hk => by
      rw [Subgroup.mem_bot.1 hk, map_one, ContinuousLinearMap.one_apply]
  have key := mem_closure_span_of_orthogonal h (fun v => fixedSub (R v).π (K v)) ?_ x ?_
  · refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_) key
    rintro _ ⟨y, hy, hyU, rfl⟩
    exact ⟨y, hy, fun v => mem_fixedSub.1 (hyU (.inr v)), rfl⟩
  · refine (Set.Finite.image Sum.inr hξ).subset ?_
    rintro (w | v) hv
    · exact absurd (hK ξ w) hv
    · exact ⟨v, fun e => hv (mem_fixedSub.2 e), rfl⟩
  · intro z hz v w hw
    obtain ⟨T, hT⟩ := exists_update_clm h hz v
    rw [← hT]
    refine inner_eq_zero_of_fixed (R v).isIrr.unitary (τ := fun g => π (embPl σ J v g))
      (fun g a b => inner_map_map hπ.unitary _ a b) T (fun g a => ?_) (K := K v) ?_ hw
    · rw [hT, hT, h.apply_embPl (SmallThetaModules.restr_update hz v a), Function.update_self, Function.update_idem]
    · rcases v with v | v
      · intro k hk
        rw [Subgroup.mem_bot.1 hk, map_one, map_one, ContinuousLinearMap.one_apply]
      · exact hx v

end GlobalTheory.FixedSpan
