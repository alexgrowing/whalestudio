import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsKStableOnKFiniteVectors

noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix
open GlobalTheory.SmoothGlob (lieSet)
open scoped ContDiff

namespace GlobalTheory.GKModule

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kFinVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H :=
  GlobalTheory.KFiniteVectors.kFiniteVectors ε σ

@[simp] theorem mem_kFinVec {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H} :
    v ∈ kFinVec ε σ ↔ IsKFin ε σ v := Iff.rfl

theorem isKStableOn_kFinVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (kFinVec ε σ) := by
  rintro g hg v ⟨S, hS, hv, hSK⟩
  exact ⟨S, hS, hSK g hg v hv, hSK⟩

structure IsGKSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) : Prop where
  smooth : ∀ v ∈ V, SmoothVec (lieSet ε) σ v
  kFin : ∀ v ∈ V, IsKFin ε σ v
  kStable : IsKStableOn ε σ V
  lieStable : ∀ X ∈ lieSet ε, ∀ v ∈ V, dRep σ X v ∈ V

def IsAdmissibleSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) : Prop :=
  ∀ Λ : Fin n → ℝ, FiniteDimensional ℂ (sSup {S | S ≤ V ∧ IsKTypeOf ε σ Λ S} : Submodule ℂ H)

def IsGKHom {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (ε : Fin n → Bool) (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁))
    (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)) (e : kFinVec ε σ₁ →ₗ[ℂ] kFinVec ε σ₂) : Prop :=
  (∀ k ∈ Kset ε, ∀ v w : kFinVec ε σ₁, (w : H₁) = σ₁ k v → (e w : H₂) = σ₂ k (e v)) ∧
    ∀ X ∈ lieSet ε, ∀ v w : kFinVec ε σ₁, (w : H₁) = dRep σ₁ X v → (e w : H₂) = dRep σ₂ X (e v)

theorem isGKHom_id (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsGKHom ε σ σ LinearMap.id :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

theorem isAdmissibleSub_of_finiteDimensional (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] : IsAdmissibleSub ε σ V :=
  fun _ => Submodule.finiteDimensional_of_le (sSup_le fun _ hS => hS.1)

theorem IsAdmissibleSub.mono {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V W : Submodule ℂ H}
    (h : IsAdmissibleSub ε σ W) (hle : V ≤ W) : IsAdmissibleSub ε σ V := fun Λ =>
  haveI := h Λ
  Submodule.finiteDimensional_of_le (sSup_le_sSup (t := {S | S ≤ W ∧ IsKTypeOf ε σ Λ S})
    fun _ hS => ⟨hS.1.trans hle, hS.2⟩)

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_det_expProd {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod).det := by
  have he : ∀ a b, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
      ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) a b := fun a b =>
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff.comp
      (GlobalTheory.GardingVec.contDiff_expProd Xs)
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun s _ => contDiff_const.mul (contDiff_prod fun i _ => he _ _)

end

theorem isURepOn_det (ε : Fin n → Bool) : IsURepOn (UJset ε) (fun g => g.det • (1 : H →L[ℂ] H)) := by
  refine ⟨⟨by simp, fun a _ b _ => by ext; simp [smul_smul, mul_comm]⟩, fun g hg v => ?_, fun v => ?_⟩
  · have h1 : ‖g.det‖ = 1 := by simpa using (GlobalTheory.Published.det_isURepOn ε).1.2.1 g hg 1
    simp [norm_smul, h1]
  · have : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => g.det • v :=
      (continuous_id.matrix_det).smul continuous_const
    simpa using this.continuousOn

theorem isGKSub_det (ε : Fin n → Bool) (V : Submodule ℂ H) [FiniteDimensional ℂ V] :
    IsGKSub ε (fun g => g.det • (1 : H →L[ℂ] H)) V ∧ IsAdmissibleSub ε (fun g => g.det • (1 : H →L[ℂ] H)) V := by
  have hK : IsKStableOn ε (fun g => g.det • (1 : H →L[ℂ] H)) V := fun g _ v hv => V.smul_mem _ hv
  refine ⟨⟨fun v _ k Xs _ => ?_, fun v hv => ⟨V, inferInstance, hv, hK⟩, hK, fun X _ v hv => ?_⟩,
    isAdmissibleSub_of_finiteDimensional _ _ _⟩
  · exact (contDiff_det_expProd Xs).smul contDiff_const
  · have h1 : ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • X)).det := by
      have := (contDiff_det_expProd (fun _ : Fin 1 => X)).comp
        (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun (t : ℝ) (_ : Fin 1) => t)
      simpa [Function.comp_def] using this
    have h2 := ((h1.differentiable (by simp)) 0).hasDerivAt.smul_const v
    have h3 : dRep (fun g => g.det • (1 : H →L[ℂ] H)) X v = _ := h2.deriv
    rw [h3]
    exact V.smul_mem _ hv

theorem mem_UJset_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ UJset ε := by
  have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  change kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem conjTranspose_mem_UJset_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ UJset ε := by
  have h1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk.1
  change kᴴᴴ * Jm ε * kᴴ = Jm ε
  rw [Matrix.conjTranspose_conjTranspose, hk.2, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem dRep_mem_of_isClosed {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {W : Submodule ℂ H}
    (hc : IsClosed (W : Set H)) (hW : ∀ g ∈ UJset ε, ∀ w ∈ W, σ g w ∈ W) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieSet ε) {v : H} (hv : v ∈ W) : dRep σ X v ∈ W := by
  have hm : ∀ t : ℝ, σ (NormedSpace.exp (t • X)) v ∈ W := fun t =>
    hW _ (GlobalTheory.GardingVec.exp_mem (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) hX t) v hv
  unfold dRep
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) 0
  · refine hc.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module]
    exact (W.restrictScalars ℝ).smul_mem _ (W.sub_mem (hm t) (hm 0))
  · rw [deriv_zero_of_not_differentiableAt hd]
    exact W.zero_mem

theorem starProjection_comm {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hU : IsURepOn (UJset ε) σ) {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : ∀ g ∈ UJset ε, ∀ w ∈ W, σ g w ∈ W) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : H) :
    W.starProjection (σ k x) = σ k (W.starProjection x) := by
  have hk1 := mem_UJset_of_mem_Kset hk
  have hk2 := conjTranspose_mem_UJset_of_mem_Kset hk
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hW k hk1 _ (W.starProjection_apply_mem x))
    fun w hw => ?_
  have h1 : σ k (σ kᴴ w) = w := by
    have := hU.1.2 k hk1 kᴴ hk2
    rw [show k * kᴴ = 1 from Matrix.mem_unitaryGroup_iff.1 hk.1, hU.1.1] at this
    exact (congrArg (fun A : H →L[ℂ] H => A w) this).symm
  let L : H →ₗᵢ[ℂ] H := ⟨(σ k : H →ₗ[ℂ] H), hU.2.1 k hk1⟩
  have h2 := L.inner_map_map (x - W.starProjection x) (σ kᴴ w)
  rw [W.starProjection_inner_eq_zero x _ (hW _ hk2 w hw)] at h2
  change inner ℂ (σ k (x - W.starProjection x)) (σ k (σ kᴴ w)) = 0 at h2
  rwa [h1, map_sub] at h2

end GlobalTheory.GKModule

namespace GlobalTheory.Published

open GlobalTheory.GKModule

def AdmissibleClosure : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    ∀ V : Submodule ℂ H, IsGKSub ε σ V → IsAdmissibleSub ε σ V →
      (∀ g ∈ UJset ε, ∀ w ∈ V.topologicalClosure, σ g w ∈ V.topologicalClosure) ∧
        ∀ w ∈ V.topologicalClosure, IsKFin ε σ w → w ∈ V

def InfinitesimalEquivalence : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool)
    (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [Nontrivial H₁]
    (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [Nontrivial H₂]
    (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)) (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)),
    IsURepOn (UJset ε) σ₁ → IsIrredOn (UJset ε) σ₁ → IsURepOn (UJset ε) σ₂ → IsIrredOn (UJset ε) σ₂ →
    ∀ e : kFinVec ε σ₁ ≃ₗ[ℂ] kFinVec ε σ₂, IsGKHom ε σ₁ σ₂ e.toLinearMap →
      ∃ (U : H₁ ≃ₗᵢ[ℂ] H₂) (c : ℝ), 0 < c ∧ (∀ g ∈ UJset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) ∧
        ∀ v : kFinVec ε σ₁, U v = (c : ℂ) • (e v : H₂)

def GKGlobalisation : Prop := AdmissibleClosure ∧ InfinitesimalEquivalence

section Consequences

variable {n : ℕ} {ε : Fin n → Bool}

theorem AdmissibleClosure.irreducible (h : AdmissibleClosure) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hU : IsURepOn (UJset ε) σ) {V : Submodule ℂ H} (hV : IsGKSub ε σ V) (hA : IsAdmissibleSub ε σ V)
    (hirr : ∀ V' ≤ V, IsGKSub ε σ V' → V' = ⊥ ∨ V' = V) {W : Submodule ℂ H} (hc : IsClosed (W : Set H))
    (hle : W ≤ V.topologicalClosure) (hW : ∀ g ∈ UJset ε, ∀ w ∈ W, σ g w ∈ W) :
    W = ⊥ ∨ W = V.topologicalClosure := by
  have hsub : IsGKSub ε σ (V ⊓ W) :=
    ⟨fun v hv => hV.smooth v hv.1, fun v hv => hV.kFin v hv.1,
      fun k hk v hv => ⟨hV.kStable k hk v hv.1, hW k (mem_UJset_of_mem_Kset hk) v hv.2⟩,
      fun X hX v hv => ⟨hV.lieStable X hX v hv.1, dRep_mem_of_isClosed hc hW hX hv.2⟩⟩
  rcases hirr _ inf_le_left hsub with h0 | h1
  · left
    have : CompleteSpace W := hc.completeSpace_coe
    have hperp : V ≤ Wᗮ := fun v hv => by
      obtain ⟨S, hS, hvS, hSK⟩ := hV.kFin v hv
      have hPW := W.starProjection_apply_mem v
      have hfin : IsKFin ε σ (W.starProjection v) := by
        refine ⟨S.map (W.starProjection : H →ₗ[ℂ] H), inferInstance, ⟨v, hvS, rfl⟩, ?_⟩
        rintro k hk _ ⟨x, hx, rfl⟩
        exact ⟨σ k x, hSK k hk x hx, starProjection_comm hU hW hk x⟩
      have hmem : W.starProjection v ∈ V ⊓ W := ⟨(h n ε H σ hU V hV hA).2 _ (hle hPW) hfin, hPW⟩
      rw [h0, Submodule.mem_bot] at hmem
      exact (Submodule.starProjection_apply_eq_zero_iff W).1 hmem
    have hcl : V.topologicalClosure ≤ Wᗮ := V.topologicalClosure_minimal hperp W.isClosed_orthogonal
    exact (W.orthogonal_disjoint).eq_bot_of_le (hle.trans hcl)
  · exact Or.inr (le_antisymm hle (V.topologicalClosure_minimal (inf_eq_left.1 h1) hc))

theorem infinitesimalEquivalence_hyp_det (ε : Fin n → Bool) :
    IsURepOn (UJset ε) (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) ∧ IsIrredOn (UJset ε) (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) ∧
      kFinVec ε (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) = ⊤ ∧
      IsGKHom ε (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) (fun g => g.det • (1 : ℂ →L[ℂ] ℂ))
        (LinearEquiv.refl ℂ _).toLinearMap :=
  ⟨(det_isURepOn ε).1, (det_isURepOn ε).2.1, eq_top_iff.2 fun v _ => (det_isURepOn ε).2.2 v, isGKHom_id _ _⟩

end Consequences

end GlobalTheory.Published

end
