import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFactorialBound
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.AnalyticClosure
open GlobalTheory.FockTensor

variable {p q : ℕ} {T : GrpData p q}

def restrictRep (πU : URep T) (K : Submodule ℂ πU.H) (hK : IsClosed (K : Set πU.H))
    (hinv : ∀ g, ∀ x ∈ K, πU.π g x ∈ K) : URep T :=
  haveI : CompleteSpace K := hK.completeSpace_coe
  { H := K
    π :=
      { toFun := fun g => ((πU.π g).comp K.subtypeL).codRestrict K (fun x => hinv g x x.2)
        map_one' := by ext x; simp
        map_mul' := fun a b => by ext x; simp; rfl }
    isom := fun g x => πU.isom g x
    cont := fun x => (πU.cont x).subtype_mk _ }

theorem inner_orbit_eq_zero (πU : URep T) {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (E : V →ₗ[ℂ] πU.H) {Y : Mat p q} (hY : Y ∈ upq p q)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (A x)) 0)
    (y : V) {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hb : ∀ k : ℕ, ‖E ((A ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (w : πU.H) (hw : ∀ v, inner ℂ w (E v) = 0) (t : ℝ) :
    inner ℂ w (πU.π (T.expt (t • Y)) (E y)) = 0 := by
  have key := GlobalTheory.FactorialJet.eq_zero_of_factorial_bound ℂ
    (fun k t => inner ℂ w (πU.π (T.expt (t • Y)) (E ((A ^ k) y)))) (‖w‖ * C) ρ
    (mul_nonneg (norm_nonneg _) hC) hρ ?_ ?_ ?_ 0 t
  · simpa using key
  · intro k s
    have h1 := hasDerivAt_orbit πU hY (hd ((A ^ k) y)) s
    have h2 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
    rw [pow_succ', Module.End.mul_apply]
    exact h2
  · intro k s
    refine (norm_inner_le_norm _ _).trans ?_
    rw [πU.isom, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← mul_assoc]
    exact hb k
  · intro k
    simp [T.expt_zero, hw]

theorem orbit_mem_closure (πU : URep T) {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (E : V →ₗ[ℂ] πU.H) {Y : Mat p q} (hY : Y ∈ upq p q)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (A x)) 0)
    (hb : ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧
      ∀ k : ℕ, ‖E ((A ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (t : ℝ) (x : πU.H) (hx : x ∈ (LinearMap.range E).topologicalClosure) :
    πU.π (T.expt (t • Y)) x ∈ (LinearMap.range E).topologicalClosure := by
  have h0 : ∀ y, πU.π (T.expt (t • Y)) (E y) ∈ (LinearMap.range E).topologicalClosure := by
    intro y
    obtain ⟨C, ρ, hC, hρ, h⟩ := hb y
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    refine inner_orbit_eq_zero πU A E hY hd y hC hρ h w (fun v => ?_) t
    exact (Submodule.mem_orthogonal' _ _).1 hw _ (LinearMap.mem_range_self _ v)
  have hcl : IsClosed ((πU.π (T.expt (t • Y))) ⁻¹'
      ((LinearMap.range E).topologicalClosure : Set πU.H)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (ContinuousLinearMap.continuous _)
  have hsub : ((LinearMap.range E : Submodule ℂ πU.H) : Set πU.H) ⊆
      (πU.π (T.expt (t • Y))) ⁻¹' ((LinearMap.range E).topologicalClosure : Set πU.H) := by
    rintro _ ⟨y, rfl⟩
    exact h0 y
  exact closure_minimal hsub hcl hx

theorem exists_subrep_closure : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (πU : URep T) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (E : V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (act Y x)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖E ((act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ (σ : URep T) (j : V →ₗ[ℂ] σ.H) (J : σ.H →ₗᵢ[ℂ] πU.H), Dense (Set.range j) ∧ (∀ x, J (j x) = E x) ∧ (∀ g y, J (σ.π g y) = πU.π g (J y)) ∧ (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (act Y x)) 0) := by
  intro p q T hgen πU V _ _ act E hd hb
  have hinv : ∀ g : T.G, ∀ x ∈ (LinearMap.range E).topologicalClosure,
      πU.π g x ∈ (LinearMap.range E).topologicalClosure := by
    intro g
    have hg : g ∈ Subgroup.closure (T.expt '' upq p q) := by rw [hgen]; trivial
    induction hg using Subgroup.closure_induction'' with
    | mem g hg =>
      obtain ⟨Y, hY, rfl⟩ := hg
      intro x hx
      simpa using orbit_mem_closure πU (act Y) E hY (hd Y hY) (hb Y hY) 1 x hx
    | inv_mem g hg =>
      obtain ⟨Y, hY, rfl⟩ := hg
      intro x hx
      have he : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
        have := T.expt_add Y hY 1 (-1)
        rw [add_neg_cancel, zero_smul, one_smul, T.expt_zero] at this
        exact inv_eq_of_mul_eq_one_right this.symm
      rw [he]
      exact orbit_mem_closure πU (act Y) E hY (hd Y hY) (hb Y hY) (-1) x hx
    | one => intro x hx; simpa using hx
    | mul a b _ _ ha hb' =>
      intro x hx
      rw [map_mul, ContinuousLinearMap.mul_apply]
      exact ha _ (hb' x hx)
  set K := (LinearMap.range E).topologicalClosure with hKdef
  have hK : IsClosed (K : Set πU.H) := Submodule.isClosed_topologicalClosure _
  have hmem : ∀ x, E x ∈ K := fun x =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)
  refine ⟨restrictRep πU K hK hinv, E.codRestrict K hmem, K.subtypeₗᵢ, ?_, fun x => rfl,
    fun g y => rfl, ?_⟩
  · show Dense (Set.range (E.codRestrict K hmem : V → K))
    rw [Subtype.dense_iff]
    intro x hx
    have : (Subtype.val '' Set.range (E.codRestrict K hmem : V → K)) =
        ((LinearMap.range E : Submodule ℂ πU.H) : Set πU.H) := by
      rw [← Set.range_comp, LinearMap.coe_range]; rfl
    exact this ▸ (hx : x ∈ closure ((LinearMap.range E : Submodule ℂ πU.H) : Set πU.H))
  · intro Y hY x
    have h := hd Y hY x
    rw [hasDerivAt_iff_isLittleO_nhds_zero, ← Asymptotics.isLittleO_norm_left] at h ⊢
    exact h

end GlobalTheory.AnalyticClosure
