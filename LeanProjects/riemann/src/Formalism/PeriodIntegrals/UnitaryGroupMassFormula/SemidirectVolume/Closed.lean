import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct Matrix

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem continuous_lin [IsTopologicalRing (R ⊗[F] E)] (x : Fin n → R ⊗[F] E) :
    Continuous fun g : HA R σ J => lin R σ J g x := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  simp only [lin, Matrix.mulVecLin_apply]
  exact hm.matrix_mulVec continuous_const

theorem exists_proj_mat (K : Submodule E (Fin n → E)) :
    ∃ P : Matrix (Fin n) (Fin n) E, (∀ x, P *ᵥ x ∈ K) ∧ ∀ x ∈ K, P *ᵥ x = x := by
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl K
  refine ⟨LinearMap.toMatrix' (K.subtype ∘ₗ Submodule.linearProjOfIsCompl K K' hK), fun x => ?_, fun x hx => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    exact (Submodule.linearProjOfIsCompl K K' hK x).2
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply]
    have := Submodule.linearProjOfIsCompl_apply_left hK ⟨x, hx⟩
    exact congrArg Subtype.val this

variable {R}

theorem ratV_mem_spanR {m : ℕ} (Y : Fin m → Fin n → E) (s : Set (Fin m)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (Y '' s)) : ratV (F := F) R x ∈ spanR (F := F) R Y s := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero =>
    have h0 : ratV (F := F) R (0 : Fin n → E) = 0 := by
      funext i
      simp [ratV]
    rw [h0]
    exact zero_mem _
  | add x y _ _ hx hy =>
    have h0 : ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
      funext i
      simp [ratV]
    rw [h0]
    exact add_mem hx hy
  | smul c x _ hx =>
    have h0 : ratV (F := F) R (c • x) = inclR (F := F) R c • ratV (F := F) R x := by
      funext i
      simp [ratV]
    rw [h0]
    exact Submodule.smul_mem _ _ hx

theorem ratV_mulVec (P : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    ratV (F := F) R (P *ᵥ x) = (P.map (inclR (F := F) R)) *ᵥ ratV (F := F) R x := by
  funext i
  simp [ratV, Matrix.mulVec, dotProduct, map_sum]

theorem mem_spanR_iff {m : ℕ} (Y : Fin m → Fin n → E) (s : Set (Fin m))
    (P : Matrix (Fin n) (Fin n) E) (hP1 : ∀ x, P *ᵥ x ∈ Submodule.span E (Y '' s))
    (hP2 : ∀ x ∈ Submodule.span E (Y '' s), P *ᵥ x = x) (v : Fin n → R ⊗[F] E) :
    v ∈ spanR (F := F) R Y s ↔ (P.map (inclR (F := F) R)) *ᵥ v = v := by
  have hfix : ∀ a ∈ s, (P.map (inclR (F := F) R)) *ᵥ ratV (F := F) R (Y a) = ratV (F := F) R (Y a) := by
    intro a ha
    rw [← ratV_mulVec, hP2 _ (Submodule.subset_span ⟨a, ha, rfl⟩)]
  have hsingle : ∀ j : Fin n, ratV (F := F) R (Pi.single j (1 : E)) = Pi.single j 1 := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij
      simp [ratV]
    · simp [ratV, Pi.single_apply, hij]
  constructor
  · intro hv
    have hle : spanR (F := F) R Y s ≤ LinearMap.eqLocus (Matrix.mulVecLin (P.map (inclR (F := F) R))) LinearMap.id := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, ha, rfl⟩
      exact hfix a ha
    exact hle hv
  · intro h
    rw [← h]
    have hv : v = ∑ j, v j • Pi.single j (1 : R ⊗[F] E) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ ?_
    have := ratV_mem_spanR (F := F) (R := R) Y s _ (hP1 (Pi.single j 1))
    rwa [ratV_mulVec, hsingle] at this

theorem isClosed_spanR [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {m : ℕ}
    (Y : Fin m → Fin n → E) (s : Set (Fin m)) :
    IsClosed (spanR (F := F) R Y s : Set (Fin n → R ⊗[F] E)) := by
  obtain ⟨P, h1, h2⟩ := exists_proj_mat (Submodule.span E (Y '' s))
  have hset : (spanR (F := F) R Y s : Set (Fin n → R ⊗[F] E)) =
      {v | (P.map (inclR (F := F) R)) *ᵥ v = v} := by
    ext v
    exact mem_spanR_iff (F := F) (R := R) Y s P h1 h2 v
  rw [hset]
  exact isClosed_eq (continuous_const.matrix_mulVec continuous_id) continuous_id

variable (R)

theorem isClosed_stabT [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {a : ℕ}
    (X : Fin a → Fin n → E) : IsClosed (stabT R σ J X : Set (HA R σ J)) := by
  have hset : (stabT R σ J X : Set (HA R σ J)) =
      ⋂ b, {g | lin R σ J g (ratV (F := F) R (X b)) = ratV (F := F) R (X b)} := by
    ext g
    simp [mem_stabT]
  rw [hset]
  exact isClosed_iInter fun b => isClosed_eq (continuous_lin R σ J _) continuous_const

theorem isClosed_Nsub [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {r : ℕ}
    (P : Frame E n r) : IsClosed (Nsub R σ J P : Set (HA R σ J)) := by
  have hset : (Nsub R σ J P : Set (HA R σ J)) =
      (⋂ b, {g | lin R σ J g (ratV (F := F) R (P.e b)) - ratV (F := F) R (P.e b) ∈
        spanR (F := F) R P.e {a | a < b}}) ∩
      ⋂ v, ⋂ (_ : InXperp R σ J P v), {g | lin R σ J g v - v ∈ spanR (F := F) R P.e Set.univ} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [hset]
  exact (isClosed_iInter fun b => (isClosed_spanR _ _).preimage ((continuous_lin R σ J _).sub continuous_const)).inter
    (isClosed_iInter fun v => isClosed_iInter fun _ =>
      (isClosed_spanR _ _).preimage ((continuous_lin R σ J v).sub continuous_const))

end Gen

theorem closedStep_of (hT : TensTop) : ClosedStep := by
  intro F E _ _ _ _ _ σ _ M J _ r P T _ _
  obtain ⟨h1, h2, _, _⟩ := hT F E
  refine ⟨isClosed_stabT _ σ J _, ?_, isClosed_stabT _ σ J _⟩
  show IsClosed ((Nsub (AF F) σ J P ⊓ S0 (AF F) σ J P : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J))
  rw [Subgroup.coe_inf]
  exact (isClosed_Nsub _ σ J P).inter (isClosed_stabT _ σ J _)

end PI.VolSemiDirect.W
