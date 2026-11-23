import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.DiffLatFree
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

section Step

variable {Em K : Type} [Field Em] [NumberField Em] [Field K] [NumberField K] {N : ℕ}

theorem absNorm_map_mapRingHom (s : Em →+* K) (b : Ideal (𝓞 Em)) :
    letI : Algebra Em K := s.toAlgebra
    Ideal.absNorm (b.map (RingOfIntegers.mapRingHom s)) = Ideal.absNorm b ^ Module.finrank Em K := by
  let _ : Algebra Em K := s.toAlgebra
  have h1 : RingOfIntegers.mapRingHom s = algebraMap (𝓞 Em) (𝓞 K) := rfl
  have h3 : Module.finrank (𝓞 Em) (𝓞 K) = Module.finrank Em K :=
    (IsFractionRing.finrank_eq (𝓞 Em) Em (𝓞 K) K).symm
  rw [h1, Ideal.absNorm_algebraMap, h3]

omit [NumberField Em] in

theorem span_singleton_toAddSubgroup (x : Fin N → Em) :
    (Submodule.span (𝓞 Em) {x}).toAddSubgroup =
      (⊤ : AddSubgroup (𝓞 Em)).map (LinearMap.toSpanSingleton (𝓞 Em) _ x).toAddMonoidHom := by
  ext y
  simp [Submodule.mem_span_singleton]

omit [NumberField K] in
theorem map_toAddSubgroup' (f : 𝓞 K →ₗ[𝓞 K] (Fin N → K)) (D : Ideal (𝓞 K)) :
    (Submodule.map f D).toAddSubgroup = D.toAddSubgroup.map f.toAddMonoidHom := by
  ext y
  simp

theorem relIndex_mul_ideal {F : Type} [Field F] [NumberField F] (D B : Ideal (𝓞 F)) (hD : Ideal.absNorm D ≠ 0) :
    (D * B).toAddSubgroup.relIndex D.toAddSubgroup = Ideal.absNorm B := by
  have h := AddSubgroup.relIndex_mul_index (H := (D * B).toAddSubgroup) (K := D.toAddSubgroup)
    (Submodule.toAddSubgroup_mono Ideal.mul_le_left)
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, map_mul] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hD) (by rw [h, mul_comm])

theorem diffLat_step (s : Em →+* K) (P : Submodule (𝓞 Em) (Fin N → Em)) (x : Fin N → Em)
    (hP : P.toAddSubgroup.relIndex (P ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup ≠ 0) :
    letI : Algebra Em K := s.toAlgebra
    (diffLat s P).toAddSubgroup.relIndex (diffLat s (P ⊔ Submodule.span (𝓞 Em) {x})).toAddSubgroup ≤
      P.toAddSubgroup.relIndex (P ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup ^ Module.finrank Em K := by
  let _ : Algebra Em K := s.toAlgebra
  let g : 𝓞 Em →ₗ[𝓞 Em] (Fin N → Em) := LinearMap.toSpanSingleton (𝓞 Em) _ x
  let f : 𝓞 K →ₗ[𝓞 K] (Fin N → K) := LinearMap.toSpanSingleton (𝓞 K) _ (fun i => s (x i))
  let b : Ideal (𝓞 Em) := P.comap g
  have hPQ : P.toAddSubgroup.relIndex (P ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup = Ideal.absNorm b := by
    rw [Submodule.sup_toAddSubgroup, span_singleton_toAddSubgroup, AddSubgroup.relIndex_sup_left,
      ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, Ideal.absNorm_eq_index]
    rfl
  have hXQ : diffLat s (P ⊔ Submodule.span (𝓞 Em) {x}) =
      diffLat s P ⊔ Submodule.map f (extDifferent s) := by
    apply le_antisymm
    · rw [diffLat, Submodule.span_le]
      rintro _ ⟨u, ⟨y, hy, z, hz, rfl⟩, rfl⟩
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hq
      have e : (fun i => s (((y : Em) • (p + c • x)) i)) =
          (fun i => s (((y : Em) • p) i)) + f (RingOfIntegers.mapRingHom s (y * c)) := by
        funext i
        simp [f, Algebra.smul_def, mul_add, mul_assoc]
      show (fun i => s (((y : Em) • (p + c • x)) i)) ∈ _
      rw [e]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, ⟨y, hy, p, hp, rfl⟩, rfl⟩)
        (Submodule.mem_map_of_mem (Ideal.mem_map_of_mem _ (Ideal.mul_mem_right c _ hy)))
    · refine sup_le (diffLat_mono s le_sup_left) ?_
      rw [Submodule.map_le_iff_le_comap, extDifferent, Ideal.map_le_iff_le_comap]
      intro y hy
      simp only [Ideal.mem_comap, Submodule.mem_comap, f, LinearMap.toSpanSingleton_apply]
      apply Submodule.subset_span
      refine ⟨(y : Em) • x, ⟨y, hy, x, Submodule.mem_sup_right (Submodule.mem_span_singleton_self x), rfl⟩, ?_⟩
      funext i
      simp [Algebra.smul_def]
  have h1 : (diffLat s P).toAddSubgroup.relIndex (diffLat s (P ⊔ Submodule.span (𝓞 Em) {x})).toAddSubgroup =
      ((diffLat s P).toAddSubgroup.comap f.toAddMonoidHom).relIndex (extDifferent s).toAddSubgroup := by
    rw [hXQ, Submodule.sup_toAddSubgroup, map_toAddSubgroup', AddSubgroup.relIndex_sup_left,
      AddSubgroup.relIndex_comap]
  have h2 : extDifferent s * b.map (RingOfIntegers.mapRingHom s) ≤ (diffLat s P).comap f := by
    rw [extDifferent, ← Ideal.map_mul, Ideal.map_le_iff_le_comap]
    refine Ideal.mul_le.2 fun y hy c hc => ?_
    have hc' : c • x ∈ P := hc
    simp only [Ideal.mem_comap, Submodule.mem_comap, f, LinearMap.toSpanSingleton_apply]
    apply Submodule.subset_span
    refine ⟨(y : Em) • (c • x), ⟨y, hy, c • x, hc', rfl⟩, ?_⟩
    funext i
    simp [Algebra.smul_def, mul_assoc]
  have hD : Ideal.absNorm (extDifferent s) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact extDifferent_ne_bot s
  have h3 : (extDifferent s * b.map (RingOfIntegers.mapRingHom s)).toAddSubgroup.relIndex
      (extDifferent s).toAddSubgroup = Ideal.absNorm (b.map (RingOfIntegers.mapRingHom s)) := by
    exact relIndex_mul_ideal _ _ hD
  have h4 := absNorm_map_mapRingHom s b
  rw [h1, hPQ, ← h4, ← h3]
  refine AddSubgroup.relIndex_le_of_le_left (fun z hz => h2 hz) ?_
  rw [h3, h4]
  exact pow_ne_zero _ (hPQ ▸ hP)

theorem diffLat_relIndex_le (s : Em →+* K) {M' M : Submodule (𝓞 Em) (Fin N → Em)} (hle : M' ≤ M) (hfg : M.FG)
    (hM : M'.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0) :
    letI : Algebra Em K := s.toAlgebra
    (diffLat s M').toAddSubgroup.relIndex (diffLat s M).toAddSubgroup ≤
      M'.toAddSubgroup.relIndex M.toAddSubgroup ^ Module.finrank Em K := by
  classical
  let _ : Algebra Em K := s.toAlgebra
  obtain ⟨T, hT⟩ := hfg
  have hTM : (↑T : Set (Fin N → Em)) ⊆ M := hT ▸ Submodule.subset_span
  have key : ∀ T : Finset (Fin N → Em), (↑T : Set (Fin N → Em)) ⊆ M →
      (diffLat s M').toAddSubgroup.relIndex (diffLat s (M' ⊔ Submodule.span (𝓞 Em) ↑T)).toAddSubgroup ≤
        M'.toAddSubgroup.relIndex (M' ⊔ Submodule.span (𝓞 Em) ↑T).toAddSubgroup ^ Module.finrank Em K := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert x T hx ih =>
      intro hT'
      have hxM : x ∈ M := hT' (Finset.mem_insert_self _ _)
      have hTM' : (↑T : Set (Fin N → Em)) ⊆ M := fun y hy => hT' (Finset.mem_insert_of_mem hy)
      have hPeq : M' ⊔ Submodule.span (𝓞 Em) ↑(insert x T) =
          (M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x} := by
        rw [Finset.coe_insert, Submodule.span_insert, sup_comm (Submodule.span (𝓞 Em) {x}), ← sup_assoc]
      rw [hPeq]
      have hP_le : M' ⊔ Submodule.span (𝓞 Em) ↑T ≤ M := sup_le hle (Submodule.span_le.2 hTM')
      have hPx_le : (M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x} ≤ M :=
        sup_le hP_le (Submodule.span_le.2 (Set.singleton_subset_iff.2 hxM))
      have hne : M'.toAddSubgroup.relIndex
          ((M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup ≠ 0 :=
        fun h => hM (AddSubgroup.relIndex_eq_zero_of_le_right hPx_le h)
      have hmul := AddSubgroup.relIndex_mul_relIndex M'.toAddSubgroup
        (M' ⊔ Submodule.span (𝓞 Em) ↑T).toAddSubgroup
        ((M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup
        (le_sup_left : M' ≤ _) (le_sup_left : M' ⊔ Submodule.span (𝓞 Em) ↑T ≤ _)
      have hstep : (M' ⊔ Submodule.span (𝓞 Em) ↑T).toAddSubgroup.relIndex
          ((M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup ≠ 0 :=
        fun h => hne (by rw [← hmul, h, mul_zero])
      have hX := AddSubgroup.relIndex_mul_relIndex (diffLat s M').toAddSubgroup
        (diffLat s (M' ⊔ Submodule.span (𝓞 Em) ↑T)).toAddSubgroup
        (diffLat s ((M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x})).toAddSubgroup
        (diffLat_mono s le_sup_left) (diffLat_mono s le_sup_left)
      rw [← hX, ← hmul, mul_pow]
      exact Nat.mul_le_mul (ih hTM') (diffLat_step s _ x hstep)
  have hM_eq : M = M' ⊔ Submodule.span (𝓞 Em) ↑T := by rw [hT, sup_eq_right.2 (hT ▸ hle)]
  rw [hM_eq] at hM ⊢
  exact key T hTM

end Step

end GroundTheory.Heights₂.Heights.NineStatements
