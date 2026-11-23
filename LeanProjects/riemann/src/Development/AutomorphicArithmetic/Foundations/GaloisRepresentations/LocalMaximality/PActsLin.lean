import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private lemma muP_tmul (τ : DR ℂ K →ₗ[K] K) (w' w'' w : DR ℂ K) :
    muP F K τ (w' ⊗ₜ w'') w = (Algebra.trace F K (τ (w' * w))) ⊗ₜ[ℂ] w'' := by
  simp [muP]

private lemma mulP_tmul (f : F) (w : DR ℂ K) : mulP F K (f ⊗ₜ w) = algebraMap F K f • w := by
  simp [mulP]

private lemma actZ_tmul (a b : K) (w' w'' : DR ℂ K) :
    actZ K (a ⊗ₜ b) (w' ⊗ₜ w'') = (a • w') ⊗ₜ[ℂ] (b • w'') := by
  simp [actZ]
  rfl

private lemma key1 (τ : DR ℂ K →ₗ[K] K) (a b : K) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (w : DR ℂ K) :
    mulP F K (muP F K τ (actZ K (a ⊗ₜ b) m) w) = b • mulP F K (muP F K τ m (a • w)) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul w' w'' =>
    rw [actZ_tmul, muP_tmul, muP_tmul, mulP_tmul, mulP_tmul, smul_mul_assoc, mul_smul_comm]
    exact smul_comm _ _ _
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, smul_add]

private lemma key2 (τ : DR ℂ K →ₗ[K] K) (f : F) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (w : DR ℂ K) :
    mulP F K (muP F K τ m (algebraMap F K f • w)) = algebraMap F K f • mulP F K (muP F K τ m w) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul w' w'' =>
    rw [muP_tmul, muP_tmul, mulP_tmul, mulP_tmul, mul_smul_comm, map_smul, smul_eq_mul, ← Algebra.smul_def,
      map_smul, smul_eq_mul, map_mul, mul_smul]
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, smul_add, hp, hq]

private lemma key3 (τ : DR ℂ K →ₗ[K] K) (f g : F) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (w : DR ℂ K) :
    mulP F K (muP F K τ (actZ K (algebraMap F K f ⊗ₜ algebraMap F K g) m) w) =
      algebraMap F K (f * g) • mulP F K (muP F K τ m w) := by
  rw [key1, key2, ← mul_smul, ← map_mul, mul_comm g f]

private lemma sysP_act_tmul {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ) (f f' : F) (k : K) (w : DR ℂ K) :
    (sysP K x a).act (f ⊗ₜ k) (f' ⊗ₜ w) = (f * f') ⊗ₜ[ℂ] (k • w) := by
  simp [sysP]
  rfl

private lemma r_eq {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ) (i j : Fin (d + 1)) (l : Mi d) :
    (sysZ K x a).r n11 (sysZ K x a).mu i j l =
      algebraMap F K (x (ofLex l).1 / x i : Fˣ) ⊗ₜ algebraMap F K (x (ofLex l).2 / x j : Fˣ) -
      algebraMap F K (x (ofLex l).2 / x i : Fˣ) ⊗ₜ algebraMap F K (x (ofLex l).1 / x j : Fˣ) := by
  simp [Sys.r, Sys.mu, Sys.u, n11, sysZ, sub_mul, div_eq_mul_inv]

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.actsLin_of :
    ActsLin := by
  intro F K _ _ _ _ _ _ d x _ τ _ a
  have hadd : ∀ (m m' : DR ℂ K ⊗[ℂ] DR ℂ K) (c c' : K),
      Acts (F := F) K τ a m c → Acts (F := F) K τ a m' c' →
        Acts (F := F) K τ a (m + m') (c + c') ∧ Acts (F := F) K τ a (m - m') (c - c') := by
    intro m m' c c' hm hm'
    unfold Acts at hm hm' ⊢
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [map_add, LinearMap.add_apply, map_add, hm w hw, hm' w hw, add_smul]
    · rw [map_sub, LinearMap.sub_apply, map_sub, hm w hw, hm' w hw, sub_smul]
  have hr : ∀ (i j : Fin (d + 1)) (l : Mi d) (m : DR ℂ K ⊗[ℂ] DR ℂ K),
      Acts (F := F) K τ a (actZ K ((sysZ K x a).r n11 (sysZ K x a).mu i j l) m) 0 := by
    intro i j l m
    unfold Acts
    intro w _
    rw [r_eq, map_sub, LinearMap.sub_apply, map_sub, LinearMap.sub_apply, map_sub, key3, key3,
      ← Units.val_mul, ← Units.val_mul, div_mul_div_comm, div_mul_div_comm,
      mul_comm (x (ofLex l).1) (x (ofLex l).2), sub_self, zero_smul]
  have hsm : ∀ (i j : Fin (d + 1)) (M : Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K)),
      ∀ m ∈ sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)),
        Acts (F := F) K τ a m 0 := by
    intro i j M m hm
    let N : Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
      { carrier := {m | Acts (F := F) K τ a m 0}
        add_mem' := fun {m m'} hm hm' => by simpa using (hadd m m' 0 0 hm hm').1
        zero_mem' := by
          simp only [Set.mem_setOf_eq, Acts]
          intro w _
          simp
        smul_mem' := fun c m hm => by
          simp only [Set.mem_setOf_eq, Acts] at hm ⊢
          intro w hw
          rw [map_smul, LinearMap.smul_apply, map_smul, hm w hw]
          simp }
    have hle : sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) ≤ N := by
      unfold sm
      refine iSup₂_le fun s hs => ?_
      rintro _ ⟨u, _, rfl⟩
      obtain ⟨l, rfl⟩ := hs
      exact hr i j l u
    exact hle hm
  refine ⟨hadd, ?_, hsm, ?_, ?_, ?_⟩
  · intro m c s hm
    induction s using TensorProduct.induction_on with
    | zero =>
      unfold Acts
      intro w _
      simp
    | tmul p q =>
      unfold Acts at hm ⊢
      intro w hw
      rw [key1, hm _ (Submodule.smul_mem _ p hw)]
      simp only [Algebra.TensorProduct.lmul'_apply_tmul, smul_smul]
      congr 1
      ring
    | add s s' hs hs' =>
      simpa only [map_add, LinearMap.add_apply, add_mul] using (hadd _ _ _ _ hs hs').1
  · intro u M m i j hm
    apply hsm i j (M.map (actZ K u))
    have hle : sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) ≤
        (sm (actZ K) (M.map (actZ K u))
          (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j))).comap (actZ K u) := by
      unfold sm
      refine iSup₂_le fun s hs => ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [Submodule.mem_comap]
      refine Submodule.mem_iSup_of_mem s (Submodule.mem_iSup_of_mem hs ⟨actZ K u v, ⟨v, hv, rfl⟩, ?_⟩)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    exact hle hm
  · intro s m
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul f k =>
      induction m using TensorProduct.induction_on with
      | zero => simp
      | tmul f' w =>
        rw [sysP_act_tmul, mulP_tmul, mulP_tmul]
        simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
        rw [← algebraMap_smul K f' w, smul_smul]
        congr 1
        ring
      | add y z hy hz => simp only [map_add, smul_add, hy, hz]
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, add_smul, hy, hz]
  · intro s m w
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul f k =>
      induction m using TensorProduct.induction_on with
      | zero => simp
      | tmul w' w'' =>
        rw [Algebra.TensorProduct.map_tmul, actZ_tmul, muP_tmul, muP_tmul, sysP_act_tmul]
        simp only [IsScalarTower.coe_toAlgHom', AlgHom.coe_id, id_eq, smul_mul_assoc, map_smul,
          smul_eq_mul]
        rw [← Algebra.smul_def, map_smul, smul_eq_mul]
      | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
