import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.Burnside

theorem span_top_of_residue {G O n : Type} [CommRing O] [IsLocalRing O] [Fintype n] [DecidableEq n] (T : G → Matrix n n O)
    (h : Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => (T g).map (IsLocalRing.residue O)) = ⊤) :
    Submodule.span O (Set.range T) = ⊤ := by
  have hB : ∀ B : Matrix n n (IsLocalRing.ResidueField O), ∃ M ∈ Submodule.span O (Set.range T),
      M.map (IsLocalRing.residue O) = B := fun B => by
    have hM : B ∈ Submodule.span (IsLocalRing.ResidueField O)
        (Set.range fun g => (T g).map (IsLocalRing.residue O)) := h ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨g, rfl⟩ := hB
      exact ⟨T g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, Matrix.map_zero _ (map_zero _)⟩
    | add B B' _ _ h h' =>
      obtain ⟨M, hM, rfl⟩ := h
      obtain ⟨M', hM', rfl⟩ := h'
      exact ⟨M + M', Submodule.add_mem _ hM hM', Matrix.map_add _ (map_add _) _ _⟩
    | smul t B _ h =>
      obtain ⟨M, hM, rfl⟩ := h
      obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
      exact ⟨t • M, Submodule.smul_mem _ _ hM, by ext p q; simp⟩
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O) Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson _) fun M _ => ?_
  obtain ⟨M', hM', e⟩ := hB (M.map (IsLocalRing.residue O))
  have e1 : M = M' + (M - M') := by abel
  rw [e1]
  refine Submodule.add_mem_sup hM' ?_
  rw [Matrix.matrix_eq_sum_single (M - M')]
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
  have e2 : Matrix.single p q ((M - M') p q) = (M - M') p q • Matrix.single p q (1 : O) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e2]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [← IsLocalRing.residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
  exact (congrFun (congrFun e p) q).symm

theorem eq_top_of_map {G O A n : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype n] [DecidableEq n]
    (T : G → Matrix n n O) (h : Submodule.span O (Set.range T) = ⊤) (S : Submodule A (Matrix n n A))
    (hS : ∀ g, (T g).map (algebraMap O A) ∈ S) : S = ⊤ := by
  have hB : ∀ B : Matrix n n O, B.map (algebraMap O A) ∈ S := fun B => by
    have hM : B ∈ Submodule.span O (Set.range T) := h ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨g, rfl⟩ := hB
      exact hS g
    | zero => rw [Matrix.map_zero _ (map_zero _)]; exact Submodule.zero_mem _
    | add B B' _ _ h h' => rw [Matrix.map_add _ (map_add _)]; exact Submodule.add_mem _ h h'
    | smul t B _ h =>
      have : (t • B).map (algebraMap O A) = algebraMap O A t • B.map (algebraMap O A) := by ext p q; simp
      rw [this]
      exact Submodule.smul_mem _ _ h
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
  have : Matrix.single p q (M p q) = M p q • (Matrix.single p q (1 : O)).map (algebraMap O A) := by
    rw [Matrix.map_single, map_one, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (hB _)

theorem span_twist_eq_top : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Submodule.span A (Set.range fun g => ((κ g : Aˣ) : A) • (Tmat i s g).map (algebraMap (X.O0 i) A)) = ⊤ := by
  intro D N X bkP i s A _ _ _ _ κ Q hS
  refine eq_top_of_map (fun g => ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)))
    (span_top_of_residue _ hS.1.2.1.1) _ fun g => ?_
  have : ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) A) =
      (algebraMap (X.O0 i) A ((chiS i s g : (X.O0 i)ˣ) : X.O0 i) * (((κ g)⁻¹ : Aˣ) : A)) •
        (((κ g : Aˣ) : A) • (Tmat i s g).map (algebraMap (X.O0 i) A)) := by
    rw [smul_smul, Units.inv_mul_cancel_right]
    ext p q
    simp only [Tmat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← map_mul, Units.mul_inv_cancel_left]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end GlobalTheory.NewPrime.Burnside
