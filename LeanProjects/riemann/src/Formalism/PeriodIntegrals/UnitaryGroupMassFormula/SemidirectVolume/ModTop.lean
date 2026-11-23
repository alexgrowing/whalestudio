import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjCont

noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct Matrix

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

def sigRLin : R ⊗[F] E →ₗ[R] R ⊗[F] E :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : R →ₗ[R] R) σ.toLinearMap

theorem sigRLin_eq (x : R ⊗[F] E) : sigRLin R σ x = sigR R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigRLin, sigR]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable [IsTopologicalRing (R ⊗[F] E)]

theorem continuous_sigR : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (sigRLin R σ) := IsModuleTopology.continuous_of_linearMap _
  have he : (sigR R σ : R ⊗[F] E → R ⊗[F] E) = sigRLin R σ :=
    funext fun x => (sigRLin_eq R σ x).symm
  rw [he]
  exact hc

theorem continuous_hR {X : Type} [TopologicalSpace X] {u v : X → Fin M → R ⊗[F] E}
    (hu : Continuous u) (hv : Continuous v) : Continuous fun x => hR R σ J (u x) (v x) := by
  unfold hR Formalism.UG.hform
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (((continuous_sigR R σ).comp ((continuous_apply i).comp hu)).mul continuous_const).mul
    ((continuous_apply j).comp hv)

theorem continuous_linMap {X : Type} [TopologicalSpace X]
    (f : (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin M → R ⊗[F] E)) {v : X → Fin M → R ⊗[F] E}
    (hv : Continuous v) : Continuous fun x => f (v x) := by
  have key : (fun x => f (v x)) =
      fun x => ∑ j, v x j • f (fun k => if j = k then (1 : R ⊗[F] E) else 0) := by
    funext x
    conv_lhs => rw [pi_eq_sum_univ (v x)]
    rw [map_sum]
    simp only [map_smul]
  rw [key]
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_apply j).comp hv).smul continuous_const

theorem continuous_linear_action {X : Type} [TopologicalSpace X] {g : X → HA R σ J}
    {v : X → Fin M → R ⊗[F] E} (hg : Continuous g) (hv : Continuous v) :
    Continuous fun x => lin R σ J (g x) (v x) := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  unfold lin
  simp only [Matrix.mulVecLin_apply]
  exact (hm.comp hg).matrix_mulVec hv

theorem continuous_L_apply {X : Type} [TopologicalSpace X]
    {w : X → Fin r → Fin M → R ⊗[F] E} {s : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hs : Continuous s) (v : Fin M → R ⊗[F] E) :
    Continuous fun x => (datR R σ J P T).L (w x) (s x) v := by
  set D := datR R σ J P T with hD
  have key : (fun x => D.L (w x) (s x) v) = fun x =>
      v + ∑ b, D.hL (D.e b) v • (w x b + ∑ a, s x a b • D.e a) - ∑ a, D.hL (w x a) (D.pW v) • D.e a := by
    funext x
    simp only [PI.VolSemiDirect.W.PG.Dat.L, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply]
  rw [key]
  have hh : ∀ (c : Fin M → R ⊗[F] E), Continuous fun u : Fin M → R ⊗[F] E => D.hL u c := by
    intro c
    first
      | exact continuous_hR R σ J (u := fun u => u) (v := fun _ => c) continuous_id continuous_const
      | exact continuous_hR R σ J (u := fun _ => c) (v := fun u => u) continuous_const continuous_id
  have hA : ∀ b : Fin r, Continuous fun x => w x b + ∑ a, s x a b • D.e a := by
    intro b
    have h1 : Continuous fun x => w x b := (continuous_apply b).comp hw
    have h2 : ∀ a : Fin r, Continuous fun x => s x a b • D.e a := by
      intro a
      have h3 : Continuous fun x => s x a b := (continuous_apply b).comp ((continuous_apply a).comp hs)
      exact h3.smul continuous_const
    exact h1.add (continuous_finset_sum _ fun a _ => h2 a)
  have hB : ∀ b : Fin r, Continuous fun x => D.hL (D.e b) v • (w x b + ∑ a, s x a b • D.e a) := by
    intro b
    exact (continuous_const (y := D.hL (D.e b) v)).smul (hA b)
  have hC : ∀ a : Fin r, Continuous fun x => D.hL (w x a) (D.pW v) • D.e a := by
    intro a
    have h4 : Continuous fun x => D.hL (w x a) (D.pW v) := (hh (D.pW v)).comp ((continuous_apply a).comp hw)
    exact h4.smul continuous_const
  exact (continuous_const.add (continuous_finset_sum _ fun b _ => hB b)).sub
    (continuous_finset_sum _ fun a _ => hC a)

theorem continuous_toMatrix'_L {X : Type} [TopologicalSpace X]
    {w : X → Fin r → Fin M → R ⊗[F] E} {s : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hs : Continuous s) :
    Continuous fun x => LinearMap.toMatrix' ((datR R σ J P T).L (w x) (s x)) := by
  refine continuous_matrix fun i j => ?_
  first
    | exact (continuous_apply i).comp (continuous_L_apply R σ J P T hw hs _)
    | (simp only [LinearMap.toMatrix'_apply]
       exact (continuous_apply i).comp (continuous_L_apply R σ J P T hw hs _))

end Cont

section HAcont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem mat_inv_eq (hJ : IsHermND σ J) (g : HA R σ J) :
    ((HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (J⁻¹).map (inclR (F := F) R) *
        Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) :
          Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J := by
  obtain ⟨_, hdet⟩ := hJ
  set A : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
    ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) with hA
  set B : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
    ((HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) with hB
  set Ji : Matrix (Fin M) (Fin M) (R ⊗[F] E) := (J⁻¹).map (inclR (F := F) R) with hJi
  have hmem : Formalism.UG.cT (sigR R σ) A * JR (F := F) R J * A = JR (F := F) R J := g.2
  have hAB : A * B = 1 := by
    have e : (HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) = (HA.mat R σ J g)⁻¹ := by
      first
        | rfl
        | exact Subgroup.coe_inv _
    rw [hA, hB, e]
    exact Units.mul_inv _
  have hJJ : Ji * JR (F := F) R J = 1 := by
    rw [hJi]
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.mpr hdet)]
    simp
  calc B = (Ji * JR (F := F) R J) * B := by rw [hJJ, Matrix.one_mul]
    _ = Ji * (Formalism.UG.cT (sigR R σ) A * JR (F := F) R J * A) * B := by rw [hmem]
    _ = Ji * Formalism.UG.cT (sigR R σ) A * JR (F := F) R J * (A * B) := by simp only [Matrix.mul_assoc]
    _ = Ji * Formalism.UG.cT (sigR R σ) A * JR (F := F) R J := by rw [hAB, Matrix.mul_one]

variable [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]

theorem continuous_into_HA (hJ : IsHermND σ J) {X : Type} [TopologicalSpace X] {f : X → HA R σ J}
    (hf : Continuous fun x => ((HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E))) : Continuous f := by
  have hcT : Continuous fun x => Formalism.UG.cT (sigR R σ)
      ((HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
    refine continuous_matrix fun i j => ?_
    exact (continuous_sigR R σ).comp (hf.matrix_elem j i)
  have hI : Continuous fun x =>
      ((HA.mat R σ J (f x)⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
    have e : (fun x =>
        ((HA.mat R σ J (f x)⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) =
        fun x => (J⁻¹).map (inclR (F := F) R) *
          Formalism.UG.cT (sigR R σ) ((HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) :
            Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J :=
      funext fun x => mat_inv_eq hJ (f x)
    rw [e]
    exact (continuous_const.matrix_mul hcT).matrix_mul continuous_const
  have hGL : Continuous fun x => (HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) :=
    Units.continuous_iff.2 ⟨hf, hI⟩
  first
    | exact continuous_induced_rng.2 hGL
    | exact hGL.subtype_mk fun x => (f x).2

end HAcont

section Raw

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)] (σ : E →ₐ[F] E)
  {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

theorem continuous_phiW_raw :
    Continuous fun n : FrameUnipotentSubgroup R σ J P => fun b : Fin r =>
      (datR R σ J P T).pW (lin R σ J (n : HA R σ J) (ratV (F := F) R (P.f b))) := by
  refine continuous_pi fun b => ?_
  exact continuous_linMap R _
    (continuous_linear_action R σ J (v := fun _ => ratV (F := F) R (P.f b)) continuous_subtype_val continuous_const)

theorem continuous_phiS_raw :
    Continuous fun n : FrameUnipotentSubgroup R σ J P => fun a b : Fin r =>
      hR R σ J (ratV (F := F) R (P.f a)) (lin R σ J (n : HA R σ J) (ratV (F := F) R (P.f b))) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact continuous_hR R σ J (u := fun _ => ratV (F := F) R (P.f a))
    (v := fun n : FrameUnipotentSubgroup R σ J P => lin R σ J (n : HA R σ J) (ratV (F := F) R (P.f b))) continuous_const
    (continuous_linear_action R σ J continuous_subtype_val continuous_const)

theorem continuous_gram_shift {X : Type} [TopologicalSpace X] (κ : R ⊗[F] E)
    {w : X → Fin r → Fin M → R ⊗[F] E} {c : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hc : Continuous c) :
    Continuous fun x => fun a b : Fin r => c x a b - κ * hR R σ J (w x a) (w x b) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact ((continuous_apply b).comp ((continuous_apply a).comp hc)).sub
    (continuous_const.mul (continuous_hR R σ J ((continuous_apply a).comp hw) ((continuous_apply b).comp hw)))

theorem continuous_gram_add {X : Type} [TopologicalSpace X] (κ : R ⊗[F] E)
    {w : X → Fin r → Fin M → R ⊗[F] E} {c : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hc : Continuous c) :
    Continuous fun x => fun a b : Fin r => c x a b + κ * hR R σ J (w x a) (w x b) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact ((continuous_apply b).comp ((continuous_apply a).comp hc)).add
    (continuous_const.mul (continuous_hR R σ J ((continuous_apply a).comp hw) ((continuous_apply b).comp hw)))

end Raw

end PI.VolSemiDirect.W.Md
