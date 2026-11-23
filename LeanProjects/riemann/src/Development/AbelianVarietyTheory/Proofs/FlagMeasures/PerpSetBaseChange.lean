import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Formalism.HarderNarasimhan.ShiftInvariance

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.PerpBaseChange

private theorem dual_span_sum_eq_zero {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (S : Set (Module.Dual E (Fin n → E))) (u : Fin n → A)
    (hu : ∀ φ ∈ S, ∑ j, ι (φ (Pi.single j 1)) * u j = 0) :
    ∀ ψ ∈ Submodule.span E S, ∑ j, ι (ψ (Pi.single j 1)) * u j = 0 := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx => exact hu x hx
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [LinearMap.add_apply, map_add, add_mul, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul c x _ hx =>
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, mul_assoc]
    rw [← Finset.mul_sum, hx, mul_zero]

theorem mem_span_of_forms {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (S : Set (Module.Dual E (Fin n → E))) (u : Fin n → A)
    (hu : ∀ φ ∈ S, ∑ j, ι (φ (Pi.single j 1)) * u j = 0) :
    u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' {y | ∀ φ ∈ S, φ y = 0}) := by
  classical

  set D : Submodule E (Module.Dual E (Fin n → E)) := Submodule.span E S with hD
  set K : Submodule E (Fin n → E) := D.dualCoannihilator with hK
  have hKset : ∀ y, y ∈ K ↔ ∀ φ ∈ S, φ y = 0 := by
    intro y
    rw [hK, Submodule.mem_dualCoannihilator]
    constructor
    · intro h φ hφ
      exact h φ (Submodule.subset_span hφ)
    · intro h φ hφ
      induction hφ using Submodule.span_induction with
      | mem x hx => exact h x hx
      | zero => simp
      | add x z _ _ hx hz => simp [hx, hz]
      | smul c x _ hx => simp [hx]

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective K.subtype K.ker_subtype
  set P : (Fin n → E) →ₗ[E] (Fin n → E) := K.subtype ∘ₗ g with hP
  have hPK : ∀ y, P y ∈ K := fun y => (g y).2
  have hPid : ∀ k ∈ K, P k = k := by
    intro k hk
    have h1 := LinearMap.congr_fun hg ⟨k, hk⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at h1
    simp [hP, h1]

  have hrow : ∀ i, (LinearMap.proj i - LinearMap.proj i ∘ₗ P : Module.Dual E (Fin n → E)) ∈ D := by
    intro i
    have hmem : (LinearMap.proj i - LinearMap.proj i ∘ₗ P : Module.Dual E (Fin n → E)) ∈
        K.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro k hk
      simp [hPid k hk]
    rwa [hK, Subspace.dualCoannihilator_dualAnnihilator_eq] at hmem
  have hcoord : ∀ i, u i = ∑ j, ι (P (Pi.single j 1) i) * u j := by
    intro i
    have h0 := dual_span_sum_eq_zero ι S u hu _ (hrow i)
    simp only [LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.comp_apply, map_sub, sub_mul,
      Finset.sum_sub_distrib, sub_eq_zero] at h0
    rw [← h0]
    simp [Pi.single_apply]
  have hu' : u = ∑ j, u j • (fun i => ι (P (Pi.single j 1) i)) := by
    funext i
    rw [hcoord i]
    simp [Finset.sum_apply, mul_comm]
  rw [hu']
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨P (Pi.single j 1), ?_, rfl⟩)
  exact (hKset _).1 (hPK _)

def formRight {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (w : Fin n → E) : Module.Dual E (Fin n → E) where
  toFun y := Formalism.UG.hform σ J w y
  map_add' y z := by simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem formRight_apply {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (w y : Fin n → E) : formRight σ J w y = Formalism.UG.hform σ J w y := rfl

private theorem hform_add_right_flag_measures {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (x y z : Fin n → A) :
    Formalism.UG.hform s J x (y + z) = Formalism.UG.hform s J x y + Formalism.UG.hform s J x z := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem hform_smul_right_flag_measures {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (c : A) (x y : Fin n → A) :
    Formalism.UG.hform s J x (c • y) = c * Formalism.UG.hform s J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem hform_add_left_flag_measures' {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (x x' y : Fin n → A) :
    Formalism.UG.hform s J (x + x') y = Formalism.UG.hform s J x y + Formalism.UG.hform s J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private theorem hform_smul_left_flag_measures {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (c : A) (x y : Fin n → A) :
    Formalism.UG.hform s J (c • x) y = s c * Formalism.UG.hform s J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem perpSet_baseChange : ∀ (E A : Type) [Field E] [CommRing A] (σ : E →+* E) (s : A →+* A) (ι : E →+* A) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (W : Submodule E (Fin n → E)), (∀ e, s (ι e) = ι (σ e)) → perpSet s (J.map ι) (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set (Fin n → E)))) = (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' perpSet σ J W) : Set (Fin n → A)) := by
  intro E A _ _ σ s ι n J W hs
  classical

  have key : ∀ w z : Fin n → E, Formalism.UG.hform s (J.map ι) (fun i => ι (w i)) (fun i => ι (z i)) =
      ι (Formalism.UG.hform σ J w z) := by
    intro w z
    simp only [Formalism.UG.hform, Matrix.map_apply, hs, map_sum, map_mul]

  have pair : ∀ (w : Fin n → E) (y : Fin n → A), Formalism.UG.hform s (J.map ι) (fun i => ι (w i)) y =
      ∑ j, ι (formRight σ J w (Pi.single j 1)) * y j := by
    intro w y
    simp only [formRight_apply, Formalism.UG.hform, Matrix.map_apply, hs, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm]
  have hset : {z : Fin n → E | ∀ φ ∈ formRight σ J '' (W : Set (Fin n → E)), φ z = 0} = perpSet σ J W := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, perpSet, formRight_apply, SetLike.mem_coe]
  ext y
  constructor
  · intro hy
    rw [SetLike.mem_coe, ← hset]
    apply mem_span_of_forms ι _ y
    rintro φ ⟨w, hw, rfl⟩
    rw [← pair]
    exact hy _ (Submodule.subset_span ⟨w, hw, rfl⟩)
  · intro hy
    rw [SetLike.mem_coe] at hy
    have hgen : ∀ w ∈ W, Formalism.UG.hform s (J.map ι) (fun i => ι (w i)) y = 0 := by
      intro w hw
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        rw [key, hz w hw, map_zero]
      | zero => simp [Formalism.UG.hform]
      | add x x' _ _ hx hx' => rw [hform_add_right_flag_measures, hx, hx', add_zero]
      | smul c x _ hx => rw [hform_smul_right_flag_measures, hx, mul_zero]
    simp only [perpSet, Set.mem_setOf_eq]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact hgen w hw
    | zero => simp [Formalism.UG.hform]
    | add x x' _ _ hx hx' => rw [hform_add_left_flag_measures', hx, hx', add_zero]
    | smul c x _ hx => rw [hform_smul_left_flag_measures, hx, mul_zero]

end GlobalTheory.PerpBaseChange
