import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.MemHFinInIff

noncomputable section

namespace PI.FT

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct

section Mat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
  {R : Type} [CommRing R] [Algebra F R]

abbrev mt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : HA R σ J) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))

abbrev mtI {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : HA R σ J) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (((HA.mat R σ J g)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))

end Mat

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

instance instIsModTopTens : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

instance instContAddTens : ContinuousAdd (R ⊗[F] E) :=
  IsModuleTopology.toContinuousAdd R (R ⊗[F] E)

theorem cont_mul_const (c d : R ⊗[F] E) : Continuous (fun a : R ⊗[F] E => c * a * d) := by
  refine (IsModuleTopology.continuous_of_linearMap (R := R)
    ((LinearMap.mulRight R d).comp (LinearMap.mulLeft R c))).congr fun a => ?_
  simp

theorem cont_sandwich {T : Type*} [TopologicalSpace T] {m n p q : Type*} [Fintype n] [Fintype p]
    (C : Matrix m n (R ⊗[F] E)) (D : Matrix p q (R ⊗[F] E)) {f : T → Matrix n p (R ⊗[F] E)}
    (hf : Continuous f) : Continuous (fun t => C * f t * D) := by
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.mul_apply, Finset.sum_mul]
  refine continuous_finset_sum _ fun l _ => continuous_finset_sum _ fun k _ => ?_
  exact (cont_mul_const R (C i k) (D l j)).comp (hf.matrix_elem k l)

theorem cont_HA_iff {T : Type*} [TopologicalSpace T] {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (f : T → HA R σ J) :
    Continuous f ↔ Continuous (fun t => mt (f t)) ∧ Continuous (fun t => mtI (f t)) := by
  constructor
  · intro hf
    have h1 : Continuous (fun t => ((toHR (f t) : HR R σ J) : GL (Fin n) (R ⊗[F] E))) :=
      continuous_subtype_val.comp hf
    exact ⟨Units.continuous_val.comp h1, Units.continuous_coe_inv.comp h1⟩
  · rintro ⟨h1, h2⟩
    have h3 : Continuous (fun t => ((toHR (f t) : HR R σ J) : GL (Fin n) (R ⊗[F] E))) :=
      Units.continuous_iff.2 ⟨h1, h2⟩
    exact h3.subtype_mk (fun t => (toHR (f t)).2)

theorem cont_transl {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : HA R σ J) :
    Continuous (fun g : HA R σ J => h * g) := by
  have hid := (cont_HA_iff R (fun g : HA R σ J => g)).1 continuous_id
  refine (cont_HA_iff R (fun g : HA R σ J => h * g)).2 ⟨?_, ?_⟩
  · have h1 := cont_sandwich R (mt h) (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) hid.1
    simp only [Matrix.mul_one] at h1
    exact h1
  · have h1 := cont_sandwich R (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (mtI h) hid.2
    simp only [Matrix.one_mul] at h1
    exact h1

end Cont

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

local notation "ι" => inclR (F := F) (E := E) (AF F)

theorem frame_formulas {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
    {J' : Matrix (Fin M) (Fin M) E} {x : Fin 1 → Fin (M + 1) → E} {β : F}
    {B : Matrix (Fin (M + 1)) (Fin M) E} (hH : FrameHyp F E σ M J J' x β B)
    (e : Hstab (AF F) σ J x ≃* HA (AF F) σ J')
    (he : ∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) :
    (∀ g : Hstab (AF F) σ J x,
      mt (e g) = (Lm σ J J' B).map ι * mt (g : HA (AF F) σ J) * B.map ι) ∧
    (∀ g : Hstab (AF F) σ J x,
      mt (g : HA (AF F) σ J) = (Xc x).map ι * (qm σ J x (algebraMap F E β)).map ι +
        B.map ι * mt (e g) * (Rm σ J J' B x (algebraMap F E β)).map ι) := by
  obtain ⟨-, hβ, hx, hxB, hJ', -, hd⟩ := hH
  have hb : algebraMap F E β ≠ 0 := fun h =>
    hβ ((algebraMap F E).injective (h.trans (map_zero _).symm))
  have hLB := Lm_mul σ hJ' hd
  have hdec := Xc_q_add_B_R σ hb hx hxB hLB
  exact ⟨fun g => formulaA σ (AF F) hLB _ _ (he g),
    fun g => formulaB σ (AF F) hdec _ _ (stab_mul_Xc σ (AF F) g) (he g)⟩

theorem mtI_eq {M' : ℕ} {J' : Matrix (Fin M') (Fin M') E}
    {K : Type} [Group K] (e : K ≃* HA (AF F) σ J') (g : K) :
    mtI (e g) = mt (e g⁻¹) := by
  rw [map_inv e g]
  rfl

theorem stepTransl : StepTransl F E σ := by
  intro M J h
  exact cont_transl (AF F) h

theorem stepHomeo : StepHomeo F E σ := by
  intro M J J' x β B hH e he
  obtain ⟨fA, fB⟩ := frame_formulas hH e he
  have hid := (cont_HA_iff (AF F) (fun g : HA (AF F) σ J => g)).1 continuous_id
  have hid' := (cont_HA_iff (AF F) (fun g : HA (AF F) σ J' => g)).1 continuous_id
  have hs1 : Continuous (fun g : Hstab (AF F) σ J x => mt (g : HA (AF F) σ J)) :=
    hid.1.comp continuous_subtype_val
  have hs2 : Continuous (fun g : Hstab (AF F) σ J x => mtI (g : HA (AF F) σ J)) :=
    hid.2.comp continuous_subtype_val
  constructor
  · refine (cont_HA_iff (AF F) e).2 ⟨?_, ?_⟩
    · exact (cont_sandwich (AF F) ((Lm σ J J' B).map ι) (B.map ι) hs1).congr fun g => (fA g).symm
    · refine (cont_sandwich (AF F) ((Lm σ J J' B).map ι) (B.map ι) hs2).congr fun g => ?_
      rw [mtI_eq e g, fA g⁻¹]
      rfl
  · have hc : Continuous (fun g' : HA (AF F) σ J' => (e.symm g' : HA (AF F) σ J)) := by
      refine (cont_HA_iff (AF F) _).2 ⟨?_, ?_⟩
      · refine (Continuous.add (continuous_const : Continuous fun _ : HA (AF F) σ J' =>
          (Xc x).map ι * (qm σ J x (algebraMap F E β)).map ι)
          (cont_sandwich (AF F) (B.map ι) ((Rm σ J J' B x (algebraMap F E β)).map ι) hid'.1)).congr
          fun g' => ?_
        rw [fB (e.symm g'), MulEquiv.apply_symm_apply]
        rfl
      · refine (Continuous.add (continuous_const : Continuous fun _ : HA (AF F) σ J' =>
          (Xc x).map ι * (qm σ J x (algebraMap F E β)).map ι)
          (cont_sandwich (AF F) (B.map ι) ((Rm σ J J' B x (algebraMap F E β)).map ι) hid'.2)).congr
          fun g' => ?_
        show _ = mt (((e.symm g')⁻¹ : Hstab (AF F) σ J x) : HA (AF F) σ J)
        rw [fB ((e.symm g')⁻¹), map_inv, MulEquiv.apply_symm_apply]
        rfl
    exact hc.subtype_mk (fun g' => (e.symm g').2)

instance instNontrivialAF : Nontrivial (AF F) :=
  inferInstanceAs (Nontrivial (NumberField.InfiniteAdeleRing F ×
    IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))

theorem inclR_injective : Function.Injective ι := by
  unfold inclR
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective

theorem stepRat : StepRat F E σ := by
  intro M J J' x β B hH e he g
  obtain ⟨fA, fB⟩ := frame_formulas hH e he
  constructor
  · intro hg
    have h1 : toHR (g : HA (AF F) σ J) ∈ HFinIn (AF F) σ J :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).1
    obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := (mem_HFinIn_iff σ (AF F) inclR_injective _).1 h1
    refine (mem_HFinIn_iff σ (AF F) inclR_injective _).2
      ⟨⟨Lm σ J J' B * a * B, ?_⟩, ⟨Lm σ J J' B * c * B, ?_⟩⟩
    · show mt (e g) = _
      rw [fA g, show mt (g : HA (AF F) σ J) = a.map ι from ha, Matrix.map_mul, Matrix.map_mul]
    · show mtI (e g) = _
      rw [mtI_eq e g, fA g⁻¹]
      show (Lm σ J J' B).map ι * mtI (g : HA (AF F) σ J) * B.map ι = _
      rw [show mtI (g : HA (AF F) σ J) = c.map ι from hc, Matrix.map_mul, Matrix.map_mul]
  · intro hg
    obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := (mem_HFinIn_iff σ (AF F) inclR_injective _).1 hg
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, g.2⟩)
    refine (mem_HFinIn_iff σ (AF F) inclR_injective _).2
      ⟨⟨Xc x * qm σ J x (algebraMap F E β) + B * a * Rm σ J J' B x (algebraMap F E β), ?_⟩,
        ⟨Xc x * qm σ J x (algebraMap F E β) + B * c * Rm σ J J' B x (algebraMap F E β), ?_⟩⟩
    · show mt (g : HA (AF F) σ J) = _
      rw [fB g, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
      rw [show mt (e g) = a.map ι from ha]
    · show mt ((g⁻¹ : Hstab (AF F) σ J x) : HA (AF F) σ J) = _
      rw [fB g⁻¹, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
        ← mtI_eq e g]
      rw [show mtI (e g) = c.map ι from hc]

end Frame

end PI.FT
