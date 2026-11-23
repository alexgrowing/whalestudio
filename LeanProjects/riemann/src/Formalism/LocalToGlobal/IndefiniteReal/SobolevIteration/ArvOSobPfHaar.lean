import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfK
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfBdd

noncomputable section

open Formalism.IndefR.Datum Matrix MeasureTheory Topology

namespace Formalism.IndefR.Tow.SobPf

variable {n : ℕ}

theorem mul_mem_KAt {G s a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KAt G s) (hb : b ∈ KAt G s) :
    a * b ∈ KAt G s := by
  have ha' : a ∈ Formalism.QuantumDeterminants.UH G ∧ a * s = s * a := ha
  have hb' : b ∈ Formalism.QuantumDeterminants.UH G ∧ b * s = s * b := hb
  have h1 : aᴴ * G * a = G := ha'.1
  have h2 : bᴴ * G * b = G := hb'.1
  show a * b ∈ Formalism.QuantumDeterminants.UH G ∧ a * b * s = s * (a * b)
  refine ⟨?_, ?_⟩
  · show (a * b)ᴴ * G * (a * b) = G
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * G * (a * b) = bᴴ * (aᴴ * G * a) * b := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, h2]
  · calc a * b * s = a * (b * s) := Matrix.mul_assoc _ _ _
      _ = a * (s * b) := by rw [hb'.2]
      _ = (a * s) * b := (Matrix.mul_assoc _ _ _).symm
      _ = (s * a) * b := by rw [ha'.2]
      _ = s * (a * b) := Matrix.mul_assoc _ _ _

theorem inv_mem_KAt {G s a : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (ha : a ∈ KAt G s) :
    a⁻¹ ∈ KAt G s := by

  have ha' : a ∈ Formalism.QuantumDeterminants.UH G ∧ a * s = s * a := ha
  have h1 : aᴴ * G * a = G := ha'.1
  have hleft : (G⁻¹ * aᴴ * G) * a = 1 := by
    calc (G⁻¹ * aᴴ * G) * a = G⁻¹ * (aᴴ * G * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hG]
  have hdet : IsUnit a.det := Matrix.isUnit_det_of_left_inverse hleft
  have hright : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hdet
  have hleft' : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hdet
  show a⁻¹ ∈ Formalism.QuantumDeterminants.UH G ∧ a⁻¹ * s = s * a⁻¹
  refine ⟨?_, ?_⟩
  · show (a⁻¹)ᴴ * G * a⁻¹ = G
    calc (a⁻¹)ᴴ * G * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * G * a) * a⁻¹ := by rw [h1]
      _ = (a * a⁻¹)ᴴ * G * (a * a⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hright]; simp
  · calc a⁻¹ * s = a⁻¹ * s * (a * a⁻¹) := by rw [hright, Matrix.mul_one]
      _ = a⁻¹ * (s * a) * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = a⁻¹ * (a * s) * a⁻¹ := by rw [ha'.2]
      _ = (a⁻¹ * a) * s * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = s * a⁻¹ := by rw [hleft', Matrix.one_mul]

theorem inv_eq_of_UH {G k : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hk : k ∈ Formalism.QuantumDeterminants.UH G) :
    k⁻¹ = G⁻¹ * kᴴ * G := by

  have h1 : kᴴ * G * k = G := hk
  have hleft : (G⁻¹ * kᴴ * G) * k = 1 := by
    calc (G⁻¹ * kᴴ * G) * k = G⁻¹ * (kᴴ * G * k) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hG]
  exact Matrix.inv_eq_left_inv hleft

def Kg {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s}
  mul_mem' {a b} ha hb := by
    show ((a * b : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
    rw [Units.val_mul]; exact mul_mem_KAt ha hb
  one_mem' := by
    show ((1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
    rw [Units.val_one]; exact one_mem_KAt G s
  inv_mem' {a} ha := by
    show ((a⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
    rw [Matrix.coe_units_inv]; exact inv_mem_KAt (det_G_unit hs) ha

theorem isCompact_Kg {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) :
    IsCompact ((Kg hs : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ) : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) := by

  have hGu : IsUnit G.det := det_G_unit hs
  haveI : CompactSpace (KAt G s) := isCompact_iff_compactSpace.mp (isCompact_KAt hs)
  have hl : ∀ k ∈ KAt G s, (G⁻¹ * kᴴ * G) * k = 1 := fun k hk => by
    have h1 : kᴴ * G * k = G := (show k ∈ Formalism.QuantumDeterminants.UH G ∧ k * s = s * k from hk).1
    calc (G⁻¹ * kᴴ * G) * k = G⁻¹ * (kᴴ * G * k) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hGu]
  have hr : ∀ k ∈ KAt G s, k * (G⁻¹ * kᴴ * G) = 1 := fun k hk => by
    rw [← Matrix.inv_eq_left_inv (hl k hk)]
    exact Matrix.mul_nonsing_inv k (Matrix.isUnit_det_of_left_inverse (hl k hk))
  let F : KAt G s → (Matrix (Fin n) (Fin n) ℂ)ˣ := fun k =>
    ⟨k.1, G⁻¹ * k.1ᴴ * G, hr k.1 k.2, hl k.1 k.2⟩
  have hF : Continuous F := by
    rw [Units.continuous_iff]
    refine ⟨continuous_subtype_val, ?_⟩
    exact (continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul
      continuous_const
  have he : ((Kg hs : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ) : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) =
      Set.range F := by
    ext u
    constructor
    · intro hu
      exact ⟨⟨u.1, hu⟩, Units.ext rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2
  rw [he]
  exact isCompact_range hF

private theorem exists_Kg_coe_eq_of_mem_KAt {G s k : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) (hk : k ∈ KAt G s) :
    ∃ u : Kg hs, ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k := by
  have hGu : IsUnit G.det := det_G_unit hs
  have h1 : kᴴ * G * k = G := (show k ∈ Formalism.QuantumDeterminants.UH G ∧ k * s = s * k from hk).1
  have hleft : (G⁻¹ * kᴴ * G) * k = 1 := by
    calc (G⁻¹ * kᴴ * G) * k = G⁻¹ * (kᴴ * G * k) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hGu]
  have hdet : IsUnit k.det := Matrix.isUnit_det_of_left_inverse hleft
  exact ⟨⟨⟨k, k⁻¹, Matrix.mul_nonsing_inv k hdet, Matrix.nonsing_inv_mul k hdet⟩, hk⟩, rfl⟩

theorem haarExists_holds : HaarExists := by
  intro n G s hs
  haveI : CompactSpace (Kg hs) := isCompact_iff_compactSpace.mp (isCompact_Kg hs)
  letI : MeasurableSpace (Kg hs) := borel (Kg hs)
  haveI : BorelSpace (Kg hs) := ⟨rfl⟩
  let ν : Measure (Kg hs) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    have h := Measure.haarMeasure_self (G := Kg hs) (K₀ := ⊤)
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h
  let φ : Kg hs → (Fin n → Fin n → ℂ) := fun u =>
    Matrix.of.symm ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  have hφ : Continuous φ := by
    show Continuous (fun u : Kg hs => ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
    exact Units.continuous_val.comp continuous_subtype_val
  have hφm : Measurable φ := hφ.measurable
  have hcl : IsClosed {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := isClosed_KAt G s
  refine ⟨ν.map φ, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    rw [Measure.map_apply hφm MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ
  · rw [ae_map_iff hφm.aemeasurable hcl.measurableSet]
    exact ae_of_all _ fun u => by
      show ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
      exact u.2
  · intro k₀ hk₀
    obtain ⟨u₀, hu₀⟩ := exists_Kg_coe_eq_of_mem_KAt hs hk₀
    have hT : Continuous (fun k : Fin n → Fin n → ℂ => Matrix.of.symm (k₀ * Matrix.of k)) := by
      show Continuous (fun k : Matrix (Fin n) (Fin n) ℂ => k₀ * k)
      exact continuous_const.matrix_mul continuous_id
    have hL : Measurable (fun u : Kg hs => u₀ * u) := (continuous_const.mul continuous_id).measurable
    have hcomp : (fun k : Fin n → Fin n → ℂ => Matrix.of.symm (k₀ * Matrix.of k)) ∘ φ =
        φ ∘ (fun u : Kg hs => u₀ * u) := by
      funext u
      show Matrix.of.symm (k₀ * ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
        Matrix.of.symm (((u₀ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
          ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
      rw [hu₀]
    rw [Measure.map_map hT.measurable hφm, hcomp, ← Measure.map_map hφm hL,
      map_mul_left_eq_self]
  · rintro U hU ⟨k, hkU, hkK⟩
    obtain ⟨u, hu⟩ := exists_Kg_coe_eq_of_mem_KAt hs hkK
    rw [Measure.map_apply hφm hU.measurableSet]
    refine (hU.preimage hφ).measure_pos ν ⟨u, ?_⟩
    show Matrix.of.symm ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ U
    rw [hu]
    exact hkU

end Formalism.IndefR.Tow.SobPf

end
