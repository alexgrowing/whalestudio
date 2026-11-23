import Mathlib
import Formalism.PeriodIntegrals.LevelKSplit

noncomputable section

namespace PI.LevelKSplit.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def SplitK : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    ∀ ΛX ΛW ΛY : Set (Fin M → E), Adapted F E σ M J P ΛX ΛW ΛY →
    ∀ m h : HA (Af F) σ J, m ∈ Nsub (Af F) σ J P → h ∈ Hsub (Af F) σ J P →
      m * h ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY) → h ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)

end Ext

section ExtN

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def ExistS : Prop :=
  ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    ∀ μN : Measure (Nsub (Af F) σ J P), μN.IsHaarMeasure →
    ∀ μH : Measure (Hsub (Af F) σ J P), μH.IsHaarMeasure →
    ∃ μS : Measure (Ssub (Af F) σ J P), μS.IsHaarMeasure ∧
      IsProdNH F E σ M J (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P) μS μN μH

def MeasKf : Prop :=
  ∀ Λ : Set (Fin M → E), MeasurableSet (Kf σ J Λ : Set (HA (Af F) σ J))

variable {F E σ M J}

theorem levelS_of (hinv : ∀ x, σ (σ x) = x) (hEx : ExistS F E σ M J) (hMe : MeasKf F E σ M J) (hSp : SplitK F E σ M J) :
    LevelS F E σ M J := by
  intro hJ r P T hP ΛX ΛW ΛY hA μN hμN μH hμH
  refine ⟨hEx r P T hP μN hμN μH hμH, ?_⟩
  rintro μS ⟨-, hprod⟩
  have hKm : MeasurableSet (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) := hMe _
  have key := hprod ((Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)).indicator 1)
    (measurable_one.indicator hKm)
  have hS : {s : Ssub (Af F) σ J P | (s : HA (Af F) σ J) ∈ KS σ J P (ΛX ∪ ΛW ∪ ΛY)} =
      Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) := by
    ext s
    show (s : HA (Af F) σ J) ∈ Ssub (Af F) σ J P ⊓ Kf σ J (ΛX ∪ ΛW ∪ ΛY) ↔
      (s : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
    rw [Subgroup.mem_inf]
    exact ⟨And.right, fun h => ⟨s.2, h⟩⟩
  have hN : {m : Nsub (Af F) σ J P | (m : HA (Af F) σ J) ∈ NO σ J P (ΛX ∪ ΛW ∪ ΛY)} =
      Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) := by
    ext s
    show (s : HA (Af F) σ J) ∈ Nsub (Af F) σ J P ⊓ Kf σ J (ΛX ∪ ΛW ∪ ΛY) ↔
      (s : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
    rw [Subgroup.mem_inf]
    exact ⟨And.right, fun h => ⟨s.2, h⟩⟩
  have hH : {m : Hsub (Af F) σ J P | (m : HA (Af F) σ J) ∈ KH σ J P (ΛX ∪ ΛW ∪ ΛY)} =
      Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) := by
    ext s
    show (s : HA (Af F) σ J) ∈ Hsub (Af F) σ J P ⊓ Kf σ J (ΛX ∪ ΛW ∪ ΛY) ↔
      (s : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
    rw [Subgroup.mem_inf]
    exact ⟨And.right, fun h => ⟨s.2, h⟩⟩
  rw [hS, hN, hH]
  have hL : ∫⁻ k, (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)).indicator 1
      (k : HA (Af F) σ J) ∂μS = μS (Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J))) := by
    rw [← lintegral_indicator_one (measurable_subtype_coe hKm)]
    congr 1
  have inner : ∀ m : Nsub (Af F) σ J P,
      ∫⁻ h, (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)).indicator 1
        ((m : HA (Af F) σ J) * (h : HA (Af F) σ J)) ∂μH =
      (Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J))).indicator
        (fun _ => μH (Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)))) m := by
    intro m
    by_cases hm : (m : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
    · rw [Set.indicator_of_mem (show m ∈ Subtype.val ⁻¹'
          (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from hm),
        ← lintegral_indicator_one (measurable_subtype_coe hKm)]
      congr 1
      funext h
      by_cases hh : (h : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
      · simp only [Set.indicator_of_mem (show (m : HA (Af F) σ J) * (h : HA (Af F) σ J) ∈
            (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from (Kf σ J _).mul_mem hm hh),
          Set.indicator_of_mem (show h ∈ Subtype.val ⁻¹'
            (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from hh), Pi.one_apply]
      · rw [Set.indicator_of_notMem (show (m : HA (Af F) σ J) * (h : HA (Af F) σ J) ∉
            (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from
              fun hmh => hh (hSp hJ hinv r P T hP ΛX ΛW ΛY hA m h m.2 h.2 hmh)),
          Set.indicator_of_notMem (show h ∉ Subtype.val ⁻¹'
            (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from hh)]
    · rw [Set.indicator_of_notMem (show m ∉ Subtype.val ⁻¹'
          (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from hm)]
      have hz : ∀ h : Hsub (Af F) σ J P, (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)).indicator 1
          ((m : HA (Af F) σ J) * (h : HA (Af F) σ J)) = (0 : ENNReal) := by
        intro h
        refine Set.indicator_of_notMem (fun hmh => hm ?_) _
        have hh := hSp hJ hinv r P T hP ΛX ΛW ΛY hA m h m.2 h.2 hmh
        have h2 := (Kf σ J (ΛX ∪ ΛW ∪ ΛY)).mul_mem hmh ((Kf σ J (ΛX ∪ ΛW ∪ ΛY)).inv_mem hh)
        rwa [mul_inv_cancel_right] at h2
      simp only [hz, lintegral_zero]
  rw [hL, lintegral_congr inner, lintegral_indicator_const (measurable_subtype_coe hKm)] at key
  rw [key, mul_comm]

end ExtN

def ExistSAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ExistS F E σ M J

def MeasKfAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      MeasKf F E σ M J

def SplitKAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => SplitK F E σ M J

theorem sig_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]

theorem levelSAll_of (h1 : ExistSAll) (h2 : MeasKfAll) (h3 : SplitKAll) : LevelSAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  exact levelS_of (sig_invol hσ) (h1 F E σ hσ M J hJ) (h2 F E σ hσ M J hJ) (h3 F E σ hσ M J hJ)

end PI.LevelKSplit.W
