import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SobClass

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

variable (F) in

def archInc (y : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i))

theorem evI_archInc (y : κ → mixedEmbedding.mixedSpace F) (i : κ) : evI F (archInc F y i) = y i := by
  simp [evI, archInc]

theorem archInc_snd (y : κ → mixedEmbedding.mixedSpace F) (i : κ) : (archInc F y i).2 = 0 := by
  simp [archInc]

theorem archInc_add (y y' : κ → mixedEmbedding.mixedSpace F) : archInc F (y + y') = archInc F y + archInc F y' := by
  funext i
  simp only [archInc, Pi.add_apply]
  rw [map_add, map_add]
  rfl

end GlobalTheory.SobClass
end

noncomputable section
namespace GlobalTheory.SobClass

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

variable (F) in

def PerM (m : ℕ) (Φ : (κ → AF F) → ℂ) : Prop :=
  ∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) →
    Φ (x + (m : AF F) • a') = Φ x

theorem dH_perM (ψ : AddChar (AF F) ℂ) {w : (κ → AF F) × (κ → AF F)} (hw : IsArch w) {m : ℕ}
    {Φ : (κ → AF F) → ℂ} (h : PerM F m Φ) : PerM F m (dH ψ w Φ) := by
  intro x a' ha
  unfold dH
  congr 1
  funext t
  simp only [schr]
  have h0 : ((m : AF F) • a') ⬝ᵥ (realAd F t • w).2 = 0 := by
    simp only [dotProduct, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := (hw i).2 (a' i) (ha i).1
    simp only [smul_eq_mul] at this
    calc _ = (m : AF F) * realAd F t * (a' i * w.2 i) := by ring
      _ = 0 := by rw [this, mul_zero]
  rw [add_dotProduct, h0, add_zero, add_right_comm, h _ _ ha]

theorem wordH_perM (ψ : AddChar (AF F) ℂ) {m : ℕ} {Φ : (κ → AF F) → ℂ} (h : PerM F m Φ) :
    ∀ l : List ((κ → AF F) × (κ → AF F)), (∀ w ∈ l, IsArch w) → PerM F m (wordH ψ l Φ) := by
  intro l
  induction l with
  | nil => intro _; exact h
  | cons w l ih =>
    intro hl
    rw [wordH_cons]
    exact dH_perM ψ (hl w (by simp)) (ih fun v hv => hl v (by simp [hv]))

theorem continuous_slice {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (x : κ → AF F) :
    Continuous fun y => Φ (x + archInc F y) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hmem =>
    obtain ⟨f, g, -, rfl⟩ := hmem
    have e1 : ∀ y : κ → mixedEmbedding.mixedSpace F, (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + archInc F y) i).1) =
        (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + y := by
      intro y; funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (archInc F y i).1) = _
      simp [archInc, map_add]
    have e2 : ∀ y : κ → mixedEmbedding.mixedSpace F, (fun i => ((x + archInc F y) i).2) = fun i => (x i).2 := by
      intro y; funext i
      show (x i).2 + (archInc F y i).2 = _
      rw [archInc_snd, add_zero]
    show Continuous fun y => pureA F f g (x + archInc F y)
    unfold pureA
    simp_rw [e1, e2]
    exact (f.continuous.comp (continuous_const.add continuous_id)).mul continuous_const
  | zero => exact continuous_const
  | add _ _ _ _ h1 h2 => exact h1.add h2
  | smul c _ _ h => exact continuous_const.mul h

theorem at_archInc (e : κ → mixedEmbedding.mixedSpace F) (i : κ) : At (evI F) (archInc F e i) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  show u * archInc F e i = 0
  refine Prod.ext ?_ ?_
  · show u.1 * (archInc F e i).1 = 0
    rw [h1, zero_mul]
  · show u.2 * (archInc F e i).2 = 0
    rw [archInc_snd, mul_zero]

theorem evI_zero : evI F (0 : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem at_zero : At (evI F) (0 : AF F) := fun u _ => smul_zero u

theorem isArchUnit_der (e : κ → mixedEmbedding.mixedSpace F) (he : ∀ i, ‖e i‖ ≤ 1) :
    IsArchUnit ((archInc F e, 0) : (κ → AF F) × (κ → AF F)) :=
  ⟨fun i => ⟨at_archInc e i, at_zero⟩, fun i => ⟨by rw [evI_archInc]; exact he i, by simp only [Pi.zero_apply, evI_zero, norm_zero, zero_le_one]⟩⟩

theorem isArchUnit_mul (e : κ → mixedEmbedding.mixedSpace F) (he : ∀ i, ‖e i‖ ≤ 1) :
    IsArchUnit ((0, archInc F e) : (κ → AF F) × (κ → AF F)) :=
  ⟨fun i => ⟨at_zero, at_archInc e i⟩, fun i => ⟨by simp only [Pi.zero_apply, evI_zero, norm_zero, zero_le_one], by rw [evI_archInc]; exact he i⟩⟩

theorem wordH_append (ψ : AddChar (AF F) ℂ) (l l' : List ((κ → AF F) × (κ → AF F))) (Φ : (κ → AF F) → ℂ) :
    wordH ψ (l ++ l') Φ = wordH ψ l (wordH ψ l' Φ) := by
  simp [wordH, List.foldr_append]

end GlobalTheory.SobClass
end
