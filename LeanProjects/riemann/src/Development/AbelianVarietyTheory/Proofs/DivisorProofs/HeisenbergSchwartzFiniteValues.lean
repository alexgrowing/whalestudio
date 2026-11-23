import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantUnderIntegralLattice

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.HeisFinFin

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem finS_eventually_eq (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) {g : (κ → Af F) → ℂ}
    (hg : g ∈ SB (κ → Af F)) (w₀ : (κ → Af F) × (κ → Af F) × Af F) :
    ∀ᶠ w in 𝓝 w₀, GlobalTheory.HeisSchA.finS ψ g w.1 w.2.1 w.2.2 = GlobalTheory.HeisSchA.finS ψ g w₀.1 w₀.2.1 w₀.2.2 := by
  obtain ⟨V, hV, hVg⟩ := GlobalTheory.SBTransl.exists_nhds_zero_invariant g hg.1 hg.2
  let H : ((κ → Af F) × (κ → Af F) × Af F) × (κ → Af F) → ℂ :=
    fun p => GlobalTheory.HeisSchA.finChar ψ (p.2 ⬝ᵥ p.1.1 + p.1.2.2)
  have hHc : Continuous fun p : ((κ → Af F) × (κ → Af F) × Af F) × (κ → Af F) => p.2 ⬝ᵥ p.1.1 + p.1.2.2 :=
    (continuous_snd.dotProduct (continuous_fst.comp continuous_fst)).add
      (continuous_snd.comp (continuous_snd.comp continuous_fst))
  have hH : IsLocallyConstant H := (GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ).comp_continuous hHc
  let Z : Set (κ → Af F) := (fun x => x - w₀.2.1) '' tsupport g
  have hZ : IsCompact Z := hg.2.isCompact.image (continuous_id.sub continuous_const)
  have hP : ∀ y ∈ Z, ∀ᶠ p : ((κ → Af F) × (κ → Af F) × Af F) × (κ → Af F) in 𝓝 (w₀, y),
      H (p.1, p.2) = H (w₀, p.2) := by
    intro y _
    have h1 : {p | H p = H (w₀, y)} ∈ 𝓝 (w₀, y) := (hH.isOpen_fiber _).mem_nhds rfl
    have hc : Continuous fun p : ((κ → Af F) × (κ → Af F) × Af F) × (κ → Af F) => (w₀, p.2) :=
      continuous_const.prodMk continuous_snd
    have h2 : {p : ((κ → Af F) × (κ → Af F) × Af F) × (κ → Af F) | H (w₀, p.2) = H (w₀, y)} ∈ 𝓝 (w₀, y) :=
      hc.continuousAt.preimage_mem_nhds ((hH.isOpen_fiber _).mem_nhds rfl)
    filter_upwards [h1, h2] with p hp1 hp2
    exact hp1.trans hp2.symm
  have hE := hZ.eventually_forall_of_forall_eventually (P := fun w z => H (w, z) = H (w₀, z)) hP
  have hS : ∀ᶠ w : (κ → Af F) × (κ → Af F) × Af F in 𝓝 w₀, w.2.1 - w₀.2.1 ∈ V := by
    have hc : Continuous fun w : (κ → Af F) × (κ → Af F) × Af F => w.2.1 - w₀.2.1 :=
      (continuous_fst.comp continuous_snd).sub continuous_const
    have := hc.continuousAt (x := w₀)
    rw [ContinuousAt, sub_self] at this
    exact this hV
  filter_upwards [hE, hS] with w hw hs
  funext z
  simp only [GlobalTheory.HeisSchA.finS]
  have hg' : g (z + w.2.1) = g (z + w₀.2.1) := by
    have := hVg (z + w₀.2.1) _ hs
    rwa [show z + w₀.2.1 + (w.2.1 - w₀.2.1) = z + w.2.1 by abel] at this
  rw [hg']
  by_cases hz : z + w₀.2.1 ∈ tsupport g
  · have hzZ : z ∈ Z := ⟨z + w₀.2.1, hz, add_sub_cancel_right _ _⟩
    have := hw z hzZ
    simp only [H] at this
    rw [this]
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

theorem finS_image_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ),
    Continuous ψ →
    ∀ g ∈ SB (κ → Af F), ∀ Ω : Set ((κ → Af F) × (κ → Af F) × Af F), IsCompact Ω →
      ((fun w : (κ → Af F) × (κ → Af F) × Af F => GlobalTheory.HeisSchA.finS ψ g w.1 w.2.1 w.2.2) '' Ω).Finite := by
  intro F _ _ κ _ ψ hψ g hg Ω hΩ
  set Φ := fun w : (κ → Af F) × (κ → Af F) × Af F => GlobalTheory.HeisSchA.finS ψ g w.1 w.2.1 w.2.2
  obtain ⟨t, -, ht⟩ := hΩ.elim_nhds_subcover (fun x => {w | Φ w = Φ x})
    (fun x _ => finS_eventually_eq ψ hψ hg x)
  refine (t.finite_toSet.image Φ).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨x, hx, hwx⟩ := Set.mem_iUnion₂.1 (ht hw)
  exact ⟨x, hx, hwx.symm⟩

end GlobalTheory.HeisFinFin
