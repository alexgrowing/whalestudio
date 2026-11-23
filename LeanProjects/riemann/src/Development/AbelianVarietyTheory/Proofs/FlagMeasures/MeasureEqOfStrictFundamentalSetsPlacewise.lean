import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserCovolumeLe
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FundEq

open GlobalTheory.DegVol

theorem measurable_mulP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) :
    Measurable (fun x : ι → Formalism.QuantumDeterminants.Mt k r => mulP m x) :=
  measurable_pi_lambda _ fun v => (GlobalTheory.DegVol.Cov.continuous_lmulM _).measurable.comp (measurable_pi_apply v)

theorem measure_eq_tsum {ι : Type} {k r : ℕ} (μ : Measure (ι → Formalism.QuantumDeterminants.Mt k r))
    (R Γ Ω S : Set (ι → Formalism.QuantumDeterminants.Mt k r)) [Countable Γ] (hR : μ Rᶜ = 0)
    (hΩ : MeasurableSet Ω) (hS : MeasurableSet S) (h : ∀ x ∈ R, ∃! m, m ∈ Γ ∧ mulP m x ∈ Ω) :
    μ S = ∑' a : Γ, μ ((fun x => mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω ∩ S) := by
  rw [← measure_iUnion₀]
  · apply measure_congr
    have : ∀ᵐ x ∂μ, x ∈ R := hR
    filter_upwards [this] with x hx
    obtain ⟨s, hs, -⟩ := h x hx
    apply propext
    constructor
    · intro hxS
      exact Set.mem_iUnion.2 ⟨⟨s, hs.1⟩, hs.2, hxS⟩
    · intro hxS
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hxS
      exact ha.2
  · intro a b hab
    refine measure_mono_null ?_ hR
    rintro x ⟨ha, hb⟩ hx
    exact hab (Subtype.ext ((h x hx).unique ⟨a.2, ha.1⟩ ⟨b.2, hb.1⟩))
  · intro a
    exact ((measurable_mulP _ hΩ).inter hS).nullMeasurableSet

def invP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) : ι → Formalism.QuantumDeterminants.Mt k r :=
  fun v => Matrix.of.symm (Matrix.of (m v))⁻¹

theorem mulP_invP_mulP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) (hm : ∀ v, IsUnit (Matrix.of (m v)).det)
    (x : ι → Formalism.QuantumDeterminants.Mt k r) : mulP (invP m) (mulP m x) = x := by
  funext v
  show (Matrix.of (m v))⁻¹ * (Matrix.of (m v) * Matrix.of (x v)) = x v
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hm v), Matrix.one_mul]
  rfl

theorem pointwiseInv_pointwiseInv {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) (hm : ∀ v, IsUnit (Matrix.of (m v)).det) :
    invP (invP m) = m := by
  funext v
  show ((Matrix.of (m v))⁻¹)⁻¹ = m v
  rw [Matrix.nonsing_inv_nonsing_inv _ (hm v)]
  rfl

theorem measure_le {ι : Type} [Fintype ι] {k r : ℕ} (μ : Measure (ι → Formalism.QuantumDeterminants.Mt k r))
    (R Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)) (hΓ : Γ.Countable) (hR : μ Rᶜ = 0)
    (hinv : ∀ m ∈ Γ, invP m ∈ Γ) (hu : ∀ m ∈ Γ, ∀ v, IsUnit (Matrix.of (m v)).det)
    (hpres : ∀ m ∈ Γ, μ.map (fun x => mulP m x) = μ)
    (h₁ : IsFund Γ R Ω₁) (h₂ : IsFund Γ R Ω₂) : μ Ω₁ ≤ μ Ω₂ := by
  haveI : Countable Γ := hΓ.to_subtype
  have e1 := measure_eq_tsum μ R Γ Ω₂ Ω₁ hR h₂.1 h₁.1 h₂.2
  have e2 := measure_eq_tsum μ R Γ Ω₁ Ω₂ hR h₁.1 h₂.1 h₁.2
  have hterm : ∀ a : Γ, μ ((fun x => mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω₂ ∩ Ω₁) =
      μ ((fun x => mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) x) ⁻¹' Ω₁ ∩ Ω₂) := by
    intro a
    have hs : MeasurableSet ((fun x => mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) x) ⁻¹' Ω₁ ∩ Ω₂) :=
      (measurable_mulP _ h₁.1).inter h₂.1
    conv_rhs => rw [← hpres a a.2, Measure.map_apply (measurable_mulP _) hs]
    congr 1
    ext x
    show (mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x ∈ Ω₂ ∧ x ∈ Ω₁) ↔
      (mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) (mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ∈ Ω₁ ∧ mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x ∈ Ω₂)
    rw [mulP_invP_mulP _ (hu a a.2)]
    exact And.comm
  let f : Γ → Γ := fun a => ⟨invP a, hinv a a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h' : invP (a : ι → Formalism.QuantumDeterminants.Mt k r) = invP b := congrArg Subtype.val hab
    apply Subtype.ext
    rw [← pointwiseInv_pointwiseInv _ (hu a a.2), ← pointwiseInv_pointwiseInv _ (hu b b.2), h']
  rw [e1, e2, tsum_congr hterm]
  exact ENNReal.tsum_comp_le_tsum_of_injective hf
    (fun b : Γ => μ ((fun x => mulP (b : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω₁ ∩ Ω₂))

theorem measure_eq : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)),
    Γ.Countable → (fun _ => Matrix.of.symm 1) ∈ Γ → (∀ m ∈ Γ, ∀ m' ∈ Γ, GlobalTheory.DegVol.mulP m m' ∈ Γ) →
    (∀ m ∈ Γ, (fun v => Matrix.of.symm (Matrix.of (m v))⁻¹) ∈ Γ) →
    (∀ m ∈ Γ, ∀ v, Matrix.of (m v) ∈ Formalism.QuantumDeterminants.Nset k r) →
    GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₁ → GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₂ →
    Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₁ = Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₂ := by
  intro ι _ k r Γ Ω₁ Ω₂ hΓ _ _ hinv hN h₁ h₂
  have hH := GlobalTheory.Amp.NHaar.isHaarOn_lebN k r
  haveI : SigmaFinite (GlobalTheory.Amp.lebN k r) := hH.1
  have hu : ∀ m ∈ Γ, ∀ v, IsUnit (Matrix.of (m v)).det := fun m hm v =>
    GlobalTheory.DegVol.RealMat.isUnit_det (hN m hm v).1
  have hnull : Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) (GlobalTheory.DegVol.RP k r (fun _ => 1))ᶜ = 0 := by
    refine measure_mono_null (t := ⋃ v : ι, Function.eval v ⁻¹' {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) ?_
      (measure_iUnion_null fun v => Measure.pi_eval_preimage_null _ hH.2.2.1)
    intro x hx
    simp only [RP, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨v, hv'⟩ := hx
    refine Set.mem_iUnion.2 ⟨v, ?_⟩
    intro hxN
    apply hv'
    refine ⟨hxN, ?_⟩
    simpa using hxN
  have hpres : ∀ m ∈ Γ, (Measure.pi fun _ : ι => GlobalTheory.Amp.lebN k r).map (fun x => mulP m x) =
      Measure.pi fun _ : ι => GlobalTheory.Amp.lebN k r := fun m hm => by
    have e : ∀ v, (GlobalTheory.Amp.lebN k r).map (Formalism.QuantumDeterminants.lmulM (Matrix.of (m v))) = GlobalTheory.Amp.lebN k r :=
      fun v => hH.2.2.2 _ (hN m hm v)
    haveI : ∀ v, SigmaFinite ((GlobalTheory.Amp.lebN k r).map (Formalism.QuantumDeterminants.lmulM (Matrix.of (m v)))) := fun v => by
      rw [e]; infer_instance
    have := Measure.pi_map_pi (μ := fun _ : ι => GlobalTheory.Amp.lebN k r)
      (f := fun v => Formalism.QuantumDeterminants.lmulM (Matrix.of (m v))) fun v => (GlobalTheory.DegVol.Cov.continuous_lmulM _).measurable.aemeasurable
    simp only [e] at this
    exact this
  exact le_antisymm
    (measure_le _ _ Γ Ω₁ Ω₂ hΓ hnull hinv hu hpres h₁ h₂)
    (measure_le _ _ Γ Ω₂ Ω₁ hΓ hnull hinv hu hpres h₂ h₁)

end GlobalTheory.FundEq
