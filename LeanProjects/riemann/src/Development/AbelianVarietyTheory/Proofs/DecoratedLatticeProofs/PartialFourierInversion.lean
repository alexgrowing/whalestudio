import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open scoped Topology

noncomputable section
namespace GlobalTheory.LocFlat.PartialFourier

theorem eventually_add_invariant {X : Type*} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    {f : X → ℂ} (hf : f ∈ SB X) : ∀ᶠ t in 𝓝 (0 : X), ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : X × X => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h1' : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + -t) = f x :=
    (continuous_neg.tendsto' (0 : X) 0 neg_zero).eventually h1
  filter_upwards [h1, h1'] with t ht ht' x
  by_cases hx : x ∈ tsupport f
  · exact ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · have := ht' _ hx'
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

omit [BorelSpace k] in

theorem partial_mem_SB {I J : Type} [Fintype I] [Fintype J] (ν : Measure k) {f : (I → k) × (J → k) → ℂ}
    (hf : f ∈ SB ((I → k) × (J → k))) :
    (fun x₁ : I → k => ∫ y : J → k, f (x₁, y) ∂(Measure.pi fun _ => ν)) ∈ SB (I → k) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_, ?_⟩
  · have h2 : Filter.Tendsto (fun z : I → k => ((z - x, 0) : (I → k) × (J → k))) (𝓝 x) (𝓝 0) := by
      have : Continuous (fun z : I → k => ((z - x, 0) : (I → k) × (J → k))) := by fun_prop
      convert this.tendsto x using 2
      simp only [sub_self]
      rfl
    filter_upwards [h2.eventually (eventually_add_invariant hf)] with z hz
    congr 1
    funext y
    have := hz (x, y)
    simpa using this
  · refine HasCompactSupport.intro (hf.2.image continuous_fst) fun x hx => ?_
    have : ∀ y, f (x, y) = 0 := fun y => image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩
    simp [this]

theorem partial_fourier_inversion : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I : Type) [Fintype I], ∃ C : ℝ, 0 < C ∧ ∀ (J : Type) [Fintype J] (a : I → k), ∀ f ∈ SB ((I → k) × (J → k)), Integrable (fun l : I → k => ∫ x : (I → k) × (J → k), f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν))) (Measure.pi fun _ => ν) ∧ ∫ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * (∫ x : (I → k) × (J → k), f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν))) ∂(Measure.pi fun _ => ν) = (C : ℂ) * ∫ y : J → k, f (a, y) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ ψ ν hψ hne hν I _
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hne
  have hO : 0 < ν.real (𝒪[k] : Set k) :=
    ENNReal.toReal_pos ((isOpen_int k).measure_pos ν ⟨0, zero_mem _⟩).ne' (isCompact_int k).measure_lt_top.ne
  have hpsi : ∀ u : k, (ψ (-u) : ℂ) * ψ u = 1 := by
    intro u
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  refine ⟨(nabs k c * ν.real (𝒪[k] : Set k) ^ 2) ^ Fintype.card I, by have := nabs_pos k c; positivity,
    fun J _ a f hf => ?_⟩
  set μI : Measure (I → k) := Measure.pi fun _ => ν with hμI
  set μJ : Measure (J → k) := Measure.pi fun _ => ν with hμJ
  set g : (I → k) → ℂ := fun x₁ => ∫ y, f (x₁, y) ∂μJ with hgdef
  have hg : g ∈ SB (I → k) := partial_mem_SB ν hf
  have hF : ∀ l : I → k, ∫ x, f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂(μI.prod μJ) = ∫ x₁, g x₁ * (ψ (x₁ ⬝ᵥ l) : ℂ) ∂μI := by
    intro l
    have hfi : Integrable f (μI.prod μJ) := hf.1.continuous.integrable_of_hasCompactSupport hf.2
    have hi : Integrable (fun x => f x * (ψ (l ⬝ᵥ x.1) : ℂ)) (μI.prod μJ) :=
      hfi.mul_bdd (c := 1)
        ((continuous_subtype_val.comp (hψ.comp (continuous_const.dotProduct continuous_fst))).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun q => (Circle.norm_coe _).le)
    rw [integral_prod _ hi]
    congr 1
    funext x₁
    simp only [hgdef, ← integral_mul_const, dotProduct_comm l]
  simp only [hF]
  refine ⟨?_, ?_⟩
  · have := FourierPi.fourier_mem_SB μI hc hg
    exact this.1.continuous.integrable_of_hasCompactSupport this.2
  · set h : (I → k) → ℂ := fun x => g (x + a) with hhdef
    have hh : h ∈ SB (I → k) :=
      ⟨hg.1.comp_continuous (continuous_add_const a), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
    have htr : ∀ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * ∫ x₁, g x₁ * (ψ (x₁ ⬝ᵥ l) : ℂ) ∂μI =
        ∫ x, h x * (ψ (x ⬝ᵥ l) : ℂ) ∂μI := by
      intro l
      rw [← integral_const_mul, ← integral_add_right_eq_self _ a]
      congr 1
      funext x
      have e1 : (x + a) ⬝ᵥ l = x ⬝ᵥ l + l ⬝ᵥ a := by rw [add_dotProduct, dotProduct_comm a l]
      rw [hhdef, e1, AddChar.map_add_eq_mul, Circle.coe_mul]
      linear_combination (g (x + a) * (ψ (x ⬝ᵥ l) : ℂ)) * hpsi (l ⬝ᵥ a)
    simp only [htr]
    obtain ⟨s, hs⟩ := FourierPi.fourier_inversion_pi μI hc hh
    have hb : ∀ r : kˣ, μI.real (FourierPi.box I r) = ν.real (cball r) ^ Fintype.card I := by
      intro r
      simp [hμI, Measure.real, FourierPi.box, Measure.pi_pi]
    rw [hs, hb, hb, ← mul_pow, measureReal_cball, measureReal_cball]
    have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
      rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
    simp only [hhdef, zero_add, hgdef, h4]
    push_cast
    ring

end GlobalTheory.LocFlat.PartialFourier
