import Mathlib
open MeasureTheory Set
open scoped ContDiff

namespace GlobalTheory

theorem setIntegral_unitCube_eq_of_torus_parametrisations :
    ∀ (ι X : Type) [Fintype ι] [TopologicalSpace X] [T2Space X] (e e' : (ι → ℝ) → X), Continuous e → Continuous e' → (∀ x y, e x = e y ↔ ∀ i, ∃ n : ℤ, x i - y i = n) → (∀ x y, e' x = e' y ↔ ∀ i, ∃ n : ℤ, x i - y i = n) → Set.range e = Set.range e' → (∀ x x' y y', e x = e' x' → e y = e' y' → e (x + y) = e' (x' + y')) → ∀ F : X → ℂ, ContinuousOn F (Set.range e) → ∫ x in Icc (0 : ι → ℝ) 1, F (e x) = ∫ x in Icc (0 : ι → ℝ) 1, F (e' x) := by
  intro ι X _ _ _ e e' hec he'c he he' hr hadd F hF
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  haveI : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
  let p : (ι → ℝ) → UnitAddTorus ι := fun x i => (x i : UnitAddCircle)
  have hq : IsOpenQuotientMap p :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have hpadd : ∀ x y, p (x + y) = p x + p y := fun x y => by
    funext i
    exact AddCircle.coe_add (1 : ℝ) (x i) (y i)
  have hpeq : ∀ x y, p x = p y ↔ ∀ i, ∃ n : ℤ, x i - y i = n := by
    intro x y
    simp only [p, funext_iff]
    refine forall_congr' fun i => ?_
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    simp [eq_comm]
  let σ := Function.surjInv hq.surjective
  have hσ : ∀ t, p (σ t) = t := Function.surjInv_eq hq.surjective

  let E : UnitAddTorus ι → X := fun t => e (σ t)
  let E' : UnitAddTorus ι → X := fun t => e' (σ t)
  have hEp : ∀ x, E (p x) = e x := fun x => (he _ _).2 ((hpeq _ _).1 (hσ (p x)))
  have hE'p : ∀ x, E' (p x) = e' x := fun x => (he' _ _).2 ((hpeq _ _).1 (hσ (p x)))
  have hEc : Continuous E := hq.isQuotientMap.continuous_iff.2 (by
    have : E ∘ p = e := funext hEp
    rw [this]; exact hec)
  have hE'c : Continuous E' := hq.isQuotientMap.continuous_iff.2 (by
    have : E' ∘ p = e' := funext hE'p
    rw [this]; exact he'c)
  have hE'i : Function.Injective E' := fun s t h => by
    rw [← hσ s, ← hσ t]; exact (hpeq _ _).2 ((he' _ _).1 h)
  have hrE : range E = range e := by
    ext z; constructor
    · rintro ⟨t, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨p x, hEp x⟩
  have hrE' : range E' = range e' := by
    ext z; constructor
    · rintro ⟨t, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨p x, hE'p x⟩
  have hα : ∀ t, ∃ u, E' u = E t := fun t => by
    have : E t ∈ range E' := by rw [hrE', ← hr, ← hrE]; exact ⟨t, rfl⟩
    exact this
  choose α hαE using hα
  have hemb : Topology.IsClosedEmbedding E' := hE'c.isClosedEmbedding hE'i
  have hαc : Continuous α := hemb.isInducing.continuous_iff.2 (by
    have : E' ∘ α = E := funext hαE
    rw [this]; exact hEc)
  have hαadd : ∀ s t, α (s + t) = α s + α t := by
    intro s t
    apply hE'i
    rw [hαE]
    obtain ⟨x, rfl⟩ := hq.surjective s
    obtain ⟨y, rfl⟩ := hq.surjective t
    obtain ⟨x', hx'⟩ := hq.surjective (α (p x))
    obtain ⟨y', hy'⟩ := hq.surjective (α (p y))
    have h1 : e x = e' x' := by rw [← hEp x, ← hE'p x', hx', hαE]
    have h2 : e y = e' y' := by rw [← hEp y, ← hE'p y', hy', hαE]
    rw [← hx', ← hy', ← hpadd, ← hpadd, hEp, hE'p]
    exact hadd x x' y y' h1 h2
  have hαs : Function.Surjective α := fun u => by
    obtain ⟨t, ht⟩ : E' u ∈ range E := by rw [hrE, hr, ← hrE']; exact ⟨u, rfl⟩
    exact ⟨t, hE'i (by rw [hαE]; exact ht)⟩
  let A : UnitAddTorus ι →+ UnitAddTorus ι := AddMonoidHom.mk' α hαadd
  have hmp : MeasurePreserving A volume volume :=
    AddMonoidHom.measurePreserving (f := A) hαc hαs rfl
  let G' : UnitAddTorus ι → ℂ := fun t => F (E' t)
  have hG'c : Continuous G' := hF.comp_continuous hE'c (fun t => by
    rw [hr, ← hrE']; exact ⟨t, rfl⟩)
  have hint : ∫ t, F (E t) = ∫ t, F (E' t) := by
    have : (fun t => F (E t)) = fun t => G' (A t) := funext fun t => by
      simp only [G', A, AddMonoidHom.mk'_apply, hαE]
    rw [this, ← integral_map hmp.measurable.aemeasurable hG'c.aestronglyMeasurable, hmp.map_eq]
  have hae : Set.Icc (0 : ι → ℝ) 1 =ᵐ[volume]
      {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} := by
    have h := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : ι => (volume : Measure ℝ))
      (f := (0 : ι → ℝ)) (g := 1)
    have e0 : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)}
        = Set.univ.pi fun i => Set.Ioc ((0 : ι → ℝ) i) ((1 : ι → ℝ) i) := by
      ext x
      simp [Set.mem_pi]
    rw [e0]
    exact h.symm
  have hEp' : ∀ x : ι → ℝ, E (fun i => (x i : UnitAddCircle)) = e x := hEp
  have hE'p' : ∀ x : ι → ℝ, E' (fun i => (x i : UnitAddCircle)) = e' x := hE'p
  have h1 := UnitAddTorus.integral_preimage (fun t => F (E t)) 0
  have h2 := UnitAddTorus.integral_preimage (fun t => F (E' t)) 0
  simp only [hEp'] at h1
  simp only [hE'p'] at h2
  rw [setIntegral_congr_set hae, setIntegral_congr_set hae, ← h1, ← h2]
  exact hint

end GlobalTheory
