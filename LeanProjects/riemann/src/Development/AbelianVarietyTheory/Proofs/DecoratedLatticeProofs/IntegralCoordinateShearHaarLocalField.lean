import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.CoordShear

theorem measurePreserving_shear {k : Type} [AddCommGroup k] [MeasurableSpace k] [MeasurableAdd₂ k]
    (ν : Measure k) [SigmaFinite ν] [ν.IsAddLeftInvariant]
    {J : Type} [Fintype J] [DecidableEq J] (S : Finset J) (g : (J → k) → (J → k))
    (hg : Measurable g) (h1 : ∀ y y' : J → k, (∀ j, j ∉ S → y j = y' j) → g y = g y')
    (h2 : ∀ (y : J → k) j, j ∉ S → g y j = 0) :
    MeasurePreserving (fun y => y + g y) (Measure.pi fun _ : J => ν) (Measure.pi fun _ : J => ν) := by
  classical
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => k) (fun j => j ∉ S) with he
  have he_mp : MeasurePreserving e (Measure.pi fun _ : J => ν)
      ((Measure.pi fun _ : {j // j ∉ S} => ν).prod (Measure.pi fun _ : {j // ¬ j ∉ S} => ν)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : J => ν) (fun j => j ∉ S)
  let G : ({j // j ∉ S} → k) → ({j // ¬ j ∉ S} → k) := fun b i => g (e.symm (b, 0)) i
  have hG : Measurable G := by
    refine measurable_pi_lambda _ fun i => ?_
    exact (measurable_pi_apply (i : J)).comp
      (hg.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))
  have hΦ : MeasurePreserving
      (fun p : ({j // j ∉ S} → k) × ({j // ¬ j ∉ S} → k) => (id p.1, G p.1 + p.2))
      ((Measure.pi fun _ : {j // j ∉ S} => ν).prod (Measure.pi fun _ : {j // ¬ j ∉ S} => ν))
      ((Measure.pi fun _ : {j // j ∉ S} => ν).prod (Measure.pi fun _ : {j // ¬ j ∉ S} => ν)) := by
    refine (MeasurePreserving.id _).skew_product (g := fun b a => G b + a) ?_ ?_
    · exact (hG.comp measurable_fst).add measurable_snd
    · exact Filter.Eventually.of_forall fun b => (measurePreserving_add_left _ (G b)).map_eq

  have hGy : ∀ y : J → k, g (e.symm ((e y).1, 0)) = g y := by
    intro y
    refine h1 _ _ fun j hj => ?_
    simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
  have key : (fun y => y + g y) = e.symm ∘ (fun p => (id p.1, G p.1 + p.2)) ∘ e := by
    funext y
    apply e.injective
    rw [Function.comp_apply, Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, h2 y i i.2]
    · have := congrFun (hGy y) i
      simp only [G, Pi.add_apply]
      rw [this]
      simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, add_comm]
  rw [key]
  exact (MeasurePreserving.symm e he_mp).comp (hΦ.comp he_mp)

theorem integral_shear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (J : Type) [Fintype J] [DecidableEq J] (S : Finset J) (g : (J → k) → (J → k)), Continuous g → (∀ y y' : J → k, (∀ j, j ∉ S → y j = y' j) → g y = g y') → (∀ (y : J → k) j, j ∉ S → g y j = 0) → ∀ F : (J → k) → ℂ, ∫ y, F (y + g y) ∂(Measure.pi fun _ => ν) = ∫ y, F y ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ ν hν J _ _ S g hg h1 h2 F

  have : SecondCountableTopology k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    let : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    let : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
    have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    exact secondCountable_of_proper
  have := hν
  have hgm : Measurable g := hg.measurable
  have hmp := measurePreserving_shear ν S g hgm h1 h2
  have hfix : ∀ y, g (y + g y) = g y := fun y => h1 _ _ fun j hj => by simp [h2 y j hj]
  have hfix' : ∀ y, g (y - g y) = g y := fun y => h1 _ _ fun j hj => by simp [h2 y j hj]
  have hsurj : Function.Surjective (fun y : J → k => y + g y) :=
    fun y => ⟨y - g y, by simp [hfix']⟩
  have hemb : MeasurableEmbedding (fun y : J → k => y + g y) :=
    MeasurableEmbedding.of_measurable_inverse (g := fun y => y - g y) (measurable_id.add hgm)
      (by rw [hsurj.range_eq]; exact MeasurableSet.univ) (measurable_id.sub hgm)
      (fun y => by simp [hfix])
  exact hmp.integral_comp hemb F

end GlobalTheory.CoordShear
