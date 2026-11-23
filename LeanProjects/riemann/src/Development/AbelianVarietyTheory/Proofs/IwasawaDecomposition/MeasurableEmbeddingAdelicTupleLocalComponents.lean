import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeGlue

theorem polishSpace_addCommGroup (G : Type) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] :
    PolishSpace G := by
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace G := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : (uniformity G).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem repr_map (φ : R →ₐ[F] R') (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem tens_ext {z z' : R ⊗[F] E} (h : ∀ k, (Algebra.TensorProduct.basis R b).repr z k =
    (Algebra.TensorProduct.basis R b).repr z' k) : z = z' :=
  (Algebra.TensorProduct.basis R b).ext_elem h

theorem exists_repr (c : Fin d → R) :
    ∃ z : R ⊗[F] E, ∀ k, (Algebra.TensorProduct.basis R b).repr z k = c k :=
  ⟨(Algebra.TensorProduct.basis R b).equivFun.symm c, fun k => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]⟩

include b in
theorem continuous_map [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace R']
    [IsTopologicalRing R'] (φ : R →ₐ[F] R') (hφ : Continuous φ) :
    Continuous (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have h1 : Continuous (Algebra.TensorProduct.basis R b).equivFun :=
    IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
  have h2 : Continuous (Algebra.TensorProduct.basis R' b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R' b).equivFun.symm.toLinearMap
  have h3 : Continuous fun z : R ⊗[F] E => fun k => φ ((Algebra.TensorProduct.basis R b).equivFun z k) :=
    continuous_pi fun k => hφ.comp ((continuous_apply k).comp h1)
  refine (h2.comp h3).congr fun z => ?_
  simp only [Function.comp_apply]
  rw [LinearEquiv.symm_apply_eq]
  funext k
  simp only [Module.Basis.equivFun_apply, repr_map]

end Coord

section Adele

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) {n M : ℕ}

theorem repr_projInf (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).1 :=
  repr_map b (fstA F) _ k

theorem repr_projV (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n)
    (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 v :=
  (repr_map b (evalV F v) _ k).trans (congrArg (evalV F v) (repr_map b (sndA F) _ k))

theorem continuous_fstA : Continuous (fstA F) := continuous_fst

theorem continuous_sndA : Continuous (sndA F) := continuous_snd

theorem continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval v

theorem adele_ext {x y : AF F} (h1 : x.1 = y.1) (h2 : ∀ v, x.2 v = y.2 v) : x = y :=
  Prod.ext h1 (RestrictedProduct.ext _ _ h2)

theorem exists_adele (x : Ainf F) (y : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (hy : ∀ᶠ v in Filter.cofinite, y v ∈ v.adicCompletionIntegers F) :
    ∃ z : AF F, z.1 = x ∧ ∀ v, z.2 v = y v :=
  ⟨pairA F x ⟨y, hy⟩, rfl, fun _ => rfl⟩

include b in
theorem continuous_projInf : Continuous (projInf (F := F) (E := E) (M := M) (n := n)) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_map b (fstA F) continuous_fstA).comp
      ((continuous_apply i).comp (continuous_apply a))

include b in
theorem continuous_projV (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_map b (evalV F v) (continuous_evalV v)).comp
      ((continuous_map b (sndA F) continuous_sndA).comp
        ((continuous_apply i).comp (continuous_apply a)))

include b in
theorem injective_glue : Function.Injective (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) := by
  intro X X' h
  have h1 : projInf X = projInf X' := congrArg Prod.fst h
  have h2 : ∀ v, projV v (projFin X) = projV v (projFin X') := congrFun (congrArg Prod.snd h)
  funext a i
  refine tens_ext b fun k => adele_ext ?_ fun v => ?_
  · rw [← repr_projInf, ← repr_projInf, h1]
  · rw [← repr_projV, ← repr_projV, h2]

theorem range_glue : Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) =
    {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} := by
  ext Y
  constructor
  · rintro ⟨X, rfl⟩
    have : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ a i k,
        ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 v ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k =>
        ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2.2
    filter_upwards [this] with v hv a i k
    rw [repr_projV]
    exact hv a i k
  · intro hY
    choose c hc1 hc2 using fun (a : Fin n) (i : Fin M) (k : Fin d) =>
      exists_adele ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y.1 a i) k)
        (fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (Y.2 v a i) k)
        (Filter.Eventually.mono hY fun v hv => hv a i k)
    choose X hX using fun a i => exists_repr b (c a i)
    have h1 : projInf X = Y.1 := by
      funext a i
      refine tens_ext b fun k => ?_
      rw [repr_projInf, hX, hc1]
    have h2 : ∀ v, projV v (projFin X) = Y.2 v := fun v => by
      funext a i
      refine tens_ext b fun k => ?_
      rw [repr_projV, hX, hc2]
    exact ⟨X, Prod.ext h1 (funext h2)⟩

end Adele

theorem adelicTuple_measurableEmbedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), MeasurableEmbedding (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) ∧ Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) = {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} ∧ Continuous (projInf (F := F) (E := E) (M := M) (n := n)) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) := by
  intro F E _ _ _ _ _ d b n M
  refine ⟨?_, range_glue b, continuous_projInf b, continuous_projV b⟩
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  haveI : PolishSpace (Fin n → Fin M → AF F ⊗[F] E) := polishSpace_addCommGroup _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (Fv F v ⊗[F] E) := fun v =>
    inferInstance
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v =>
    inferInstance
  haveI : BorelSpace (∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E) :=
    Pi.borelSpace
  haveI : BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := inferInstance
  exact ((continuous_projInf b).prodMk (continuous_pi (continuous_projV b))).measurableEmbedding
    (injective_glue b)

end GlobalTheory.GaugeGlue
