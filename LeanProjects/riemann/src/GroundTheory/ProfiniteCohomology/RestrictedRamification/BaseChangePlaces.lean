import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.LocalMaps
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.IsScalarTowerFiniteSubfieldAlgebraicClosure
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.SemiLocal

open scoped TensorProduct

universe u

noncomputable section

variable {F L : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  {v : HeightOneSpectrum (𝓞 F)}

section General

variable (j : L →ₐ[F] AlgebraicClosure (v.adicCompletion F))

def tensorLiftOfAlgHom :
    CompletionsOver L v →ₐ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F) :=
  (Algebra.TensorProduct.lift (Algebra.ofId _ _) j (fun _ _ ↦ Commute.all _ _)).comp
    (tensorEquiv L v).symm.toAlgHom

theorem tensorLiftOfAlgHom_tensorEquiv (t : v.adicCompletion F ⊗[F] L) :
    tensorLiftOfAlgHom j (tensorEquiv L v t) = Algebra.TensorProduct.lift (Algebra.ofId _ _) j
      (fun _ _ ↦ Commute.all _ _) t := by
  simp [tensorLiftOfAlgHom]

theorem tensorLiftOfAlgHom_tensorEquiv_tmul (a : v.adicCompletion F) (x : L) :
    tensorLiftOfAlgHom j (tensorEquiv L v (a ⊗ₜ x)) =
      algebraMap (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) a * j x := by
  rw [tensorLiftOfAlgHom_tensorEquiv, Algebra.TensorProduct.lift_tmul]
  rfl

theorem tensorLiftOfAlgHom_algebraMap (x : L) :
    tensorLiftOfAlgHom j (algebraMap L (CompletionsOver L v) x) = j x := by
  rw [← tensorEquiv_one_tmul, tensorLiftOfAlgHom_tensorEquiv]
  simp

open Classical in
theorem exists_unique_tensorLiftOfAlgHom_single :
    ∃! w : PlacesOver L v, tensorLiftOfAlgHom j (Pi.single w 1) = 1 :=
  exists_unique_map_single_one_eq_one (tensorLiftOfAlgHom j).toRingHom

def placeOfAlgHom : PlacesOver L v :=
  (exists_unique_tensorLiftOfAlgHom_single j).exists.choose

open Classical in
theorem tensorLiftOfAlgHom_single_placeOfAlgHom :
    tensorLiftOfAlgHom j (Pi.single (placeOfAlgHom j) 1) = 1 :=
  (exists_unique_tensorLiftOfAlgHom_single j).exists.choose_spec

open Classical in
theorem eq_placeOfAlgHom_of_tensorLiftOfAlgHom {w : PlacesOver L v}
    (h : tensorLiftOfAlgHom j (Pi.single w 1) = 1) : w = placeOfAlgHom j :=
  (exists_unique_tensorLiftOfAlgHom_single j).unique h (tensorLiftOfAlgHom_single_placeOfAlgHom j)

theorem pi_single_algebraMap_completionsOver {w : PlacesOver L v} [DecidableEq (PlacesOver L v)]
    (a : v.adicCompletion F) :
    Pi.single w (algebraMap (v.adicCompletion F) (w.1.adicCompletion L) a) =
      algebraMap (v.adicCompletion F) (CompletionsOver L v) a * Pi.single w 1 := by
  funext u
  by_cases hu : u = w
  · subst hu
    simp
  · simp [hu]

open Classical in

def completionEmbeddingOfAlgHom :
    (placeOfAlgHom j).1.adicCompletion L →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F) where
  toFun x := tensorLiftOfAlgHom j (Pi.single (placeOfAlgHom j) x)
  map_one' := tensorLiftOfAlgHom_single_placeOfAlgHom j
  map_mul' x y := by rw [Pi.single_mul, map_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' x y := by rw [Pi.single_add, map_add]
  commutes' a := by
    rw [pi_single_algebraMap_completionsOver, map_mul, AlgHom.commutes,
      tensorLiftOfAlgHom_single_placeOfAlgHom,
      mul_one]

theorem tensorLiftOfAlgHom_eq (y : CompletionsOver L v) :
    tensorLiftOfAlgHom j y = completionEmbeddingOfAlgHom j (y (placeOfAlgHom j)) := by
  classical
  exact map_eq_map_single_of_map_single_one (φ := (tensorLiftOfAlgHom j).toRingHom)
    (tensorLiftOfAlgHom_single_placeOfAlgHom j) y

@[simp]
theorem completionEmbeddingOfAlgHom_algebraMap (x : L) :
    completionEmbeddingOfAlgHom j (algebraMap L ((placeOfAlgHom j).1.adicCompletion L) x) = j x := by
  rw [← tensorLiftOfAlgHom_algebraMap j x, tensorLiftOfAlgHom_eq]
  rfl

end General

theorem adicCompletion_algHom_ext {B : Type*} [Semiring B] [Algebra F B]
    [Algebra (v.adicCompletion F) B] [IsScalarTower F (v.adicCompletion F) B]
    {w : PlacesOver L v} {f g : w.1.adicCompletion L →ₐ[v.adicCompletion F] B}
    (h : ∀ x : L, f (algebraMap L _ x) = g (algebraMap L _ x)) : f = g := by
  have key : (f.comp (Pi.evalAlgHom _ _ w)).comp (tensorEquiv L v).toAlgHom =
      (g.comp (Pi.evalAlgHom _ _ w)).comp (tensorEquiv L v).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro a x
    change f ((tensorEquiv L v (a ⊗ₜ x)) w) = g ((tensorEquiv L v (a ⊗ₜ x)) w)
    rw [tensorEquiv_tmul, Pi.mul_apply, map_mul, map_mul]
    congr 1
    · change f (algebraMap _ _ a) = g (algebraMap _ _ a)
      rw [AlgHom.commutes, AlgHom.commutes]
    · exact h x
  ext y
  classical
  obtain ⟨t, ht⟩ := (tensorEquiv L v).surjective (Pi.single w y)
  have := DFunLike.congr_fun key t
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at this
  rw [show (tensorEquiv L v).toAlgHom t = tensorEquiv L v t from rfl, ht,
    Pi.single_eq_same] at this
  exact this

section Place

variable (j : L →ₐ[F] AlgebraicClosure (v.adicCompletion F))

theorem eq_placeOfAlgHom {w : PlacesOver L v}
    (c : w.1.adicCompletion L →ₐ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F))
    (hc : ∀ x : L, c (algebraMap L _ x) = j x) : w = placeOfAlgHom j := by
  classical
  have key : tensorLiftOfAlgHom j = c.comp (Pi.evalAlgHom _ _ w) := by
    have : (tensorLiftOfAlgHom j).comp (tensorEquiv L v).toAlgHom =
        (c.comp (Pi.evalAlgHom _ _ w)).comp (tensorEquiv L v).toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro a x
      change tensorLiftOfAlgHom j (tensorEquiv L v (a ⊗ₜ x)) = c ((tensorEquiv L v (a ⊗ₜ x)) w)
      rw [tensorLiftOfAlgHom_tensorEquiv_tmul, tensorEquiv_tmul, Pi.mul_apply, map_mul, ← hc x]
      congr 1
      exact (c.commutes a).symm
    ext y
    obtain ⟨t, rfl⟩ := (tensorEquiv L v).surjective y
    exact DFunLike.congr_fun this t
  apply eq_placeOfAlgHom_of_tensorLiftOfAlgHom
  refine (DFunLike.congr_fun key _).trans ?_
  rw [AlgHom.comp_apply, Pi.evalAlgHom_apply, Pi.single_eq_same, map_one]

theorem finiteDimensional_adicCompletion_of_placesOver (w : PlacesOver L v) :
    FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion L) :=
  Module.finite_of_finrank_pos (by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg]
    exact Nat.mul_pos (Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 F))
      (Ideal.inertiaDeg_pos w.1.asIdeal (𝓞 F)))

theorem exists_placeOfAlgHom_eq (w : PlacesOver L v) :
    ∃ j : L →ₐ[F] AlgebraicClosure (v.adicCompletion F), placeOfAlgHom j = w := by
  have := finiteDimensional_adicCompletion_of_placesOver w
  let c : w.1.adicCompletion L →ₐ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F) :=
    IsAlgClosed.lift
  let j : L →ₐ[F] AlgebraicClosure (v.adicCompletion F) :=
    (c.restrictScalars F).comp (IsScalarTower.toAlgHom F L (w.1.adicCompletion L))
  exact ⟨j, (eq_placeOfAlgHom j c fun _ => rfl).symm⟩

theorem placeOfAlgHom_comp (g : Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F)) :
    placeOfAlgHom (((g : AlgebraicClosure (v.adicCompletion F) →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F)).restrictScalars F).comp j) = placeOfAlgHom j :=
  (eq_placeOfAlgHom _ ((g : AlgebraicClosure (v.adicCompletion F) →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F)).comp (completionEmbeddingOfAlgHom j)) fun x => by
    rw [AlgHom.comp_apply, completionEmbeddingOfAlgHom_algebraMap]
    rfl).symm

theorem exists_algEquiv_comp_eq {K : Type*} [Field K] [Algebra (v.adicCompletion F) K]
    (c c' : K →ₐ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F)) :
    ∃ g : Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F), ∀ y, c' y = g (c y) := by
  let χ : c.fieldRange ≃ₐ[v.adicCompletion F] c'.fieldRange :=
    c.equivFieldRange.symm.trans c'.equivFieldRange
  refine ⟨χ.liftNormal (AlgebraicClosure (v.adicCompletion F)), fun y => ?_⟩
  have h := χ.liftNormal_commutes (AlgebraicClosure (v.adicCompletion F)) ⟨c y, y, rfl⟩
  refine Eq.trans ?_ h.symm
  change c' y = ((c'.equivFieldRange (c.equivFieldRange.symm ⟨c y, y, rfl⟩)) : _)
  have : c.equivFieldRange.symm ⟨c y, y, rfl⟩ = y :=
    c.equivFieldRange.symm_apply_eq.2 (Subtype.ext rfl)
  rw [this]
  rfl

theorem exists_algEquiv_of_placeOfAlgHom_eq (j j' : L →ₐ[F] AlgebraicClosure (v.adicCompletion F))
    (h : placeOfAlgHom j = placeOfAlgHom j') :
    ∃ g : Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F), ∀ x, j' x = g (j x) := by
  obtain ⟨c', hc'⟩ : ∃ c' : (placeOfAlgHom j).1.adicCompletion L →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F), ∀ x, c' (algebraMap L _ x) = j' x := by
    rw [h]
    exact ⟨completionEmbeddingOfAlgHom j', completionEmbeddingOfAlgHom_algebraMap j'⟩
  obtain ⟨g, hg⟩ := exists_algEquiv_comp_eq (completionEmbeddingOfAlgHom j) c'
  refine ⟨g, fun x => ?_⟩
  rw [← hc' x, hg, completionEmbeddingOfAlgHom_algebraMap]

theorem apply_completionEmbeddingOfAlgHom_of_forall
    (g : Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F)) (hg : ∀ x, g (j x) = j x)
    (y : (placeOfAlgHom j).1.adicCompletion L) :
    g (completionEmbeddingOfAlgHom j y) = completionEmbeddingOfAlgHom j y := by
  have : ((g : AlgebraicClosure (v.adicCompletion F) →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F)).comp (completionEmbeddingOfAlgHom j)) =
        completionEmbeddingOfAlgHom j :=
    adicCompletion_algHom_ext fun x => by
      rw [AlgHom.comp_apply, completionEmbeddingOfAlgHom_algebraMap]
      exact hg x
  exact DFunLike.congr_fun this y

end Place

end

end GroundTheory.ProfCoh
