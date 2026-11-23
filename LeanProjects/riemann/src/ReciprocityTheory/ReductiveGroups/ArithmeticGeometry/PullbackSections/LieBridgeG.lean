import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {X0 : Scheme.{0}} {R : Type} [CommRing R] (x0 : Sp R ⟶ X0) {G : Over X0} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x0 Φ)

theorem epsScaleR_comp_alg (a : R) :
    (epsScaleR a).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
  ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

def scK (a : R) (p : epsR R ⟶ G') : epsR R ⟶ G' :=
  Over.homMk (spMap (epsScaleR a) ≫ p.left) (by
    rw [Category.assoc, Over.w p]
    show spMap (epsScaleR a) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R))
    rw [spMap_comp_spMap, epsScaleR_comp_alg])

variable {x0}

theorem push_inj : Function.Injective (pushHom h (epsR R)) := by
  intro p q hpq
  have e : p.left ≫ Φ = q.left ≫ Φ := congrArg (fun V => V.left) hpq
  apply Over.OverMorphism.ext
  exact h.1.hom_ext e ((Over.w p).trans (Over.w q).symm)

theorem push_surj (V : overAt x0 (DualNumber R) ⟶ G) : ∃ p, pushHom h (epsR R) p = V :=
  ⟨Over.homMk (h.1.lift V.left (epsR R).hom (Over.w V)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem push_scK (a : R) (p : epsR R ⟶ G') : pushHom h (epsR R) (scK a p) = smT x0 a (pushHom h (epsR R) p) :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

theorem scK_zero_iff (p : epsR R ⟶ G') : IsTangent p ↔ scK 0 p = 1 := by
  have e0 : epsScaleR (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have e1 : ((1 : epsR R ⟶ G').left) = spMap (algebraMap R (DualNumber R)) ≫ η[G'].left := by
    rw [Hom.one_def]; rfl
  have e2 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    rw [spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact Spec.map_id _
  constructor
  · intro hp
    apply Over.OverMorphism.ext
    show spMap (epsScaleR 0) ≫ p.left = _
    rw [e1, e0, ← spMap_comp_spMap, Category.assoc, hp]
  · intro hp
    have := congrArg (fun V => spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ V.left) hp
    rw [e1, ← Category.assoc, e2, Category.id_comp] at this
    show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ p.left = η[G'].left
    rw [← this]
    show _ = spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (spMap (epsScaleR 0) ≫ p.left)
    rw [e0, ← spMap_comp_spMap]
    simp only [← Category.assoc, e2, Category.id_comp]

theorem isTangent_iff (p : epsR R ⟶ G') : IsTangent p ↔ smT x0 0 (pushHom h (epsR R) p) = 1 := by
  rw [scK_zero_iff, ← push_scK h, ← map_one (pushHom h (epsR R))]
  exact (push_inj h).eq_iff.symm

theorem isLieComb_iff {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G')) (w : epsR R ⟶ G') :
    IsLieComb c v w ↔ pushHom h (epsR R) w = combT x0 (fun i => pushHom h (epsR R) (v i)) c := by
  have hprod : ∀ u : Fin m → (epsR R ⟶ G'), pushHom h (epsR R) (List.ofFn u).prod =
      ∏ i, pushHom h (epsR R) (u i) := fun u => by
    rw [map_list_prod, List.map_ofFn, List.prod_ofFn]; rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [hprod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show u i = scK (c i) (v i) from Over.OverMorphism.ext (hu i), push_scK]
  · intro hw
    refine ⟨fun i => scK (c i) (v i), fun i => rfl, push_inj h ?_⟩
    rw [hw, hprod]
    exact Finset.prod_congr rfl fun i _ => (push_scK h _ _).symm

end ReciprocityTheory.ChartRestriction.G.PullbackSections
