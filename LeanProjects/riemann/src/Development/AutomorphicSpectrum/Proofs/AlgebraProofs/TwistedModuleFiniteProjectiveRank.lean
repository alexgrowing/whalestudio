import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

namespace GlobalTheory.CompanionTheory.Ar.TwModule

open GlobalTheory.CompanionTheory.Ar

variable {O : Type} [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L]

theorem twMod_smul (c : O) (x : L) :
    (c • (show TwMod s L from x) : TwMod s L) = (show TwMod s L from s c • x) := rfl

def twOut {n : ℕ} (f : (Fin n → O) →ₗ[O] L) : (Fin n → O) →ₗ[O] TwMod s L where
  toFun v := (show TwMod s L from f (fun i => s (v i)))
  map_add' v w := by
    have : (fun i => s ((v + w) i)) = (fun i => s (v i)) + (fun i => s (w i)) := by
      funext i; simp
    show f (fun i => s ((v + w) i)) = f (fun i => s (v i)) + f (fun i => s (w i))
    rw [this, map_add]
  map_smul' c v := by
    have : (fun i => s ((c • v) i)) = s c • (fun i => s (v i)) := by
      funext i; simp
    show f (fun i => s ((c • v) i)) = s c • f (fun i => s (v i))
    rw [this, map_smul]

def twIn {n : ℕ} (r : L →ₗ[O] (Fin n → O)) : TwMod s L →ₗ[O] (Fin n → O) where
  toFun x := fun i => s.symm (r (show L from x) i)
  map_add' x y := by
    funext i
    have h : r (show L from x + y) i = r (show L from x) i + r (show L from y) i :=
      congrFun (map_add r (show L from x) (show L from y)) i
    exact (congrArg s.symm h).trans (map_add s.symm _ _)
  map_smul' c x := by
    funext i
    have h : r (show L from c • x) i = s c * r (show L from x) i :=
      congrFun (map_smul r (s c) (show L from x)) i
    refine (congrArg s.symm h).trans ?_
    show s.symm (s c * r (show L from x) i) = c * s.symm (r (show L from x) i)
    rw [map_mul, s.symm_apply_apply]

theorem twOut_twIn {n : ℕ} (f : (Fin n → O) →ₗ[O] L) (r : L →ₗ[O] (Fin n → O)) (h : f ∘ₗ r = LinearMap.id)
    (x : TwMod s L) : twOut s L f (twIn s L r x) = x := by
  have hx : f (r (show L from x)) = (show L from x) := LinearMap.congr_fun h _
  show f (fun i => s (s.symm (r (show L from x) i))) = (show L from x)
  simpa using hx

theorem twOut_surjective {n : ℕ} (f : (Fin n → O) →ₗ[O] L) (hf : Function.Surjective f) :
    Function.Surjective (twOut s L f) := by
  intro x
  obtain ⟨v, hv⟩ := hf (show L from x)
  refine ⟨fun i => s.symm (v i), ?_⟩
  show f (fun i => s (s.symm (v i))) = (show L from x)
  simpa using hv

theorem finite_twMod [Module.Finite O L] : Module.Finite O (TwMod s L) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O L
  exact Module.Finite.of_surjective _ (twOut_surjective s L f hf)

theorem projective_twMod [Module.Finite O L] [Module.Projective O L] : Module.Projective O (TwMod s L) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O L
  obtain ⟨r, hr⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact Module.Projective.of_split (twIn s L r) (twOut s L f)
    (LinearMap.ext (twOut_twIn s L f r hr))

theorem rank_twMod : Module.rank O (TwMod s L) = Module.rank O L :=
  (rank_eq_of_equiv_equiv (s : O → O) (AddEquiv.refl (TwMod s L) : TwMod s L ≃+ L) s.bijective
    (fun _ _ => rfl))

theorem finrank_twMod : Module.finrank O (TwMod s L) = Module.finrank O L := by
  rw [Module.finrank, Module.finrank, rank_twMod]

end GlobalTheory.CompanionTheory.Ar.TwModule

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank :
    ∀ (O : Type) [CommRing O] [IsDomain O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L]
      [Module.Finite O L] [Module.Projective O L],
      Module.Finite O (TwMod s L) ∧ Module.Projective O (TwMod s L) ∧
        Module.finrank O (TwMod s L) = Module.finrank O L := by
  intro O _ _ s L _ _ _ _
  exact ⟨finite_twMod s L, projective_twMod s L, finrank_twMod s L⟩
