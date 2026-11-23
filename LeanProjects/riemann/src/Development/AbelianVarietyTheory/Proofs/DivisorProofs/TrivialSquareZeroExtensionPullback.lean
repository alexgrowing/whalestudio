import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SqZeroPb

def liftHom {K : Type} [Field K] {V W₁ W₂ : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁]
    [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂]
    (e : V ≃ₗ[K] W₁ × W₂) {T : Type} [CommRing T]
    (a : T →+* TrivSqZeroExt K W₁) (b : T →+* TrivSqZeroExt K W₂)
    (h : ∀ t, (a t).fst = (b t).fst) : T →+* TrivSqZeroExt K V where
  toFun t := TrivSqZeroExt.inl (a t).fst + TrivSqZeroExt.inr (e.symm ((a t).snd, (b t).snd))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, zero_add, smul_eq_mul, op_smul_eq_smul, smul_zero]
      rw [← map_smul, ← map_smul, ← map_add]
      congr 1
      ext <;> simp [h]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add]
      rw [show ((a x).snd + (a y).snd, (b x).snd + (b y).snd)
          = ((a x).snd, (b x).snd) + ((a y).snd, (b y).snd) from rfl, map_add]

end GlobalTheory.SqZeroPb

open GlobalTheory.SqZeroPb in
theorem GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt : ∀ (K : Type) [Field K] (V W₁ W₂ : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁] [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂] (p : V →ₗ[K] W₁) (q : V →ₗ[K] W₂), Function.Bijective (LinearMap.prod p q) → IsPullback (CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom) := by
  intro K _ V W₁ W₂ _ _ _ _ _ _ _ _ _ _ _ _ p q hpq
  let e := LinearEquiv.ofBijective (LinearMap.prod p q) hpq
  have he : ∀ v, e v = (p v, q v) := fun v => rfl
  have hw : CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom =
      CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom := by
    ext x; simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => CommRingCat.ofHom (liftHom e s.fst.hom s.snd.hom ?_)) ?_ ?_ ?_)
  · intro t
    have := congrArg (fun φ => φ.hom t) s.condition
    simpa using this
  · intro s
    ext t : 2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom]
    · simp [liftHom]
      exact congrArg Prod.fst (e.apply_symm_apply _)
  · intro s
    ext t : 2
    have hc := congrArg (fun φ => φ.hom t) s.condition
    simp at hc
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom, hc]
    · simp [liftHom]
      exact congrArg Prod.snd (e.apply_symm_apply _)
  · intro s m hm1 hm2
    ext t : 2
    have h1 := congrArg (fun φ => φ.hom t) hm1
    have h2 := congrArg (fun φ => φ.hom t) hm2
    simp at h1 h2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom, ← h1]
    · simp [liftHom, ← h1, ← h2]
      rw [LinearEquiv.eq_symm_apply]
      rfl
