import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
import Development.EtaleCohomology.WeilConjectures.AbsContPf
import Development.EtaleCohomology.WeilConjectures.ChevPf

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.degCont_of :
    StabOpen → DegCont := by
  intro hst l _ k Ω _ _ _ _ X p hqc hqs n i hfin v μ
  have habs := LateralTheory.EWeil.AbsContPf.AbsCont_of LateralTheory.EWeil.ChevPf.Chev_of
  have key : ∀ (φ : Hl l (sch.obj (geom Ω p)) n i →ₗ[ℤ_[l]] ℚ_[l]) (x : Hl l (sch.obj (geom Ω p)) n i),
      Continuous fun σ : Gal(Ω/k) => φ (galHl l Ω p n i σ x) := by
    intro φ x
    refine habs l Gal(Ω/k) (Hl l (sch.obj (geom Ω p)) n i) (galHl l Ω p n i)
      (fun m => LinearMap.ker (LateralTheory.EWeil.ContinCut.evk l (sch.obj (geom Ω p)) n i m))
      (LateralTheory.EWeil.ContinCut.evk_anti l _ n i) ?_ ?_ φ x
    · intro y hy
      apply Subtype.ext
      funext m
      simpa [LateralTheory.EWeil.ContinCut.evk] using hy m
    · intro y m
      have hset : {σ : Gal(Ω/k) | (galHl l Ω p n i σ) y - y ∈
          LinearMap.ker (LateralTheory.EWeil.ContinCut.evk l (sch.obj (geom Ω p)) n i m)} =
          {σ | (galHl l Ω p n i σ y).1 m = y.1 m} := by
        ext σ
        simp [LateralTheory.EWeil.ContinCut.evk, sub_eq_zero]
      rw [hset]
      exact hst l k Ω p hqc hqs n i y m
  induction v using TensorProduct.induction_on with
  | zero => simpa using continuous_const
  | tmul q x =>
    have hφ := key ((μ.restrictScalars ℤ_[l]) ∘ₗ (TensorProduct.mk ℤ_[l] ℚ_[l] _ 1)) x
    refine (Continuous.mul (continuous_const : Continuous fun _ : Gal(Ω/k) => q) hφ).congr ?_
    intro σ
    have e : galHQ l Ω p n i σ (q ⊗ₜ x) = q • ((1 : ℚ_[l]) ⊗ₜ (galHl l Ω p n i σ x)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [GlobalTheory.EtC.galHQ]
    rw [e, map_smul, smul_eq_mul]
    rfl
  | add a b ha hb =>
    exact (ha.add hb).congr fun σ => by simp only [map_add, Pi.add_apply]
