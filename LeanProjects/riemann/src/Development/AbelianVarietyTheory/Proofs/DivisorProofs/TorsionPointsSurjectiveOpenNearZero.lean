import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpOverFstComp
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
open GlobalTheory.SqZeroPt
open scoped GlobalTheory.SqZeroPt
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.OpenOmega

namespace GlobalTheory.OpenOmega

theorem spMap_fst_surjective (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] : Function.Surjective (spMap (TrivSqZeroExt.fstHom R R M).toRingHom) := by
  intro x
  refine ⟨PrimeSpectrum.comap (algebraMap R (TrivSqZeroExt R M)) x, ?_⟩
  change PrimeSpectrum.comap _ (PrimeSpectrum.comap _ x) = x
  have hx := PrimeSpectrum.isPrime x
  apply PrimeSpectrum.ext
  ext a
  change algebraMap R (TrivSqZeroExt R M) a.fst ∈ PrimeSpectrum.asIdeal x ↔ _
  have h : (TrivSqZeroExt.inr a.snd : TrivSqZeroExt R M) ∈ PrimeSpectrum.asIdeal x :=
    (hx.mem_or_mem (x := TrivSqZeroExt.inr a.snd) (y := TrivSqZeroExt.inr a.snd)
      (by rw [TrivSqZeroExt.inr_mul_inr]; exact zero_mem _)).elim id id
  rw [TrivSqZeroExt.algebraMap_eq_inl]
  conv_rhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a]
  exact (Ideal.add_mem_iff_left _ h).symm

theorem one_left {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] :
    (1 : SpAlg R R ⟶ G).left = η[G].left := by
  have hu : (toUnit (Over.mk (spMap (algebraMap R R)))).left = 𝟙 (Sp R) := by
    rw [Over.toUnit_left]; exact Spec.map_id _
  change (toUnit (Over.mk (spMap (algebraMap R R)))).left ≫ η[G].left = _
  erw [hu]
  exact Category.id_comp _

theorem ptSurj_of_isOpenNearZero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G]
    (GG : PDivGroup p R) (θ : TorsionMap G GG) (h : θ.IsOpenNearZero) (n : ℕ) : PtSurj θ n := by
  intro M _ _ _ _ φ hφ
  obtain ⟨U, V, hU, hb⟩ := h n
  have h1 : θ.pt n R ⟨1, one_pow _⟩ = Bialgebra.counitAlgHom R (GG.A n) := by
    have h1 := θ.pt_one n R (Fact.out : p.Prime).ne_zero
    ext a
    have h2 := congrArg (fun f : WithConv (GG.A n →ₐ[R] R) => f.ofConv a) h1
    simpa using h2
  have hU1 : (⟨1, one_pow _⟩ : Tors G (p ^ n) R) ∈ {z : Tors G (p ^ n) R | Set.range z.1.left ⊆ U} := by
    change Set.range (1 : SpAlg R R ⟶ G).left ⊆ U
    rw [one_left]
    exact hU
  have hV1 := (hb R).mapsTo hU1
  rw [h1, ← hφ] at hV1
  have hVφ : Set.range (spMap (φ : GG.A n →+* TrivSqZeroExt R M)) ⊆ V := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := spMap_fst_surjective R M x
    exact hV1 ⟨y, rfl⟩
  obtain ⟨z, hzU, hz⟩ := (hb (TrivSqZeroExt R M)).surjOn hVφ
  refine ⟨z, ?_, hz⟩
  let z' : Tors G (p ^ n) R := ⟨spOver (TrivSqZeroExt.fstHom R R M) ≫ z.1, by
    rw [← MonObj.comp_pow, z.2, MonObj.comp_one]⟩
  have hz'U : z' ∈ {z : Tors G (p ^ n) R | Set.range z.1.left ⊆ U} := by
    rintro _ ⟨x, rfl⟩
    exact hzU ⟨(spOver (TrivSqZeroExt.fstHom R R M)).left x, rfl⟩
  have e : z' = ⟨1, one_pow _⟩ := (hb R).injOn hz'U hU1 (by
    rw [θ.nat n _ R (TrivSqZeroExt.fstHom R R M) z z' rfl, hz, hφ, h1])
  have e2 := congrArg (fun w : Tors G (p ^ n) R => w.1.left) e
  ext1
  exact e2.trans (one_left G)

end GlobalTheory.OpenOmega
