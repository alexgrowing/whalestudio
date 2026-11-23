import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSide
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * x) :=
  _root_.UpperTheory.Reformulated.B.DYha3.main x

theorem exists_nat_mul_isIntegral_of_isCompact (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {𝒦 : Set (Af F ⊗[F] E)} (h𝒦 : IsCompact 𝒦) :
    ∃ d : ℕ, 0 < d ∧ ∀ e : E, inclR (F := F) (Af F) e ∈ 𝒦 → IsIntegral ℤ ((d : E) * e) := by
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let bb := Algebra.TensorProduct.basis (Af F) b
  have hc : ∀ i, Continuous (fun x : Af F ⊗[F] E => bb.coord i x) := fun i =>
    IsModuleTopology.continuous_of_linearMap (bb.coord i)
  have hcoord : ∀ (e : E) i, bb.coord i (inclR (F := F) (Af F) e) = algebraMap F (Af F) (b.repr e i) := by
    intro e i
    change bb.repr ((1 : Af F) ⊗ₜ[F] e) i = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp [Algebra.algebraMap_eq_smul_one]
  choose m hm hmi using fun i =>
    GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_integral_of_isCompact F (h𝒦.image (hc i))
  choose D hD hDi using fun i => exists_nat_mul_isIntegral (b i)
  refine ⟨(∏ i, m i) * ∏ i, D i, Nat.mul_pos (Finset.prod_pos fun i _ => hm i)
    (Finset.prod_pos fun i _ => hD i), fun e he => ?_⟩
  have hsum : ((((∏ i, m i) * ∏ i, D i : ℕ)) : E) * e =
      ∑ i, algebraMap F E (((∏ i, m i : ℕ) : F) * b.repr e i) * (((∏ i, D i : ℕ)) : E) * b i := by
    conv_lhs => rw [← b.sum_repr e]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [hsum]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  obtain ⟨z, hz⟩ := hmi i (b.repr e i) ⟨_, he, hcoord e i⟩
  have h1 : IsIntegral ℤ (algebraMap F E (((∏ i, m i : ℕ) : F) * b.repr e i)) := by
    have : ((∏ i, m i : ℕ) : F) * b.repr e i = (q : F) * (z : F) := by
      rw [hq, hz, Nat.cast_mul]
      ring
    rw [this]
    exact IsIntegral.algebraMap ((isIntegral_natCast q).mul z.2)
  have h2 : (((∏ i, D i : ℕ)) : E) * b i = (r : E) * ((D i : E) * b i) := by
    rw [hr, Nat.cast_mul]
    ring
  rw [mul_assoc, h2]
  exact h1.mul ((isIntegral_natCast r).mul (hDi i))

end GlobalTheory.CompanionTheory.CFin

namespace GlobalTheory.CompanionTheory.CFin

theorem bounded_denominators : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (𝒞 : Set (GFin σ J)), IsCompact 𝒞 → ∀ {ι : Type} [Fintype ι] (A : Matrix ι (Fin n) E) (B : Matrix (Fin n) ι E), ∃ d : ℕ, 0 < d ∧ ∀ δ : GRat σ J, projFin σ J (ratEmb σ J δ) ∈ 𝒞 → ∀ u v, IsIntegral ℤ ((d : E) * (A * δ.1.1 * B) u v) := by
  intro F E _ _ _ _ _ σ n J 𝒞 h𝒞 ι _ A B
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  let f : ι → ι → GFin σ J → Af F ⊗[F] E := fun u v y =>
    (A.map (inclR (F := F) (Af F)) * (matHom (Af F) σ J y).1 * B.map (inclR (F := F) (Af F))) u v
  have hmat : Continuous fun y : GFin σ J => ((matHom (Af F) σ J y).1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    Units.continuous_val.comp (GlobalTheory.AdelicU.isEmbedding_matHom (Af F) σ J).continuous
  have hf : ∀ u v, Continuous (f u v) := fun u v => by
    have : Continuous fun y : GFin σ J =>
        A.map (inclR (F := F) (Af F)) * (matHom (Af F) σ J y).1 * B.map (inclR (F := F) (Af F)) :=
      (continuous_const.matrix_mul hmat).matrix_mul continuous_const
    exact this.matrix_elem u v
  obtain ⟨d, hd, h⟩ := exists_nat_mul_isIntegral_of_isCompact F E
    (𝒦 := ⋃ u, ⋃ v, f u v '' 𝒞)
    (isCompact_iUnion fun u => isCompact_iUnion fun v => h𝒞.image (hf u v))
  refine ⟨d, hd, fun δ hδ u v => h _ ?_⟩
  refine Set.mem_iUnion.2 ⟨u, Set.mem_iUnion.2 ⟨v, _, hδ, ?_⟩⟩
  have hval : ((matHom (Af F) σ J (GlobalTheory.AdelicU.projFin σ J (ratEmb σ J δ))).1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) =
      δ.1.1.map (inclR (F := F) (Af F)) := by
    refine Matrix.ext fun r s => ?_
    change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] (δ.1.1 r s)) =
      (1 : Af F) ⊗ₜ[F] (δ.1.1 r s)
    simp
  change (A.map (inclR (F := F) (Af F)) * (matHom (Af F) σ J (GlobalTheory.AdelicU.projFin σ J (ratEmb σ J δ))).1 *
    B.map (inclR (F := F) (Af F))) u v = _
  rw [hval, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]

end GlobalTheory.CompanionTheory.CFin

end
