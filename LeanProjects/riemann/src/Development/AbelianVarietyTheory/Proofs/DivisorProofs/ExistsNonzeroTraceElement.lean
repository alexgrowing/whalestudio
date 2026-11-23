import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory

open Polynomial

theorem intCasimir_exists : ∀ (E : Type) [Field E] [NumberField E], ∃ (d : ℕ) (c θ : Fin d → 𝓞 E),
    (∀ o : 𝓞 E, ∑ j, c j ⊗ₜ[ℤ] (o * θ j) = ∑ j, (o * c j) ⊗ₜ[ℤ] θ j) ∧ ∑ j, c j * θ j ≠ 0 := by
  intro E _ _
  classical
  obtain ⟨α, -, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := ℂ) (RingHom.id ℂ)
    (fun τ => τ.comp (algebraMap (𝓞 E) E)) (fun _ _ => rfl)
  let g : ℤ[X] := minpoly ℤ α
  have hgα : aeval α g = 0 := minpoly.aeval ℤ α
  have hroot : (g.map (algebraMap ℤ (𝓞 E))).IsRoot α := by
    rw [IsRoot, Polynomial.eval_map, ← aeval_def, hgα]
  let q := (g.map (algebraMap ℤ (𝓞 E))) /ₘ (X - C α)
  have hq : (X - C α) * q = g.map (algebraMap ℤ (𝓞 E)) := mul_divByMonic_eq_iff_isRoot.2 hroot
  let iL : 𝓞 E →+* 𝓞 E ⊗[ℤ] 𝓞 E := Algebra.TensorProduct.includeLeftRingHom
  let iR : 𝓞 E →+* 𝓞 E ⊗[ℤ] 𝓞 E := (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] _).toRingHom
  have hiL : ∀ x, iL x = x ⊗ₜ[ℤ] 1 := fun _ => rfl
  have hiR : ∀ x, iR x = 1 ⊗ₜ[ℤ] x := fun _ => rfl
  let T : 𝓞 E ⊗[ℤ] 𝓞 E := q.eval₂ iL (iR α)
  have hT : T = ∑ j : Fin (q.natDegree + 1), q.coeff j ⊗ₜ[ℤ] (α ^ (j : ℕ)) := by
    show q.eval₂ iL (iR α) = _
    rw [eval₂_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun n => iL (q.coeff n) * (iR α) ^ n)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hiL, hiR, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul,
      _root_.mul_one, _root_.one_mul]
  have hαT : iR α * T = iL α * T := by
    have h1 : ((X - C α) * q).eval₂ iL (iR α) = 0 := by
      rw [hq, eval₂_map]
      have : iL.comp (algebraMap ℤ (𝓞 E)) = iR.comp (algebraMap ℤ (𝓞 E)) := RingHom.ext_int _ _
      rw [this, ← hom_eval₂, ← aeval_def, hgα, map_zero]
    rw [eval₂_mul, eval₂_sub, eval₂_X, eval₂_C] at h1
    exact sub_eq_zero.1 (by rw [← sub_mul]; exact h1)
  let I : Ideal (𝓞 E ⊗[ℤ] 𝓞 E) := (Submodule.span (𝓞 E ⊗[ℤ] 𝓞 E) {T}).annihilator
  have hmemI : ∀ r, r ∈ I ↔ r * T = 0 := fun r => by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  let π := Ideal.Quotient.mk I
  have hπα : (π.comp iR).toIntAlgHom α = (π.comp iL).toIntAlgHom α := by
    show π (iR α) = π (iL α)
    rw [Ideal.Quotient.eq, hmemI, sub_mul, hαT, sub_self]
  have key : ∀ p : ℤ[X], π (iR (aeval α p)) = π (iL (aeval α p)) := fun p => by
    have h1 := aeval_algHom_apply (π.comp iR).toIntAlgHom α p
    have h2 := aeval_algHom_apply (π.comp iL).toIntAlgHom α p
    rw [hπα] at h1
    exact h1.symm.trans h2
  haveI : Module.Free ℤ (𝓞 E) := inferInstance
  haveI : Module.Free ℤ (𝓞 E ⊗[ℤ] 𝓞 E) := Module.Free.of_basis
    ((Module.Free.chooseBasis ℤ (𝓞 E)).tensorProduct (Module.Free.chooseBasis ℤ (𝓞 E)))
  haveI : Module.IsTorsionFree ℤ (𝓞 E ⊗[ℤ] 𝓞 E) := inferInstance
  have hall : ∀ o : 𝓞 E, iR o * T = iL o * T := by
    intro o
    obtain ⟨N, p, hN0, hNp⟩ := hN o
    have h := key p
    rw [← hNp, Ideal.Quotient.eq, hmemI, map_mul, map_mul, map_intCast, map_intCast, ← mul_sub,
      _root_.mul_assoc, ← zsmul_eq_mul] at h
    rw [← sub_eq_zero, ← sub_mul]
    exact (smul_eq_zero.1 h).resolve_left hN0
  refine ⟨q.natDegree + 1, fun j => q.coeff j, fun j => α ^ (j : ℕ), fun o => ?_, ?_⟩
  · have h := hall o
    rw [hT, Finset.mul_sum, Finset.mul_sum] at h
    convert h using 2 with j
    · rw [hiR, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
    · rw [hiL, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
  · have hsum : ∑ j : Fin (q.natDegree + 1), q.coeff j * α ^ (j : ℕ) = q.eval α := by
      rw [eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun n => q.coeff n * α ^ n)]
    rw [hsum]
    have hd := congrArg derivative hq
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, _root_.one_mul,
      derivative_map] at hd
    have he := congrArg (eval α) hd
    rw [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, Polynomial.eval_map,
      ← aeval_def] at he
    rw [he]
    intro h0
    have hE : aeval (α : E) (derivative g) = 0 := by
      rw [Polynomial.aeval_algebraMap_apply, h0, map_zero]
    have hint : IsIntegral ℤ (α : E) := RingOfIntegers.isIntegral_coe α
    have hmin : minpoly ℚ (α : E) = g.map (algebraMap ℤ ℚ) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, NumberField.RingOfIntegers.minpoly_coe]
    have hsep := (Algebra.IsSeparable.isSeparable ℚ (α : E)).aeval_derivative_ne_zero
      (minpoly.aeval ℚ (α : E))
    rw [hmin, derivative_map, aeval_map_algebraMap] at hsep
    exact hsep hE

end GlobalTheory
