import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

open Module
universe u v

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem monoidAlgebra_lift_freeMonoid_eq_wop {F A J : Type*} [Field F] [Ring A] [Algebra F A] (T : J → A)
    (t : MonoidAlgebra F (FreeMonoid J)) :
    MonoidAlgebra.lift F A (FreeMonoid J) (FreeMonoid.lift T) t = wop T (t.coeff : List J →₀ F) := by
  rw [MonoidAlgebra.lift_apply]
  unfold wop
  congr 1
  funext w c
  rw [FreeMonoid.lift_apply]
  rfl

private theorem algHom_wop_eq_wop_comp {F A B J : Type*} [Field F] [Ring A] [Algebra F A] [Ring B]
    [Algebra F B] (φ : A →ₐ[F] B) (T : J → A) (t : List J →₀ F) :
    φ (wop T t) = wop (fun j => φ (T j)) t := by
  unfold wop
  simp only [Finsupp.sum, map_sum, map_smul, map_list_prod, List.map_map]
  rfl

private theorem exists_idempotent_aeval_nilpotent_sub_of_isIntegral {F D : Type*} [Field F] [CommRing D] [Algebra F D] (x : D)
    (hx : IsIntegral F x) (c : F) :
    ∃ q : Polynomial F, q.eval c = 1 ∧ IsIdempotentElem (Polynomial.aeval x q) ∧
      ∃ N, (x - algebraMap F D c) ^ N * Polynomial.aeval x q = 0 := by
  obtain ⟨r, hm, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly F x)
    (minpoly.ne_zero hx) c
  set k := Polynomial.rootMultiplicity c (minpoly F x)
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C c) ^ (k + 1)) r :=
    ((Polynomial.irreducible_X_sub_C c).coprime_iff_not_dvd.mpr hndvd).pow_left
  obtain ⟨a, b, hab⟩ := hcop
  have h0 : Polynomial.aeval x (minpoly F x) = 0 := minpoly.aeval F x
  refine ⟨b * r, ?_, ?_, k + 1, ?_⟩
  · have := congrArg (Polynomial.eval c) hab
    simpa using this
  · have hid : (b * r) * (b * r) = b * r - a * b * (Polynomial.X - Polynomial.C c) * minpoly F x := by
      rw [hm]
      linear_combination (b * r) * hab
    unfold IsIdempotentElem
    rw [← map_mul, hid]
    simp only [map_sub, map_mul, h0, mul_zero, sub_zero]
  · have hz : (Polynomial.X - Polynomial.C c) ^ (k + 1) * (b * r) =
        b * (Polynomial.X - Polynomial.C c) * minpoly F x := by
      rw [hm]; ring
    have := congrArg (Polynomial.aeval x) hz
    simpa [h0] using this

theorem pProjOne_holds : ProjOne.{u} := by
  intro F _ A _ _ _ J T hT θ
  classical
  let gen : J → F × A := fun j => (θ j, T j)
  let D := Algebra.adjoin F (Set.range gen)
  have hcomm : ∀ a ∈ Set.range gen, ∀ b ∈ Set.range gen, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact Prod.ext (mul_comm _ _) (hT i j)
  letI : CommRing D := Algebra.adjoinCommRingOfComm F hcomm
  haveI : Module.Finite F D := inferInstanceAs (Module.Finite F (Subalgebra.toSubmodule D))
  let χ : D →ₐ[F] F := (AlgHom.fst F F A).comp D.val
  let b := Module.finBasis F D
  choose q hq1 hq2 N hN using fun i => exists_idempotent_aeval_nilpotent_sub_of_isIntegral (b i) (IsIntegral.of_finite F (b i)) (χ (b i))
  let z : D := ∏ i, Polynomial.aeval (b i) (q i)
  have hzid : IsIdempotentElem z := by
    unfold IsIdempotentElem
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hq2 i)
  have hzχ : χ z = 1 := by
    rw [map_prod]
    apply Finset.prod_eq_one
    intro i _
    rw [← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, hq1]
  have hnil : ∀ d : D, IsNilpotent ((d - algebraMap F D (χ d)) * z) := by
    let L : D →ₗ[F] D := LinearMap.mulRight F z ∘ₗ (LinearMap.id - (Algebra.linearMap F D) ∘ₗ χ.toLinearMap)
    have hL : ∀ d, L d = (d - algebraMap F D (χ d)) * z := fun d => rfl
    let S := ((nilradical D).restrictScalars F).comap L
    have hb : ∀ i, b i ∈ S := by
      intro i
      show L (b i) ∈ nilradical D
      rw [hL]
      have hsplit : z = Polynomial.aeval (b i) (q i) *
          ∏ j ∈ Finset.univ.erase i, Polynomial.aeval (b j) (q j) :=
        (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
      rw [hsplit, ← mul_assoc]
      apply Ideal.mul_mem_right
      rw [mem_nilradical]
      refine ⟨N i + 1, ?_⟩
      rw [mul_pow, (hq2 i).pow_succ_eq, pow_succ', mul_assoc, hN i, mul_zero]
    have hS : S = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hb i
    intro d
    have hd : d ∈ S := hS ▸ Submodule.mem_top
    rw [← mem_nilradical, ← hL]
    exact hd
  let Ψ := MonoidAlgebra.lift F (F × A) (FreeMonoid J) (FreeMonoid.lift gen)
  have hD : D ≤ Ψ.range := by
    apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    exact ⟨MonoidAlgebra.of F _ (FreeMonoid.of j), by simp [Ψ, MonoidAlgebra.lift_of]⟩
  obtain ⟨t, ht⟩ := hD z.2
  have ht' : MonoidAlgebra.lift F (F × A) (FreeMonoid J) (FreeMonoid.lift gen) t = z := ht
  have hwθ : wop θ t.coeff = (z : F × A).1 := by
    have h1 := algHom_wop_eq_wop_comp (AlgHom.fst F F A) gen t.coeff
    rw [← monoidAlgebra_lift_freeMonoid_eq_wop, ht'] at h1
    exact h1.symm
  have hwT : wop T t.coeff = (z : F × A).2 := by
    have h1 := algHom_wop_eq_wop_comp (AlgHom.snd F F A) gen t.coeff
    rw [← monoidAlgebra_lift_freeMonoid_eq_wop, ht'] at h1
    exact h1.symm
  refine ⟨t.coeff, ?_, ?_, ?_⟩
  · rw [hwθ]
    exact hzχ
  · rw [hwT]
    unfold IsIdempotentElem
    have h1 := congrArg (fun x : D => (x : F × A).2) hzid
    simpa using h1
  · intro j
    let d : D := ⟨gen j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
    obtain ⟨M, hM⟩ := hnil d
    refine ⟨M + 1, ?_⟩
    have h2 : (d - algebraMap F D (θ j)) ^ (M + 1) * z = 0 := by
      have h3 : ((d - algebraMap F D (χ d)) * z) ^ (M + 1) = 0 := by
        rw [pow_succ, hM, zero_mul]
      rw [mul_pow, hzid.pow_succ_eq] at h3
      exact h3
    have h4 := congrArg ((AlgHom.snd F F A).comp D.val) h2
    rw [hwT]
    simpa [d, gen] using h4

end UpperTheory.Gal.CertificateRingHomMap
