import Mathlib
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedSplit

open GlobalTheory.SplitIdem GlobalTheory.IdemModTwo

theorem idem_alg {T : Type} [CommRing T] (p U R w w' : T) (hU : p * U = U)
    (hR : R * R - (w + w') * R + w * w' * p = 0) (hδ : (w + w') * U - 2 * (U * R) = p) :
    (U * w - U * R) * (U * w - U * R) = U * w - U * R ∧
      (U * w - U * R) * (U * w' - U * R) = 0 ∧
      (U * w - U * R) + (U * w' - U * R) = p := by
  have h2 : (U * w - U * R) * (U * w' - U * R) = 0 := by
    linear_combination U * U * hR - w * w' * U * hU
  refine ⟨?_, h2, by linear_combination hδ⟩
  linear_combination (U * w - U * R) * hδ - h2 + (w - R) * hU

theorem idem_tensor {F A E K : Type} [Field F] [CommRing A] [Algebra F A] [CommRing E] [Algebra F E]
    [CommRing K] [Algebra F K] (φ : K →ₙ+* A)
    (hφ : ∀ (t : F) (y : K), φ (algebraMap F K t * y) = algebraMap F A t * φ y)
    (c : A ⊗[F] E →+* A ⊗[F] E) (a b : E) (t n : F) (r u : K)
    (hc1 : ∀ x : A, c (x ⊗ₜ 1) = x ⊗ₜ 1) (hca : ∀ x : A, c (x ⊗ₜ a) = x ⊗ₜ b)
    (ht : algebraMap F E t = a + b) (hn : algebraMap F E n = a * b)
    (hr : r * r - algebraMap F K t * r + algebraMap F K n = 0) (hu : u * (algebraMap F K t - 2 * r) = 1)
    (e : A ⊗[F] E) (he : e = φ u ⊗ₜ a + φ (-(u * r)) ⊗ₜ 1) :
    e * e = e ∧ e * c e = 0 ∧ e + c e = algebraMap A (A ⊗[F] E) (φ 1) := by
  let j : A →+* A ⊗[F] E := algebraMap A _
  let k : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E)
  have hjk : ∀ a x, a ⊗ₜ[F] x = j a * k x := fun a x => by
    simp [j, k, Algebra.TensorProduct.tmul_mul_tmul]
  have hF : ∀ s : F, j (algebraMap F A s) = k (algebraMap F E s) := fun s => by
    have h := hjk 1 (algebraMap F E s)
    rw [tmul_algebraMap_eq, mul_one, map_one, one_mul] at h
    exact h
  have h1 : e = j (φ u) * k a - j (φ u) * j (φ r) := by
    rw [he, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  have h2 : c e = j (φ u) * k b - j (φ u) * j (φ r) := by
    rw [he, map_add, hc1, hca, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  rw [h2, h1]
  refine idem_alg (j (φ 1)) _ _ _ _ ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, one_mul]
  · have : φ r * φ r - algebraMap F A t * φ r + algebraMap F A n * φ 1 = 0 := by
      rw [← hφ, ← hφ, ← map_mul, ← map_sub, ← map_add, mul_one, hr, map_zero]
    have h := congrArg j this
    rwa [map_add, map_sub, map_mul, map_mul, map_mul, hF, hF, ht, hn, map_add, map_mul, map_zero] at h
  · have : algebraMap F A t * φ u - 2 * (φ u * φ r) = φ 1 := by
      rw [two_mul, ← hφ, ← map_mul, ← map_add, ← map_sub, ← hu]; congr 1; ring
    have h := congrArg j this
    rwa [map_sub, map_mul, map_mul, map_mul, map_ofNat, hF, ht, map_add] at h

theorem exists_root (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t n : 𝓞 F)
    (ht : t ∉ v.asIdeal) (hn : n ∈ v.asIdeal) :
    ∃ r u : v.adicCompletionIntegers F,
      r * r - algebraMap (𝓞 F) (v.adicCompletionIntegers F) t * r +
        algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = 0 ∧
      u * (algebraMap (𝓞 F) (v.adicCompletionIntegers F) t - 2 * r) = 1 := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : algebraMap (𝓞 F) (v.adicCompletionIntegers F) n ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
    exact fun h => h hn
  have hT : IsUnit (algebraMap (𝓞 F) (v.adicCompletionIntegers F) t) :=
    (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v t).2 ht
  generalize algebraMap (𝓞 F) (v.adicCompletionIntegers F) t = T at hT
  generalize algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = N at hm
  obtain ⟨r, hr, hr0⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
    (Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C N) (by monicity!) 0
    (by simpa using hm) (by simpa using hT.map _)
  rw [sub_zero] at hr0
  have hunit : IsUnit (T - 2 * r) := by
    by_contra h
    have h1 : T - 2 * r ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := h
    have h2 := Ideal.add_mem _ h1 (Ideal.mul_mem_left _ 2 hr0)
    rw [sub_add_cancel] at h2
    exact h2 hT
  obtain ⟨u, hu⟩ := hunit.exists_left_inv
  refine ⟨r, u, ?_, hu⟩
  simpa [Polynomial.IsRoot, pow_two] using hr

theorem exists_int (D : D7) (x : 𝓞 D.host.E) (hx : star (x : D.host.E) = x) :
    ∃ t : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = x ∧
      algebraMap D.host.F D.host.E (t : D.host.F) = x := by
  obtain ⟨t, ht⟩ := exists_of_star_eq D hx
  have hi : IsIntegral ℤ t :=
    (isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective).1 (ht ▸ x.2)
  exact ⟨⟨t, hi⟩, RingOfIntegers.ext ht, ht⟩

theorem exists_splitAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), GlobalTheory.UnRep.SplitPl (GlobalTheory.Member.cF D) v → ∃ e : Formalism.L2.Theta.AE D, GlobalTheory.IdemModTwo.SplitAt D v e := by
  rintro D v ⟨P, hP, hPv, a, ha, b, hb, hbP⟩
  have hb' : (b : D.host.E) = star (a : D.host.E) := hb
  obtain ⟨t, ht, ht'⟩ := exists_int D (a + b) (by
    show star ((a : D.host.E) + b) = (a : D.host.E) + b
    rw [hb', star_add, star_star, add_comm])
  obtain ⟨n, hn, hn'⟩ := exists_int D (a * b) (by
    show star ((a : D.host.E) * b) = (a : D.host.E) * b
    rw [hb', star_mul', star_star, mul_comm])
  have htv : t ∉ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap, ht]
    exact fun h => hbP ((Ideal.add_mem_iff_right P ha).1 h)
  have hnv : n ∈ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap, hn]
    exact Ideal.mul_mem_right _ _ ha
  obtain ⟨r, u, hr, hu⟩ := exists_root D.host.F v t n htv hnv
  have key := idem_tensor (placeHom D.host.F v) (fun s y => by
      refine Prod.ext (mul_zero _).symm ?_
      show singleV D.host.F v _ = algebraMap D.host.F (Af D.host.F) s * singleV D.host.F v y
      rw [singleV_mul, AlgHom.commutes])
    (cA D) (a : D.host.E) (b : D.host.E) (t : D.host.F) (n : D.host.F) (r : Fv D.host.F v) (u : Fv D.host.F v)
    (fun x => by rw [cA_tmul, star_one]) (fun x => by rw [cA_tmul, hb']) ht' hn'
    (congrArg Subtype.val hr) (congrArg Subtype.val hu) _ rfl
  exact ⟨_, key⟩

end GlobalTheory.MovedSplit

end
