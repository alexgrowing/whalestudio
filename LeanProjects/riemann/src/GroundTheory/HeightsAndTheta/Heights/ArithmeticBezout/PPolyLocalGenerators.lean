import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPolyLocalGenerators
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGeneratorsDiff
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.SmoothOfRegular
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMaximalIdealHeightFG
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module IsLocalRing

noncomputable section

theorem PolyLocalGenerators.proof : PolyLocalGenerators.Statement := by
  intro n m J hJ hdim p hp htan
  classical

  have H := exists_polyDiff_basis J p
  rw [htan] at H
  obtain ⟨q, hqJ, hli, hspan⟩ := H
  have hqp : ∀ i, eval p (q i) = 0 := fun i => hp _ (hqJ i)
  have htq : polyTangent (Set.range q) p = polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p := by
    refine polyTangent_eq_of_subset _ _ p (by rintro _ ⟨i, rfl⟩; exact hqJ i) fun f hf => ?_
    have := hspan f hf
    rwa [Set.range_comp] at this

  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval p) with hMdef
  have hevsurj : Function.Surjective (eval p : MvPolynomial (Fin n) ℂ →+* ℂ) :=
    fun c => ⟨C c, by simp⟩
  have hMmax : M.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hevsurj
  have : J.IsPrime := hJ
  let ev : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ := Ideal.Quotient.lift J (eval p) (fun x hx => hp x hx)
  set N : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := RingHom.ker ev with hNdef
  have hevsurj' : Function.Surjective ev :=
    fun c => ⟨Ideal.Quotient.mk J (C c), by simp [ev]⟩
  have hNmax : N.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hevsurj'
  have hNM : N.comap (Ideal.Quotient.mk J) = M := by
    ext x
    simp only [Ideal.mem_comap, hNdef, hMdef, RingHom.mem_ker, ev, Ideal.Quotient.lift_mk]

  let P := Localization.AtPrime M
  let S := Localization.AtPrime N
  let ψ : P →+* S := Localization.localRingHom M N (Ideal.Quotient.mk J) hNM.symm
  let _ : Algebra P S := ψ.toAlgebra
  have halg : ∀ x, algebraMap P S x = ψ x := fun _ => rfl
  have hψmk : ∀ x, ψ (algebraMap (MvPolynomial (Fin n) ℂ) P x) =
      algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S (Ideal.Quotient.mk J x) :=
    fun x => Localization.localRingHom_to_map M N (Ideal.Quotient.mk J) hNM.symm x
  have hsurj : Function.Surjective (algebraMap P S) := by
    intro z
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq N.primeCompl z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (t : MvPolynomial (Fin n) ℂ ⧸ J)
    have hyM : y ∈ M.primeCompl := by
      intro hyM'
      have hyN : y ∈ N.comap (Ideal.Quotient.mk J) := by rw [hNM]; exact hyM'
      apply t.2
      rw [← hy]
      exact hyN
    refine ⟨IsLocalization.mk' P x ⟨y, hyM⟩, ?_⟩
    rw [halg, Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hy

  have hdimS : ringKrullDim S = m := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height N S,
      NumbersDVR.MaximalIdealHeightFG.proof ℂ (MvPolynomial (Fin n) ℂ ⧸ J) N hNmax, hdim]

  let f : Fin (n - m) → P := fun i => algebraMap (MvPolynomial (Fin n) ℂ) P (q i)
  have hf : ∀ i, f i ∈ RingHom.ker (algebraMap P S) := by
    intro i
    rw [RingHom.mem_ker, halg, hψmk, Ideal.Quotient.eq_zero_iff_mem.2 (hqJ i), map_zero]
  have hmP : maximalIdeal P = M.map (algebraMap (MvPolynomial (Fin n) ℂ) P) :=
    (Localization.AtPrime.map_eq_maximalIdeal (I := M)).symm

  have hJcov : J ≤ Ideal.span (Set.range q) ⊔ M ^ 2 := fun x hx =>
    mem_span_sup_sq_of_polyDiff_mem p q hqp (hp x hx) (hspan x hx)
  obtain ⟨Cc, hCc⟩ := Submodule.exists_isCompl (Submodule.span ℂ (Set.range (polyDiff p ∘ q)))
  have hfinD : finrank ℂ (Submodule.span ℂ (Set.range (polyDiff p ∘ q))) = n - m := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hmn : m ≤ n := by
    rw [← htan]
    exact (Submodule.finrank_le _).trans (Module.finrank_fin_fun ℂ).le
  have hfinC : finrank ℂ Cc = m := by
    have := Submodule.finrank_add_eq_of_isCompl hCc
    rw [hfinD, Module.finrank_fin_fun] at this
    omega
  let c := Module.finBasisOfFinrankEq ℂ Cc hfinC
  let y : Fin m → MvPolynomial (Fin n) ℂ := fun k => tanLinPoly p (c k)
  have hMcov : M ≤ Ideal.span (Set.range (Sum.elim q y)) ⊔ M ^ 2 := by
    intro x hx
    refine mem_span_sup_sq_of_polyDiff_mem p (Sum.elim q y) ?_ (RingHom.mem_ker.1 hx) ?_
    · rintro (i | k)
      · exact hqp i
      · exact eval_tanLinPoly p _
    · have htop : Submodule.span ℂ (Set.range (polyDiff p ∘ Sum.elim q y)) = ⊤ := by
        rw [eq_top_iff, ← hCc.sup_eq_top]
        apply sup_le
        · apply Submodule.span_mono
          rintro _ ⟨i, rfl⟩
          exact ⟨Sum.inl i, rfl⟩
        · intro v hv
          have hCspan : Cc = Submodule.span ℂ (Set.range (Cc.subtype ∘ c)) := by
            rw [Set.range_comp, Submodule.span_image, c.span_eq, Submodule.map_subtype_top]
          rw [hCspan] at hv
          refine Submodule.span_mono ?_ hv
          rintro _ ⟨k, rfl⟩
          exact ⟨Sum.inr k, by simp [y, polyDiff_tanLinPoly]⟩
      rw [htop]
      exact Submodule.mem_top

  let φ : MvPolynomial (Fin n) ℂ →+* S :=
    (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S).comp (Ideal.Quotient.mk J)
  have hmS : maximalIdeal S = M.map φ := by
    calc maximalIdeal S = N.map (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S) :=
          (Localization.AtPrime.map_eq_maximalIdeal (I := N)).symm
      _ = (M.map (Ideal.Quotient.mk J)).map (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S) := by
          rw [← hNM, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
      _ = M.map φ := Ideal.map_map _ _
  have hφq : ∀ i, φ (q i) = 0 := by
    intro i
    simp [φ, Ideal.Quotient.eq_zero_iff_mem.2 (hqJ i)]
  have hS_le : maximalIdeal S ≤ Ideal.span (Set.range (φ ∘ y)) := by
    refine maximalIdeal_le_span_of_le_sup_sq (R := S) (Set.range (φ ∘ y)) ?_
    rw [hmS]
    have h1 := Ideal.map_mono (f := φ) hMcov
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow] at h1
    refine h1.trans (sup_le_sup ?_ ?_)
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨_, ⟨i | k, rfl⟩, rfl⟩
      · simp [hφq]
      · exact Ideal.subset_span ⟨k, rfl⟩
    · exact le_rfl
  have hμ : (maximalIdeal S).spanFinrank ≤ m := by
    have heq : maximalIdeal S = Ideal.span (Set.range (φ ∘ y)) := by
      refine le_antisymm hS_le (Ideal.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, hmS]
      exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 (eval_tanLinPoly p _))
    rw [heq]
    calc (Ideal.span (Set.range (φ ∘ y))).spanFinrank ≤ (Set.range (φ ∘ y)).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ ≤ (Set.univ : Set (Fin m)).ncard := by
          rw [← Set.image_univ]
          exact Set.ncard_image_le Set.finite_univ
      _ = m := by simp [Set.ncard_univ]

  have hcov : RingHom.ker (algebraMap P S) ≤ Ideal.span (Set.range f) ⊔ maximalIdeal P ^ 2 := by
    intro z hz
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M.primeCompl z
    have hx0 : algebraMap P S (algebraMap (MvPolynomial (Fin n) ℂ) P x) = 0 := by
      rw [← IsLocalization.mk'_spec P x s, map_mul, RingHom.mem_ker.1 hz, zero_mul]
    rw [halg, hψmk] at hx0
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff N.primeCompl S _).1 hx0
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (t : MvPolynomial (Fin n) ℂ ⧸ J)
    have hwx : w * x ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hw, ht]
    have hwJ : w ∉ J := by
      intro hwJ
      apply t.2
      rw [← hw, Ideal.Quotient.eq_zero_iff_mem.2 hwJ]
      exact zero_mem _
    have hxJ : x ∈ J := (hJ.mem_or_mem hwx).resolve_left hwJ
    have hx' : algebraMap (MvPolynomial (Fin n) ℂ) P x ∈
        Ideal.span (Set.range f) ⊔ maximalIdeal P ^ 2 := by
      have h1 := Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) ℂ) P) (hJcov hxJ)
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, ← hmP, ← Set.range_comp] at h1
      exact h1
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hx'

  have hker := GroundTheory.Arith.Jacobian.ker_le_span_of_spanFinrank_le (P := P) (S := S) hsurj f hf hcov
    m hμ hdimS.ge

  have hloc : ∀ x ∈ J, ∃ s ∈ M.primeCompl, s * x ∈ Ideal.span (Set.range q) := by
    intro x hx
    have hx1 : algebraMap (MvPolynomial (Fin n) ℂ) P x ∈ Ideal.span (Set.range f) := by
      apply hker
      rw [RingHom.mem_ker, halg, hψmk, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    have hspanf : Ideal.span (Set.range f) =
        (Ideal.span (Set.range q)).map (algebraMap (MvPolynomial (Fin n) ℂ) P) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    rw [hspanf] at hx1
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff M.primeCompl P).1 hx1
    rw [← map_mul, IsLocalization.eq_iff_exists M.primeCompl P] at e
    obtain ⟨c', hc'⟩ := e
    refine ⟨c' * s, M.primeCompl.mul_mem c'.2 hs, ?_⟩
    have e2 : (c' : MvPolynomial (Fin n) ℂ) * s * x = c' * a := by
      rw [← hc']
      ring
    rw [e2]
    exact Ideal.mul_mem_left _ _ ha
  choose! σ hσM hσ using hloc
  obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing J
  have hsJ : ∀ x ∈ s, x ∈ J := fun x hx => by
    rw [← hs]
    exact Submodule.subset_span hx
  refine ⟨q, ∏ x ∈ s, σ x, hqJ, ?_, ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun x hx h0 => ?_
    exact hσM x (hsJ x hx) (RingHom.mem_ker.2 h0)
  · rw [htq, htan]
  · intro r hr
    have hle : J ≤ Submodule.comap (LinearMap.mulLeft (MvPolynomial (Fin n) ℂ) (∏ x ∈ s, σ x))
        (Ideal.span (Set.range q)) := by
      rw [← hs]
      refine Submodule.span_le.2 fun x hx => ?_
      have hxJ := hsJ x hx
      show (∏ x ∈ s, σ x) * x ∈ Ideal.span (Set.range q)
      rw [← Finset.mul_prod_erase s σ hx,
        show σ x * (∏ y ∈ s.erase x, σ y) * x = (∏ y ∈ s.erase x, σ y) * (σ x * x) by ring]
      exact Ideal.mul_mem_left _ _ (hσ x hxJ)
    exact hle hr

end

end GroundTheory.Heights₂.Heights
