import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSpanOfWeightedHomogeneousRelationQuasiReStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedHomogenisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrLocPrincipalPrimeStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open MvPolynomial

theorem exists_weightedMonomialPlace : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (r : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
    IsNoetherianRing Q → Ideal.span (Set.range z) = IsLocalRing.maximalIdeal Q →
    IsQuasiRegularSeq Q z → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
    ∃ (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
      (∀ i, (u i : L) * (z 0 : L) ^ wt i.succ = z i.succ) ∧
      Irreducible (⟨z 0, hC _ (z 0).2⟩ : V.ring) ∧
      (∀ q ∈ IsLocalRing.maximalIdeal Q,
        (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) ∧
      (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) ∧
      ∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
        f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
          MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro r z wt hN hm hz hw0 hw
  haveI := hN
  have hz0 : (z 0 : L) ≠ 0 := by
    intro h
    have h1 : z 0 = 0 := Subtype.ext h
    have := GlobalTheory.T.coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular z wt hw hz (wt 0) (X 0) (isWeightedHomogeneous_X Q wt 0)
      (by simp [h1]) (Finsupp.single 0 1)
    rw [coeff_X, if_pos rfl, hm] at this
    exact (IsLocalRing.maximalIdeal.isMaximal Q).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  set u : Fin r → L := fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ with hu
  have key0 : ∀ P : MvPolynomial (Fin r) Q, eval₂ Q.subtype u P = 0 →
      ∀ α, P.coeff α ∈ IsLocalRing.maximalIdeal Q := by
    intro P hP α
    obtain ⟨N, F, hF, hFe, hc⟩ := GlobalTheory.T.exists_weightedHomogeneous_homogenisation Q r z wt hw0 hz0 P
    obtain ⟨β, hβ⟩ := hc α
    rw [← hβ, ← hm]
    refine GlobalTheory.T.coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular z wt hw hz N F hF ?_ β
    apply Subtype.ext
    rw [hFe, hP, mul_zero]
    rfl
  set e : MvPolynomial (Fin r) Q →+* L := eval₂Hom Q.subtype u with he
  set A : Subring L := e.range with hA
  set eA : MvPolynomial (Fin r) Q →+* A := e.rangeRestrict with heA
  have heA_surj : Function.Surjective eA := e.rangeRestrict_surjective
  have heA_val : ∀ P, ((eA P : A) : L) = e P := fun P => rfl
  have hQA : ∀ q ∈ Q, q ∈ A := fun q hq => ⟨C ⟨q, hq⟩, by simp [he]⟩
  have huA : ∀ i, u i ∈ A := fun i => ⟨X i, by simp [he]⟩
  let t : A := ⟨z 0, hQA _ (z 0).2⟩
  have hzA : ∀ j, ∃ a : A, ((z j : Q) : L) = (z 0 : L) * a := by
    intro j
    refine Fin.cases ⟨1, by simp⟩ (fun i => ?_) j
    refine ⟨⟨(z 0 : L) ^ (wt i.succ - 1) * u i, A.mul_mem (A.pow_mem (hQA _ (z 0).2) _) (huA i)⟩, ?_⟩
    show ((z i.succ : Q) : L) = (z 0 : L) * ((z 0 : L) ^ (wt i.succ - 1) * ((z i.succ : L) / (z 0 : L) ^ wt i.succ))
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (hw i.succ), mul_div_cancel₀ _ (pow_ne_zero _ hz0)]
  have hmA : Ideal.map (eA.comp C) (IsLocalRing.maximalIdeal Q) ≤ Ideal.span {t} := by
    rw [Ideal.map_le_iff_le_comap, ← hm, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨a, ha⟩ := hzA j
    show eA (C (z j)) ∈ Ideal.span {t}
    rw [Ideal.mem_span_singleton']
    exact ⟨a, Subtype.ext (by rw [heA_val]; simp [he, ha, mul_comm, t])⟩
  have hspan : Ideal.span {t} = Ideal.map eA (Ideal.map C (IsLocalRing.maximalIdeal Q)) := by
    rw [Ideal.map_map]
    refine le_antisymm ?_ hmA
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have : t = (eA.comp C) (z 0) := Subtype.ext (by rw [RingHom.comp_apply, heA_val]; simp [he, t])
    rw [SetLike.mem_coe, this]
    exact Ideal.mem_map_of_mem _ (by rw [← hm]; exact Ideal.subset_span ⟨0, rfl⟩)
  have hker : RingHom.ker eA ≤ Ideal.map C (IsLocalRing.maximalIdeal Q) := by
    intro P hP
    rw [MvPolynomial.mem_map_C_iff]
    refine key0 P ?_
    have := congrArg Subtype.val ((RingHom.mem_ker).mp hP)
    simpa [heA_val, he] using this
  have hprimeC : (Ideal.map (C : Q →+* MvPolynomial (Fin r) Q) (IsLocalRing.maximalIdeal Q)).IsPrime := by
    have := MvPolynomial.ker_map (σ := Fin r) (IsLocalRing.residue Q)
    rw [IsLocalRing.ker_residue] at this
    rw [← this]
    exact RingHom.ker_isPrime _
  have hprime : (Ideal.span {t}).IsPrime := by
    rw [hspan]
    exact Ideal.map_isPrime_of_surjective heA_surj hker
  have key1 : ∀ P : MvPolynomial (Fin r) Q, eA P ∈ Ideal.span {t} →
      P ∈ Ideal.map C (IsLocalRing.maximalIdeal Q) := by
    intro P hP
    rw [hspan] at hP
    obtain ⟨x, hx, hxP⟩ := (Ideal.mem_map_iff_of_surjective eA heA_surj).mp hP
    have : P - x ∈ RingHom.ker eA := by rw [RingHom.mem_ker, map_sub, hxP, sub_self]
    simpa using Ideal.add_mem _ (hker this) hx
  have hNA : IsNoetherianRing A := isNoetherianRing_of_surjective _ _ eA heA_surj
  have hfracA : ∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a := by
    intro f
    obtain ⟨a, ha, b, hb, hb0, hab⟩ := hQ.frac f
    exact ⟨a, hQA a ha, b, hQA b hb, hb0, hab⟩
  obtain ⟨V, hAV, hdvr, hirr, hunit, hfrV, hess⟩ :=
    GlobalTheory.T.isDVR_of_principal_prime_localization A t hNA hz0 hprime hfracA
  have hQAf : (Q.subtype.codRestrict A fun q => hQA _ q.2).FiniteType := by
    have h1 : (Q.subtype.codRestrict A fun q => hQA _ q.2) = eA.comp C := by
      ext q; simp [heA_val, he]
    rw [h1]
    exact RingHom.FiniteType.comp_surjective (RingHom.finiteType_algebraMap.mpr inferInstance) heA_surj
  have hconst : ∀ a, c a ∈ V := fun a => hAV _ (hQA _ (hQ.const_mem a))
  have hessV : (c.codRestrict V hconst).EssFiniteType := by
    have h := (hQ.essFiniteType.comp hQAf.essFiniteType).comp hess
    exact h
  let P0 : Place c := ⟨V, hconst, hdvr, hessV⟩
  have hC : P0.Contains Q := fun f hf => hAV _ (hQA _ hf)
  let uV : Fin r → P0.ring := fun i => ⟨u i, hAV _ (huA i)⟩
  have hev : ∀ P : MvPolynomial (Fin r) Q,
      ((MvPolynomial.eval₂ (Q.subtype.codRestrict P0.ring fun q => hC _ q.2) uV P : P0.ring) : L) =
        e P := by
    intro P
    exact MvPolynomial.eval₂_comp_left (P0.ring.subtype)
      (Q.subtype.codRestrict P0.ring fun q => hC _ q.2) uV P
  refine ⟨P0, hC, uV, fun i => ?_, ?_, fun q hq => ?_, fun P hP => ?_, fun f => ?_⟩
  · exact div_mul_cancel₀ _ (pow_ne_zero _ hz0)
  · exact hirr
  · obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton').mp (hmA (Ideal.mem_map_of_mem _ hq))
    have hmt : (⟨(t : L), hAV _ t.2⟩ : V) ∈ IsLocalRing.maximalIdeal V :=
      (IsLocalRing.mem_maximalIdeal _).mpr hirr.not_isUnit
    have : (⟨(q : L), hC _ q.2⟩ : P0.ring) = ⟨(a : L), hAV _ a.2⟩ * ⟨(t : L), hAV _ t.2⟩ :=
      Subtype.ext (by have := congrArg Subtype.val ha; simpa [heA_val, he] using this.symm)
    rw [this]
    exact Ideal.mul_mem_left _ _ hmt
  · have hs : eA P ∉ Ideal.span {t} := fun h => by
      obtain ⟨α, hα⟩ := hP
      exact hα ((MvPolynomial.mem_map_C_iff.mp (key1 P h)) α)
    have := hunit _ hs
    convert this using 1
    exact Subtype.ext (hev P)
  · obtain ⟨a, s, hs, hfs⟩ := hfrV f
    obtain ⟨P, rfl⟩ := heA_surj a
    obtain ⟨R, rfl⟩ := heA_surj s
    refine ⟨P, R, ?_, Subtype.ext ?_⟩
    · convert hunit _ hs using 1
      exact Subtype.ext (hev R)
    · calc ((f * MvPolynomial.eval₂ (Q.subtype.codRestrict P0.ring fun q => hC _ q.2) uV R : P0.ring) : L)
          = (f : L) * e R := by rw [← hev R]; rfl
        _ = e P := hfs
        _ = _ := (hev P).symm

end GlobalTheory
