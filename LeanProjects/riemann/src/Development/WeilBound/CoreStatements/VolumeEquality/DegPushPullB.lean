import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.NumericalSegre

noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G MvPolynomial
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

section

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

theorem aeval_scale [Fintype K] [DecidableEq K] {L : Type} [CommRing L] [Algebra k L] (s : K → L) (w : (Σ b, ι b) → L)
    {f : MRing ι k} {b : K → ℕ} (hf : IsMultiHomog f b) :
    aeval (fun p => s p.1 * w p) f = (∏ x, s x ^ b x) * aeval w f := by
  have key : ∀ m ∈ f.support, (m.prod fun p e => s p.1 ^ e) = ∏ x, s x ^ b x := by
    intro m hm
    have hw : Finsupp.weight (blockWeight ι) m = b := hf (mem_support_iff.mp hm)
    rw [← hw]
    simp only [Finsupp.weight_apply, Finsupp.sum, blockWeight]
    rw [Finsupp.prod]
    simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow_eq_pow_sum]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Finset.prod_eq_single p.1]
    · simp
    · intro x _ hx
      simp [Pi.single_apply, hx]
    · intro h
      exact absurd (Finset.mem_univ _) h
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul, key m hm]
  ring

theorem pointIdeal_comp (y : (Σ b, ι' b) → Ω) (κ : K → K') (hκ : Function.Injective κ) (v : (Σ b, ι b) → Σ b, ι' b)
    (hv : ∀ p, (v p).1 = κ p.1) : pointIdeal k (y ∘ v) = (pointIdeal k y).comap (rename v : MRing ι k →ₐ[k] MRing ι' k) := by
  have key : ∀ f : MRing ι k, pointConeMap k y (rename v f) = rename κ (pointConeMap k (y ∘ v) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [pointConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
      rw [map_mul, map_mul, hp, map_mul, map_mul]
      congr 1
      simp [pointConeMap, hv]
  ext f
  simp only [pointIdeal, Ideal.mem_comap, RingHom.mem_ker]
  rw [show (rename v : MRing ι k →ₐ[k] MRing ι' k) f = rename v f from rfl, key]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply MvPolynomial.rename_injective _ hκ
    rw [h, map_zero]

private theorem aeval_div_mem_fnField_of_multiHomog {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} {ι : K → Type}
    [Fintype K] [DecidableEq K] (z : (Σ b, ι b) → Ω) (hz : ∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) {f g : MRing ι k} {b : K → ℕ}
    (hf : IsMultiHomog f b) (hg : IsMultiHomog g b) : aeval z f / aeval z g ∈ fnField k z := by
  choose i hi using hz
  let s : K → Ω := fun x => z ⟨x, i x⟩
  let w : (Σ b, ι b) → Ω := fun p => z p / s p.1
  have hwmem : ∀ p, w p ∈ fnField k z := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, i p.1⟩, rfl, rfl⟩
  have hmem : ∀ h : MRing ι k, aeval w h ∈ fnField k z := by
    intro h
    induction h using MvPolynomial.induction_on with
    | C a =>
      rw [aeval_C]
      exact IntermediateField.algebraMap_mem _ a
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p n hp =>
      rw [map_mul, aeval_X]
      exact mul_mem hp (hwmem n)
  have hzw : (fun p => s p.1 * w p) = z := by
    funext p
    have := hi p.1
    simp only [s, w]
    field_simp
  have e : ∀ h : MRing ι k, IsMultiHomog h b → aeval z h = (∏ x, s x ^ b x) * aeval w h := by
    intro h hh
    rw [← aeval_scale s w hh, hzw]
  have hP : (∏ x, s x ^ b x) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => pow_ne_zero _ (hi x)
  rw [e f hf, e g hg, mul_div_mul_left _ _ hP]
  exact div_mem (hmem f) (hmem g)

theorem map_homFrac [Fintype K] [DecidableEq K] {L : Type} [Field L] [Algebra k L] (P : Ideal (MRing ι k)) [P.IsPrime]
    (φ : FractionRing (MRing ι k ⧸ P) →ₐ[k] L) (c : Ω →ₐ[k] L) (t : K → L) (z : (Σ b, ι b) → Ω)
    (hz : ∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) (ht : ∀ b, t b ≠ 0)
    (hφ : ∀ p, φ (algebraMap (MRing ι k ⧸ P) _ (Ideal.Quotient.mk P (X p))) = c (z p) * t p.1) :
    (homFracDegZero P).map φ = (fnField k z).map c := by
  let Ψ : MRing ι k →ₐ[k] L := φ.comp ((IsScalarTower.toAlgHom k (MRing ι k ⧸ P)
    (FractionRing (MRing ι k ⧸ P))).comp (Ideal.Quotient.mkₐ k P))
  have hΨX : ∀ p, Ψ (X p) = t p.1 * c (z p) := by
    intro p
    rw [mul_comm]
    exact hφ p
  have hΨ : ∀ {f : MRing ι k} {b : K → ℕ}, IsMultiHomog f b → Ψ f = (∏ x, t x ^ b x) * c (aeval z f) := by
    intro f b hf
    rw [MvPolynomial.aeval_unique Ψ]
    have hfun : (⇑Ψ ∘ X) = fun p => t p.1 * c (z p) := funext hΨX
    rw [hfun, aeval_scale t (fun p => c (z p)) hf]
    congr 1
    show _ = (c.comp (aeval z)) f
    rw [MvPolynomial.comp_aeval]
  have hT : ∀ b : K → ℕ, (∏ x, t x ^ b x) ≠ 0 := fun b =>
    Finset.prod_ne_zero_iff.mpr fun x _ => pow_ne_zero _ (ht x)
  apply le_antisymm
  · unfold homFracDegZero
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, ⟨b, f, g, hf, hg, hgP, rfl⟩, rfl⟩
    rw [map_div₀]
    change Ψ f / Ψ g ∈ _
    rw [hΨ hf, hΨ hg, mul_div_mul_left _ _ (hT b), ← map_div₀]
    exact ⟨_, aeval_div_mem_fnField_of_multiHomog z hz hf hg, rfl⟩
  · unfold fnField
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨u, ⟨p, q, hpq, rfl⟩, rfl⟩
    by_cases hq : z q = 0
    · rw [hq, div_zero, map_zero]
      exact zero_mem _
    · have hXq : X q ∉ P := by
        intro hm
        have h0 : Ψ (X q) = 0 := by
          simp [Ψ, Ideal.Quotient.eq_zero_iff_mem.mpr hm]
        rw [hΨX] at h0
        exact mul_ne_zero (ht q.1) ((map_ne_zero c).mpr hq) h0
      refine ⟨algebraMap _ (FractionRing (MRing ι k ⧸ P)) (Ideal.Quotient.mk P (X p)) /
        algebraMap _ (FractionRing (MRing ι k ⧸ P)) (Ideal.Quotient.mk P (X q)), ?_, ?_⟩
      · apply IntermediateField.subset_adjoin
        refine ⟨Pi.single q.1 1, X p, X q, ?_, ?_, hXq, rfl⟩
        · have h1 := isWeightedHomogeneous_X k (blockWeight ι) p
          simp only [blockWeight, hpq] at h1
          exact h1
        · exact isWeightedHomogeneous_X k (blockWeight ι) q
      · rw [map_div₀]
        change Ψ (X p) / Ψ (X q) = _
        rw [hΨX, hΨX, hpq, mul_div_mul_left _ _ (ht q.1), map_div₀]

theorem fnField_comp_le (y : (Σ b, ι' b) → Ω) (κ : K → K') (v : (Σ b, ι b) → Σ b, ι' b) (hv : ∀ p, (v p).1 = κ p.1) :
    fnField k (y ∘ v) ≤ fnField k y := by
  unfold fnField
  apply IntermediateField.adjoin_le_iff.mpr
  rintro t ⟨p, q, hpq, rfl⟩
  apply IntermediateField.subset_adjoin
  exact ⟨v p, v q, by rw [hv, hv, hpq], rfl⟩

theorem relDeg_pointIdeal [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] (j : K ↪ K') (y : (Σ b, ι' b) → Ω)
    (hy : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) [(pointIdeal k y).IsPrime] :
    relDeg j (pointIdeal k y) = IntermediateField.relfinrank (fnField k (y ∘ blockIncl j ι')) (fnField k y) := by
  let P' := pointIdeal k y
  let M := MvPolynomial K' Ω
  let L := FractionRing M
  let q : (MRing ι' k ⧸ P') →ₐ[k] M := Ideal.kerLiftAlg (pointConeMap k y)
  have hq : Function.Injective q := Ideal.kerLiftAlg_injective _
  let g : (MRing ι' k ⧸ P') →ₐ[k] L := (IsScalarTower.toAlgHom k M L).comp q
  have hg : Function.Injective g := (IsFractionRing.injective M L).comp hq
  let φ : FractionRing (MRing ι' k ⧸ P') →ₐ[k] L := IsFractionRing.liftAlgHom hg
  let c : Ω →ₐ[k] L := (IsScalarTower.toAlgHom k M L).comp (IsScalarTower.toAlgHom k Ω M)
  let t : K' → L := fun b => algebraMap M L (X b)
  have ht : ∀ b, t b ≠ 0 := by
    intro b h
    apply X_ne_zero (R := Ω) b
    apply IsFractionRing.injective M L
    rw [map_zero]
    exact h
  have hφ : ∀ p, φ (algebraMap (MRing ι' k ⧸ P') _ (Ideal.Quotient.mk P' (X p))) = c (y p) * t p.1 := by
    intro p
    simp only [φ, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    show algebraMap M L (q (Ideal.Quotient.mk P' (X p))) = _
    rw [show q (Ideal.Quotient.mk P' (X p)) = pointConeMap k y (X p) from Ideal.kerLiftAlg_mk _ _]
    simp only [pointConeMap, aeval_X, map_mul]
    rfl
  have h1 := map_homFrac P' φ c t y hy ht hφ
  let φ₂ := φ.comp (contractFracMap j P')
  have hφ₂ : ∀ p, φ₂ (algebraMap _ (FractionRing (MRing (fun b => ι' (j b)) k ⧸ contractPrime j P'))
      (Ideal.Quotient.mk (contractPrime j P') (X p))) = c ((y ∘ blockIncl j ι') p) * (t ∘ j) p.1 := by
    intro p
    have hc : contractQuot j P' (Ideal.Quotient.mk (contractPrime j P') (X p)) =
        Ideal.Quotient.mk P' (X (blockIncl j ι' p)) := by
      show Ideal.Quotient.mk P' (rename (blockIncl j ι') (X p)) = _
      rw [rename_X]
    have hcf : contractFracMap j P' (algebraMap _ (FractionRing (MRing (fun b => ι' (j b)) k ⧸ contractPrime j P'))
        (Ideal.Quotient.mk (contractPrime j P') (X p))) =
        algebraMap _ (FractionRing (MRing ι' k ⧸ P')) (contractQuot j P' (Ideal.Quotient.mk (contractPrime j P') (X p))) := by
      unfold contractFracMap
      erw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
      rfl
    simp only [φ₂, AlgHom.comp_apply]
    rw [hcf, hc, hφ]
    rfl
  have h2 := map_homFrac (contractPrime j P') φ₂ c (t ∘ j) (y ∘ blockIncl j ι') (fun b => hy (j b))
    (fun b => ht (j b)) hφ₂
  unfold relDeg
  rw [← IntermediateField.relfinrank_map_map _ _ φ, IntermediateField.map_map, h1]
  erw [h2]
  exact IntermediateField.relfinrank_map_map _ _ c

end

theorem numPull : NumPull := by
  intro k _ Ω _ _ K _ ι _ K' _ ι' _ κ v y d a hbm hy hyv
  classical
  obtain ⟨hκ, hvinj, hv, hvs⟩ := hbm
  let j : K ↪ K' := ⟨κ, hκ⟩
  let τf : (Σ b, ι b) → Σ b : K, ι' (j b) := fun p => ⟨p.1, cast (congrArg ι' (hv p)) (v p).2⟩
  have hτv : ∀ p, blockIncl j ι' (τf p) = v p := by
    intro p
    exact Sigma.ext (hv p).symm (cast_heq _ _)
  have hbinj : Function.Injective (blockIncl j ι') := by
    rintro ⟨b1, i1⟩ ⟨b2, i2⟩ h
    simp only [blockIncl, Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    have hb : b1 = b2 := hκ h1
    subst hb
    simp [eq_of_heq h2]
  have hτinj : Function.Injective τf := fun p q h => hvinj (by rw [← hτv, ← hτv, h])
  have hτsurj : Function.Surjective τf := by
    rintro ⟨b, i⟩
    obtain ⟨p, hp⟩ := hvs ⟨κ b, i⟩ ⟨b, rfl⟩
    exact ⟨p, hbinj (by rw [hτv, hp]; rfl)⟩
  let τ := Equiv.ofBijective τf ⟨hτinj, hτsurj⟩
  let z := y ∘ blockIncl j ι'
  have hyvz : y ∘ v = z ∘ τ := by
    funext p
    show y (v p) = y (blockIncl j ι' (τf p))
    rw [hτv]
  have hF1 : fnField k (y ∘ v) = fnField k z := by
    rw [hyvz]
    apply le_antisymm
    · exact fnField_comp_le z id τ (fun p => rfl)
    · have hz : z = (z ∘ τ) ∘ τ.symm := by
        funext q
        simp
      conv_lhs => rw [hz]
      exact fnField_comp_le (z ∘ τ) id τ.symm (fun q => congrArg Sigma.fst (τ.apply_symm_apply q))
  have hinum : inum k (y ∘ v) a = inum k z a := by
    have hP : pointIdeal k (z ∘ τ) =
        (pointIdeal k z).comap (rename τ : MRing ι k →ₐ[k] MRing (fun b => ι' (j b)) k) :=
      pointIdeal_comp z id Function.injective_id τ (fun p => rfl)
    rw [hyvz]
    unfold inum
    rw [hP, FieldNumbers.RenameIntNum.full k K K ι (fun b => ι' (j b)) (Equiv.refl K) τ (fun p => rfl)]
    rfl
  have hzPt : IsPt k z d := by
    obtain ⟨h1, h2, h3⟩ := hyv
    refine ⟨fun b => ?_, ?_, h3⟩
    · obtain ⟨i, hi⟩ := h1 b
      refine ⟨(τf ⟨b, i⟩).2, fun h0 => hi ?_⟩
      show y (v ⟨b, i⟩) = 0
      rw [← hτv]
      exact h0
    · rw [← hF1]
      exact h2
  obtain ⟨hP'm, hrel, -⟩ := ptDim k Ω K' ι' y d hy
  obtain ⟨hPzm, hrelz, -⟩ := ptDim k Ω K (fun b => ι' (j b)) z d hzPt
  haveI : (pointIdeal k y).IsPrime := hP'm.isPrime
  have hcon : contractPrime j (pointIdeal k y) = pointIdeal k z :=
    (pointIdeal_comp y κ hκ (blockIncl j ι') (fun p => rfl)).symm
  have hPF := (ProjectionFormulaDegree.of_divPushForward
    (DivPushForward.proof ContractRelDimLe.proof DivPushForwardLocalZero)
    k K K' j ι' (pointIdeal k y) hP'm d hrel (by rw [hcon]; exact hrelz) a).2
  rw [hcon] at hPF
  have hrd := relDeg_pointIdeal (k := k) j y hy.1
  have hle : fnField k z ≤ fnField k y := fnField_comp_le y κ (blockIncl j ι') (fun p => rfl)
  haveI : FiniteDimensional (fnField k y) Ω := hy.2.1
  unfold num
  rw [hinum, hF1, ← IntermediateField.relfinrank_mul_finrank_top hle]
  unfold inum
  change _ * intNum k (pointIdeal k y) (fun i => pullDeg j (a i)) = _
  rw [hPF, hrd]
  push_cast
  ring

end SheetDecomposition
