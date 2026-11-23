import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsNormInvSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueIsStandardAdeleCharUnramifiedCMBaseStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndexStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscrStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEqStandardAdeleCharRationalDilateStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInvStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

noncomputable section

namespace GlobalTheory.LocalDensityProduct

variable {F : Type} [Field F] [NumberField F]

def colonV (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) : AddSubgroup (Fv F v) :=
  (intV F v).comap (AddMonoidHom.mulRight c)

theorem mem_colonV {v : HeightOneSpectrum (𝓞 F)} {c t : Fv F v} :
    t ∈ colonV v c ↔ t * c ∈ v.adicCompletionIntegers F := Iff.rfl

theorem mem_intV {v : HeightOneSpectrum (𝓞 F)} {t : Fv F v} :
    t ∈ intV F v ↔ t ∈ v.adicCompletionIntegers F := Iff.rfl

theorem card_quot_span (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletionIntegers F)
    (hc : (c : Fv F v) ≠ 0) :
    (Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {c}) : ℝ) = ‖(c : Fv F v)‖⁻¹ := by
  have hv : Valued.v (c : Fv F v) ≠ 0 := by simpa using hc
  have h1 : Valued.v (c : Fv F v) ≤ 1 := c.2
  have hl : WithZero.log (Valued.v (c : Fv F v)) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hv, WithZero.exp_zero]; exact h1
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (Valued.v (c : Fv F v)) = -(e : ℤ) :=
    ⟨(-WithZero.log (Valued.v (c : Fv F v))).toNat, by omega⟩
  have he' : Valued.v (c : Fv F v) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, WithZero.exp_log hv]
  rw [(GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 c e he',
    FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
  have : Multiplicative.toAdd (WithZero.unzero hv) = -(e : ℤ) := by
    rw [← he]
    conv_rhs => rw [← WithZero.coe_unzero hv]
    rfl
  rw [this]
  simp

theorem relIndex_colonV_inv (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletionIntegers F)
    (hc : (c : Fv F v) ≠ 0) :
    ((colonV v (c : Fv F v)⁻¹).relIndex (intV F v) : ℝ) = ‖(c : Fv F v)‖⁻¹ := by
  let f : v.adicCompletionIntegers F →+ Fv F v :=
    ((v.adicCompletionIntegers F).subtype : _ →+* _).toAddMonoidHom
  have hr : f.range = intV F v := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hcm : (colonV v (c : Fv F v)⁻¹).comap f = (Ideal.span {c}).toAddSubgroup := by
    ext x
    change (x : Fv F v) * (c : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F ↔ x ∈ Ideal.span {c}
    rw [Ideal.mem_span_singleton']
    constructor
    · intro h
      exact ⟨⟨_, h⟩, Subtype.ext (inv_mul_cancel_right₀ hc _)⟩
    · rintro ⟨a, rfl⟩
      change (a : Fv F v) * c * (c : Fv F v)⁻¹ ∈ _
      rw [mul_inv_cancel_right₀ hc]
      exact a.2
  rw [← hr, ← AddSubgroup.index_comap, hcm, ← card_quot_span v c hc]
  rfl

theorem relIndex_intV_colonV (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) (hc : c ≠ 0) :
    (intV F v).relIndex (colonV v c) = (colonV v c⁻¹).relIndex (intV F v) := by
  have h1 : intV F v = (colonV v c⁻¹).comap (AddMonoidHom.mulRight c) := by
    ext x
    change _ ↔ x * c * c⁻¹ ∈ v.adicCompletionIntegers F
    rw [mul_inv_cancel_right₀ hc]
    rfl
  have hs : Function.Surjective (AddMonoidHom.mulRight c) := fun y =>
    ⟨y * c⁻¹, inv_mul_cancel_right₀ hc y⟩
  conv_lhs => rw [h1]
  rw [AddSubgroup.relIndex_comap, colonV, colonV, AddSubgroup.map_comap_eq_self_of_surjective hs]

theorem index_colonV (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) (hc : c ≠ 0) :
    ((intV F v).relIndex (colonV v c) ≠ 0 ∧ (colonV v c).relIndex (intV F v) ≠ 0) ∧
      ((intV F v).relIndex (colonV v c) : ℝ) / ((colonV v c).relIndex (intV F v) : ℝ) = ‖c‖⁻¹ := by
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  rcases (v.adicCompletionIntegers F).mem_or_inv_mem c with h | h
  · have e1 : ((intV F v).relIndex (colonV v c) : ℝ) = ‖c‖⁻¹ := by
      rw [relIndex_intV_colonV v c hc]
      exact relIndex_colonV_inv v ⟨c, h⟩ hc
    have e2 : (colonV v c).relIndex (intV F v) = 1 :=
      AddSubgroup.relIndex_eq_one.2 fun x hx => mem_colonV.2 (mul_mem (mem_intV.1 hx) h)
    refine ⟨⟨fun h0 => ?_, by rw [e2]; exact one_ne_zero⟩, by rw [e1, e2]; simp⟩
    rw [h0, Nat.cast_zero] at e1
    exact inv_ne_zero hn e1.symm
  · have e1 : ((colonV v c).relIndex (intV F v) : ℝ) = ‖c‖ := by
      have := relIndex_colonV_inv v ⟨c⁻¹, h⟩ (inv_ne_zero hc)
      simpa using this
    have e2 : (intV F v).relIndex (colonV v c) = 1 :=
      AddSubgroup.relIndex_eq_one.2 fun x hx => by
        have := mul_mem (mem_colonV.1 hx) h
        rwa [mul_inv_cancel_right₀ hc] at this
    refine ⟨⟨by rw [e2]; exact one_ne_zero, fun h0 => ?_⟩, by rw [e1, e2]; simp⟩
    rw [h0, Nat.cast_zero] at e1
    exact hn e1.symm

theorem exists_generator_differentV (v : HeightOneSpectrum (𝓞 F)) :
    ∃ δ : v.adicCompletionIntegers F, (δ : Fv F v) ≠ 0 ∧ differentV F v = Ideal.span {δ} := by
  obtain ⟨δ, hδ⟩ := (IsPrincipalIdealRing.principal (differentV F v)).principal
  refine ⟨δ, fun h => ?_, hδ⟩
  have h0 : δ = 0 := Subtype.ext h
  rw [h0, Submodule.span_zero_singleton, differentV, Ideal.map_eq_bot_iff_of_injective] at hδ
  · exact differentIdeal_ne_bot hδ
  · intro x y hxy
    have := congrArg (fun z : v.adicCompletionIntegers F => (z : Fv F v)) hxy
    simp only [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply] at this
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F ((algebraMap F (Fv F v)).injective this)

theorem psiV_of_eq {ψ₀ ψ : AddChar (AF F) ℂ} {a : F}
    (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x)) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    psiV F ψ v t = psiV F ψ₀ v (algebraMap F (Fv F v) a * t) := by
  classical
  rw [psiV, psiV, h]
  congr 1
  refine Prod.ext (mul_zero _) ?_
  change algebraMap F (Af F) a * singleV F v t = singleV F v _
  refine DFunLike.ext _ _ fun w => ?_
  change algebraMap F (Fv F w) a * singleV F v t w = _
  by_cases hw : w = v
  · subst hw
    have e : ∀ y : Fv F w, singleV F w y w = y := fun y =>
      RestrictedProduct.single_eq_same _ w y
    rw [e, e]
  · have e : ∀ y : Fv F v, singleV F v y w = 0 := fun y =>
      RestrictedProduct.single_eq_of_ne _ y hw
    rw [e, e, mul_zero]

theorem dual_scaled {ψ₀ ψ : AddChar (AF F) ℂ} {a : F} (ha : a ≠ 0)
    (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x)) (v : HeightOneSpectrum (𝓞 F))
    (h₀ : ∀ t : Fv F v, t ∈ dualV F ψ₀ v ↔
      ∀ d ∈ differentV F v, t * (d : Fv F v) ∈ v.adicCompletionIntegers F) :
    ((intV F v).relIndex (dualV F ψ v) ≠ 0 ∧ (dualV F ψ v).relIndex (intV F v) ≠ 0) ∧
      dualIndex F ψ v = normDifferentV F v * ‖algebraMap F (Fv F v) a‖⁻¹ := by
  obtain ⟨δ, hδ, hD⟩ := exists_generator_differentV v
  have e : dualV F ψ v = colonV v (algebraMap F (Fv F v) a * δ) := by
    ext t
    have e1 : t ∈ dualV F ψ v ↔ algebraMap F (Fv F v) a * t ∈ dualV F ψ₀ v := by
      change (∀ s ∈ _, _) ↔ (∀ s ∈ _, _)
      simp only [psiV_of_eq h, mul_assoc]
    rw [e1, h₀, hD, mem_colonV, ← mul_assoc, mul_comm t]
    constructor
    · intro H
      exact H δ (Ideal.mem_span_singleton_self δ)
    · intro H d hd
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hd
      have := mul_mem H z.2
      change _ * ((z : Fv F v) * δ) ∈ _
      rwa [mul_comm (z : Fv F v), ← mul_assoc]
  have hc : algebraMap F (Fv F v) a * δ ≠ 0 := mul_ne_zero ((map_ne_zero _).2 ha) hδ
  rw [dualIndex, e]
  refine ⟨(index_colonV v _ hc).1, ?_⟩
  rw [(index_colonV v _ hc).2, normDifferentV, hD, card_quot_span v δ hδ, norm_mul, mul_inv,
    mul_comm]

theorem eq_of_isScalingInf {ψ₀ ψ : AddChar (AF F) ℂ} (h₀ : IsStdChar F ψ₀) (hψ : IsCharAF F ψ)
    {a : F} (ha : a ≠ 0) (hs : IsScalingInf F ψ a) (x : AF F) :
    ψ x = ψ₀ (algebraMap F (AF F) a * x) := by
  have hc : IsCharAF F (ψ₀.mulShift (algebraMap F (AF F) a)) := by
    refine ⟨h₀.1.1.comp (continuous_const_mul _), fun y => h₀.1.2.1 _, fun b => ?_, ?_⟩
    · rw [AddChar.mulShift_apply, ← map_mul]; exact h₀.1.2.2.1 _
    · obtain ⟨y, hy⟩ := h₀.1.2.2.2
      refine ⟨algebraMap F (AF F) a⁻¹ * y, ?_⟩
      rwa [AddChar.mulShift_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  have hs' : IsScalingInf F (ψ₀.mulShift (algebraMap F (AF F) a)) a :=
    isScalingInf_of_eq F h₀ fun _ => rfl
  rw [GlobalTheory.StdAdelicChar.eq_of_psiInf_eq hψ hc fun y => (hs y).trans (hs' y).symm]
  rfl

theorem finite_norm_ne_one {a : F} (ha : a ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖algebraMap F (Fv F v) a‖).Finite :=
  (FinitePlace.hasFiniteMulSupport ha).preimage
    (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn

theorem absInf_mul_finprod {a : F} (ha : a ≠ 0) :
    absInf F a * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖ = 1 := by
  rw [← prod_abs_eq_one ha, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  rfl

theorem summable_eulerInv (E : Type) [Field E] [Algebra F E] (M : ℕ) (hM : 2 ≤ M) :
    Summable fun v => |eulerInv F E M v - 1| := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun v => ?_)
    (GlobalTheory.PrimeSquareSum.summable_absNorm_inv_sq F).1
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℕ) := by
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le
  have h2 : |etaV F E v| = 1 := by
    unfold etaV; split_ifs <;> simp
  rw [eulerInv, sub_sub_cancel_left, abs_neg, abs_mul, abs_pow, h2, one_pow, one_mul, resCard,
    zpow_neg, zpow_natCast, abs_of_nonneg (by positivity)]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 hM)

theorem density_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ, IsCharAF F ψ → (∀ v, (intV F v).relIndex (dualV F ψ v) ≠ 0 ∧ (dualV F ψ v).relIndex (intV F v) ≠ 0) ∧ ∀ a : F, a ≠ 0 → IsScalingInf F ψ a → ∀ M : ℕ, 2 ≤ M → Summable (fun v => |localDensity F E ψ M v - 1|) ∧ ∃ P : ℝ, 0 < P ∧ HasProd (localDensity F E ψ M) P ∧ absInf F a ^ ((M : ℝ) - 1 / 2) * P = absDiscr F ^ ((1 : ℝ) / 2 - M) / Formalism.HermitianLatticesTheory.lValEta E M := by
  intro F E _ _ _ _ _ _ σ hCM hst hU ψ hψ
  obtain ⟨ψ₀, h₀, -⟩ := GlobalTheory.T.existsUnique_isStandardAdeleChar_unramifiedCM_base F E σ hCM hst hU
  have hd := GlobalTheory.T.dual_lattice_different_index F E σ hCM hst hU ψ₀ h₀
  obtain ⟨hfin, hprod, -⟩ := GlobalTheory.T.finprod_localDifferentIdealNorm_eq_discr F E σ hCM hst hU
  refine ⟨fun v => ?_, fun a ha hs M hM => ?_⟩
  · obtain ⟨a, ha, h⟩ := GlobalTheory.T.exists_eq_standardAdeleChar_rational_dilate F E σ hCM hst hU ψ₀ h₀ ψ hψ
    exact (dual_scaled ha h v (hd v).1).1
  obtain ⟨hL, hE⟩ := GlobalTheory.T.hasProd_quadExtLocalEulerFactorInv_inv F E σ hCM hst hU M hM
  have hn : ∀ v, dualIndex F ψ v = normDifferentV F v * ‖algebraMap F (Fv F v) a‖⁻¹ := fun v =>
    (dual_scaled ha (eq_of_isScalingInf h₀ hψ ha hs) v (hd v).1).2
  have hfa := finite_norm_ne_one ha
  classical
  let S : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset ∪ hfa.toFinset
  have hS : ∀ v ∉ S, dualIndex F ψ v = 1 := fun v hv => by
    simp only [S, Finset.mem_union, Set.Finite.mem_toFinset, Function.mem_mulSupport, not_or,
      not_not] at hv
    rw [hn, hv.1, hv.2]; simp
  have hA : 0 < absInf F a :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 ha) _
  have hD : 0 < absDiscr F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hSp : ∏ v ∈ S, dualIndex F ψ v = absDiscr F * absInf F a := by
    have e1 := absInf_mul_finprod ha
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (by
      intro v hv; simp only [S, Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hv)] at e1
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (by
      intro v hv; simp only [S, Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inl hv)] at hprod
    simp only [hn]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← hprod, Nat.cast_prod,
      inv_eq_of_mul_eq_one_left e1]
  have h1 : HasProd (fun v => dualIndex F ψ v ^ ((1 : ℝ) / 2 - M))
      ((absDiscr F * absInf F a) ^ ((1 : ℝ) / 2 - M)) := by
    rw [← hSp, ← Real.finset_prod_rpow _ _ (fun v _ => by rw [hn]; positivity)]
    exact hasProd_prod_of_ne_finset_one fun v hv => by rw [hS v hv, Real.one_rpow]
  have h2 : HasProd (eulerInv F E M) (Formalism.HermitianLatticesTheory.lValEta E M)⁻¹ := by
    have := Filter.Tendsto.inv₀ hE hL.ne'
    simp only [Finset.prod_inv_distrib, inv_inv] at this
    exact this
  refine ⟨?_, _, by positivity, h1.mul h2, ?_⟩
  · refine (summable_eulerInv E M hM).congr_cofinite ?_
    filter_upwards [S.eventually_cofinite_notMem] with v hv
    rw [localDensity, hS v hv, Real.one_rpow, one_mul]
  · rw [Real.mul_rpow hD.le hA.le, div_eq_mul_inv _ (Formalism.HermitianLatticesTheory.lValEta E M), ← mul_assoc,
      mul_left_comm, ← Real.rpow_add hA]
    simp

end GlobalTheory.LocalDensityProduct

end
