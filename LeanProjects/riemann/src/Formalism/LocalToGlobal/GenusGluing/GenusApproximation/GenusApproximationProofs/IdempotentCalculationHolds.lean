import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GlueExists

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adele_sum_apply {ι : Type} (T : Finset ι) (f : ι → Formalism.L2.Herm.Af F) (w : HeightOneSpectrum (𝓞 F)) :
    (∑ v ∈ T, f v) w = ∑ v ∈ T, f v w := by
  classical
  induction T using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

theorem one_tmul_mem (a : Formalism.L2.Herm.Af F) (h : a ∈ Formalism.UG.intAd F) :
    (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E :=
  (Formalism.L2.DIV.adS F E ⟨a, h⟩).2

theorem iA_algebraMap (r : 𝓞 F) :
    iA F E (algebraMap (𝓞 F) E r) = (1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (Formalism.L2.Herm.Af F) r := by
  have := Formalism.UG.P.csGlob_tmul_int (F := F) (E := E) (1 : E) r
  rw [mul_one] at this
  exact this.symm

theorem iA_algebraMap_mem (r : 𝓞 F) : iA F E (algebraMap (𝓞 F) E r) ∈ Formalism.L2.Herm.intAf F E := by
  rw [iA_algebraMap]
  exact one_tmul_mem _ (Formalism.UG.P.levelaf_int_mem r)

theorem eP_mem (P : HeightOneSpectrum (𝓞 F) → Prop) : eP E P ∈ Formalism.L2.Herm.intAf F E :=
  (Formalism.L2.DIV.adS F E (Formalism.L2.DIV.idemAd P)).2

theorem eP_mul_mem (P : HeightOneSpectrum (𝓞 F) → Prop) (c : 𝓞 F) (hc : ∀ w, P w → c ∉ w.asIdeal)
    (u : E ⊗[F] Formalism.L2.Herm.Af F) (hu : iA F E (algebraMap (𝓞 F) E c) * u ∈ Formalism.L2.Herm.intAf F E) :
    eP E P * u ∈ Formalism.L2.Herm.intAf F E := by
  classical
  have hw : ∀ w : HeightOneSpectrum (𝓞 F),
      (if P w then (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹ else 0) ∈ w.adicCompletionIntegers F := by
    intro w
    split_ifs with h
    · exact Formalism.L2.DIV.fr_inv_int w c (hc w h)
    · exact zero_mem _
  set wA : Formalism.UG.intAd F := Formalism.L2.DIV.mkAd _ hw with hwA
  have hprod : algebraMap (𝓞 F) (Formalism.L2.Herm.Af F) c * (wA : Formalism.L2.Herm.Af F) =
      ((Formalism.L2.DIV.idemAd P : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) := by
    ext1 w
    show algebraMap (𝓞 F) (w.adicCompletion F) c * ((wA : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) w =
      ((Formalism.L2.DIV.idemAd P : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) w
    rw [hwA, Formalism.L2.DIV.mkAd_apply]
    by_cases h : P w
    · rw [if_pos h, Formalism.L2.DIV.idemAd_pos h]
      refine mul_inv_cancel₀ (Formalism.UG.P.levelaf_algebraMap_ne_zero w c ?_)
      rintro rfl
      exact hc w h (Ideal.zero_mem _)
    · rw [if_neg h, Formalism.L2.DIV.idemAd_neg h, mul_zero]
  have key : eP E P = (1 : E) ⊗ₜ[F] (wA : Formalism.L2.Herm.Af F) * iA F E (algebraMap (𝓞 F) E c) := by
    rw [iA_algebraMap, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm, hprod]
    rfl
  rw [key, mul_assoc]
  exact mul_mem (one_tmul_mem _ wA.2) hu

end SlopeTestRemainingChoices

theorem idempotentCalculation_holds : IdemCalc := by
  intro F E _ _ _ _ _
  refine ⟨fun P => eP_mem P, fun P Q => ?_, fun T => ?_⟩
  · show (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd P : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) *
        (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd Q : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) =
      (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd (fun v => P v ∧ Q v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ext1 w
    show ((Formalism.L2.DIV.idemAd P : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) w *
        ((Formalism.L2.DIV.idemAd Q : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) w =
      ((Formalism.L2.DIV.idemAd (fun v => P v ∧ Q v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) w
    by_cases hP : P w
    · by_cases hQ : Q w
      · rw [Formalism.L2.DIV.idemAd_pos hP, Formalism.L2.DIV.idemAd_pos hQ,
          Formalism.L2.DIV.idemAd_pos (P := fun v => P v ∧ Q v) ⟨hP, hQ⟩, one_mul]
      · rw [Formalism.L2.DIV.idemAd_neg hQ, Formalism.L2.DIV.idemAd_neg (P := fun v => P v ∧ Q v) (fun h => hQ h.2),
          mul_zero]
    · rw [Formalism.L2.DIV.idemAd_neg hP, Formalism.L2.DIV.idemAd_neg (P := fun v => P v ∧ Q v) (fun h => hP h.1),
        zero_mul]
  · show ∑ v ∈ T, (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) +
        (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd (fun v => v ∉ T) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) = 1
    rw [← TensorProduct.tmul_sum, ← TensorProduct.tmul_add, Algebra.TensorProduct.one_def]
    congr 1
    ext1 w
    show (∑ v ∈ T, ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F)) w +
        ((Formalism.L2.DIV.idemAd (fun v => v ∉ T) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) w = 1
    rw [adele_sum_apply]
    by_cases hw : w ∈ T
    · rw [Finset.sum_eq_single w, Formalism.L2.DIV.idemAd_pos (P := fun x => x = w) rfl,
        Formalism.L2.DIV.idemAd_neg (P := fun x => x ∉ T) (not_not.2 hw), add_zero]
      · intro b _ hb
        exact Formalism.L2.DIV.idemAd_neg (P := fun x => x = b) (v := w) (fun h => hb h.symm)
      · intro h
        exact absurd hw h
    · rw [Finset.sum_eq_zero, Formalism.L2.DIV.idemAd_pos (P := fun x => x ∉ T) hw, zero_add]
      intro b hb
      exact Formalism.L2.DIV.idemAd_neg (P := fun x => x = b) (v := w) (fun h => hw (by subst h; exact hb))

theorem idempotentIntegral_holds : IdemInt := by
  intro F E _ _ _ _ _ v r hr u hu
  exact eP_mul_mem _ r (fun w hw => by subst hw; exact hr) u hu

theorem idempotentCofinite_holds : IdemCof := by
  intro F E _ _ _ _ _ D _ u hu
  exact eP_mul_mem _ D (fun _ h => h) u hu

theorem idempotentDenominator_holds : IdemDenom := by
  intro F E _ _ _ _ _ v u hu
  obtain ⟨d, hd0, hd⟩ := Formalism.UG.P.levelaf_denom (F := F) (E := E) u
  rw [Formalism.L2.DIV.levelafC_eq_incl] at hd
  obtain ⟨π, hπv, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hD : d * π ≠ 0 := mul_ne_zero hd0 hπ0
  obtain ⟨r, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F (d * π) hD
    ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) (Formalism.L2.DIV.idemAd _).2
  refine ⟨r, fun hr => ?_, ?_⟩
  · have h2 : ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) v =
        algebraMap (𝓞 F) (v.adicCompletion F) r + algebraMap (𝓞 F) (v.adicCompletion F) (d * π) * y v :=
      congrArg (fun z : Formalism.L2.Herm.Af F => z v) e
    rw [Formalism.L2.DIV.idemAd_pos (P := fun w => w = v) (v := v) rfl] at h2
    have hrv : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
      rw [Formalism.UG.P.csApprox_val_int]
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).2 hr
    have hDv : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (d * π)) < 1 := by
      rw [Formalism.UG.P.csApprox_val_int]
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 (Ideal.mul_mem_left _ d hπv)
    have hyv : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy v)
    have h1 : Valued.v (1 : v.adicCompletion F) < 1 := by
      rw [h2]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hrv ?_)
      rw [map_mul]
      exact mul_lt_one_of_lt_of_le hDv hyv
    rw [map_one] at h1
    exact lt_irrefl _ h1
  · have hid : eAt E v = iA F E (algebraMap (𝓞 F) E r) +
        iA F E (algebraMap (𝓞 F) E π) * (1 : E) ⊗ₜ[F] y * iA F E (algebraMap (𝓞 F) E d) := by
      show (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) = _
      rw [e, iA_algebraMap, iA_algebraMap, iA_algebraMap, TensorProduct.tmul_add,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, map_mul]
      congr 2
      ring
    have hsub : iA F E (algebraMap (𝓞 F) E r) * u = eAt E v * u -
        iA F E (algebraMap (𝓞 F) E π) * (1 : E) ⊗ₜ[F] y * (iA F E (algebraMap (𝓞 F) E d) * u) := by
      rw [hid]; ring
    rw [hsub]
    exact sub_mem hu (mul_mem (mul_mem (iA_algebraMap_mem π) (one_tmul_mem y hy)) hd)

theorem memLocalizedStd_holds : MemLocFStd := by
  intro F E _ _ _ _ _ n v z
  have halg : ∀ r : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) = algebraMap (𝓞 F) E r :=
    fun r => (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E r).symm
  constructor
  · rintro ⟨s, hs, hsz⟩
    obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.1 hs
    have hr' : r ∉ v.asIdeal := hr
    intro i
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 hsz) i (Set.mem_univ i))
    refine idempotentIntegral_holds F E v r hr' _ ?_
    rw [← map_mul]
    have : algebraMap (𝓞 F) E r * z i = algebraMap (𝓞 E) E b := by
      rw [hb, ← halg]
      rfl
    rw [this]
    exact Formalism.UG.CS.incl_int b
  · intro h
    have h' : ∀ i, ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap (𝓞 F) E r * z i) := by
      intro i
      obtain ⟨r, hr, hm⟩ := idempotentDenominator_holds F E v _ (h i)
      rw [← map_mul] at hm
      exact ⟨r, hr, Formalism.UG.P.csGlob_int _ hm⟩
    choose r hr hint using h'
    refine ⟨algebraMap (𝓞 F) (𝓞 E) (∏ i, r i),
      Submonoid.mem_map_of_mem _ (Submonoid.prod_mem _ (fun i _ => (hr i : r i ∈ v.asIdeal.primeCompl))), ?_⟩
    refine Submodule.mem_pi.2 (fun i _ => Submodule.mem_one.2 ?_)
    obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = algebraMap (𝓞 F) E (r i) * z i :=
      ⟨⟨_, hint i⟩, rfl⟩
    refine ⟨algebraMap (𝓞 F) (𝓞 E) (∏ j ∈ Finset.univ.erase i, r j) * b, ?_⟩
    show _ = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) (∏ i, r i)) * z i
    rw [map_mul, hb, halg, halg, ← Finset.mul_prod_erase Finset.univ r (Finset.mem_univ i), map_mul]
    ring

end Formalism.L2.GenusGluing.Gen
