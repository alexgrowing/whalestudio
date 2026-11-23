import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordGeoNum
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordArInt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace IntegralCoordinateChange

theorem hermLine_ext {ι : Unit → Type} [∀ k, Fintype (ι k)] {L M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (ha : L.a = M.a) (hh : L.h = M.h) : L = M := by
  cases L
  cases M
  cases ha
  cases hh
  rfl

variable {T T₂ : Type} [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂]

omit [DecidableEq T₂] in

theorem subst_subst {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (f : MRing (dualBlocks T)) :
    intCoordSubst A (intCoordSubst B f) = f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    show intCoordSubst A (intCoordSubst B (algebraMap ℤ _ a)) = algebraMap ℤ _ a
    rw [AlgHom.commutes, AlgHom.commutes]
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | mul_X f p hf =>
    rw [map_mul, map_mul, hf]
    congr 1
    obtain ⟨⟨⟩, t⟩ := p
    have hC : ∀ a : ℤ, (C a : MRing (dualBlocks T)) = (a : MRing (dualBlocks T)) := fun a => map_intCast C a
    simp only [intCoordSubst, aeval_X, map_sum, map_mul, eq_intCast, hC, map_intCast, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Int.cast_mul, ← Finset.sum_mul, ← Int.cast_sum]
    have h1 : ∀ x : T, ∑ s, B s t * A x s = (A * B) x t := by
      intro x
      simp [Matrix.mul_apply, mul_comm]
    simp_rw [h1, hAB, Matrix.one_apply]
    simp

omit [DecidableEq T₂] in

theorem subst_surjective {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) :
    Function.Surjective (intCoordSubst A) :=
  fun f => ⟨intCoordSubst B f, subst_subst hAB f⟩

def substEquiv {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (hBA : B * A = 1) :
    MRing (dualBlocks T₂) ≃+* MRing (dualBlocks T) :=
  (AlgEquiv.ofAlgHom (intCoordSubst A) (intCoordSubst B) (AlgHom.ext (subst_subst hAB))
    (AlgHom.ext (subst_subst hBA))).toRingEquiv

theorem map_eq_comap {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (hBA : B * A = 1)
    (P : Ideal (MRing (dualBlocks T₂))) : P.map (intCoordSubst A) = P.comap (intCoordSubst B) := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun x hx => ?_) fun x hx => ?_
  · rw [Ideal.mem_comap, Ideal.mem_comap, subst_subst hBA]
    exact hx
  · rw [← subst_subst hAB x]
    exact Ideal.mem_map_of_mem _ hx

omit [DecidableEq T] in

theorem weight_one_eq (m : (Σ _ : Unit, T) →₀ ℕ) : Finsupp.weight 1 m = ∑ i : T, m ⟨(), i⟩ := by
  have h : Finsupp.weight 1 m = m.degree := by
    rw [Finsupp.degree_eq_weight_one]
    rfl
  rw [h, Finsupp.degree_eq_sum, Fintype.sum_sigma]
  simp

omit [DecidableEq T] in

theorem isMultiHomog_iff (f : MRing (dualBlocks T)) (d : Unit → ℕ) :
    Geo.IsMultiHomog f d ↔ f.IsHomogeneous (d ()) := by
  constructor
  · intro h m hm
    rw [weight_one_eq]
    exact h m (mem_support_iff.mpr hm) ()
  · intro h m hm k
    obtain ⟨⟩ := k
    rw [← weight_one_eq]
    exact h (mem_support_iff.mp hm)

omit [DecidableEq T] [DecidableEq T₂] in

theorem isMultiHomog_subst (M : Matrix T T₂ ℤ) {f : MRing (dualBlocks T₂)} {d : Unit → ℕ}
    (hf : Geo.IsMultiHomog f d) : Geo.IsMultiHomog (intCoordSubst M f) d := by
  rw [isMultiHomog_iff] at hf ⊢
  have h := hf.eval₂ (algebraMap ℤ (MRing (dualBlocks T))) (fun p => ∑ t, C (M t p.2) * X ⟨(), t⟩)
    (fun r => by rw [MvPolynomial.algebraMap_eq]; exact isHomogeneous_C _ r)
    (fun p => IsHomogeneous.sum _ _ _ fun t _ => isHomogeneous_C_mul_X _ _)
  rw [one_mul] at h
  exact h

omit [DecidableEq T₂] in

theorem isRelevant_comap {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1)
    (W : Ideal (MRing (dualBlocks T))) : Geo.IsRelevant (W.comap (intCoordSubst A)) ↔ Geo.IsRelevant W := by
  constructor
  · rintro h ⟨⟩
    obtain ⟨s, hs⟩ := h ()
    by_contra hall
    push Not at hall
    apply hs
    rw [Ideal.mem_comap]
    simp only [intCoordSubst, aeval_X]
    exact Ideal.sum_mem _ fun t _ => Ideal.mul_mem_left _ _ (hall t)
  · rintro h ⟨⟩
    obtain ⟨t, ht⟩ := h ()
    by_contra hall
    push Not at hall
    apply ht
    rw [← subst_subst hAB (X ⟨(), t⟩)]
    have e : intCoordSubst B (X ⟨(), t⟩ : MRing (dualBlocks T)) = ∑ s, C (B s t) * X ⟨(), s⟩ := by
      simp only [intCoordSubst, aeval_X]
    rw [e, map_sum]
    refine Ideal.sum_mem _ fun s _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (hall s)

theorem isMultiHomogIdeal_comap {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (hBA : B * A = 1)
    {Q : Ideal (MRing (dualBlocks T))} (hQ : Geo.IsMultiHomogIdeal Q) :
    Geo.IsMultiHomogIdeal (Q.comap (intCoordSubst A)) := by
  obtain ⟨S, hS, rfl⟩ := hQ
  refine ⟨intCoordSubst B '' S, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, isMultiHomog_subst B ha⟩
  · rw [← map_eq_comap hBA hAB, Ideal.map_span]

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in

theorem comap_C_comap (A : Matrix T T₂ ℤ) (W : Ideal (MRing (dualBlocks T))) :
    (W.comap (intCoordSubst A)).comap (C : ℤ →+* MRing (dualBlocks T₂)) = W.comap C := by
  ext c
  simp only [Ideal.mem_comap]
  rw [show intCoordSubst A (C c) = C c from (intCoordSubst A).commutes c]

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in
theorem isHorizontal_comap (A : Matrix T T₂ ℤ) (W : Ideal (MRing (dualBlocks T))) :
    Geo.IsHorizontal (W.comap (intCoordSubst A)) ↔ Geo.IsHorizontal W := by
  unfold Geo.IsHorizontal
  rw [comap_C_comap]

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in
theorem charOf_comap (A : Matrix T T₂ ℤ) (W : Ideal (MRing (dualBlocks T))) :
    Geo.charOf (W.comap (intCoordSubst A)) = Geo.charOf W := by
  simp only [Geo.charOf, comap_C_comap]

theorem ringKrullDim_quot_comap {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (hBA : B * A = 1)
    (Q : Ideal (MRing (dualBlocks T))) :
    ringKrullDim (MRing (dualBlocks T₂) ⧸ Q.comap (intCoordSubst A)) =
      ringKrullDim (MRing (dualBlocks T) ⧸ Q) :=
  ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ Q (substEquiv hAB hBA)
    (Ideal.map_comap_of_surjective _ (subst_surjective hAB) Q).symm)

theorem isArithVar_comap {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (hBA : B * A = 1)
    {Q : Ideal (MRing (dualBlocks T))} {d : ℕ} (hQ : Geo.IsArithVar Q d) :
    Geo.IsArithVar (Q.comap (intCoordSubst A)) d := by
  obtain ⟨hK, ⟨hp, hmh, hrel⟩, hhor, hdim⟩ := hQ
  have := hp
  refine ⟨hK, ⟨Ideal.comap_isPrime _ _, isMultiHomogIdeal_comap hAB hBA hmh, (isRelevant_comap hAB Q).2 hrel⟩,
    (isHorizontal_comap A Q).2 hhor, ?_⟩
  rw [ringKrullDim_quot_comap hAB hBA]
  exact hdim

theorem multAt_comap {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (hBA : B * A = 1)
    (J W : Ideal (MRing (dualBlocks T))) (hW : W.IsPrime) :
    Geo.multAt (J.comap (intCoordSubst A)) (W.comap (intCoordSubst A)) = Geo.multAt J W := by
  have hW' : (W.comap (intCoordSubst A)).IsPrime := Ideal.comap_isPrime _ _
  unfold Geo.multAt
  rw [dif_pos hW', dif_pos hW]
  congr 1
  let e := Ideal.quotientEquiv (J.comap (intCoordSubst A)) J (substEquiv hAB hBA)
    (Ideal.map_comap_of_surjective _ (subst_surjective hAB) J).symm
  exact NumbersDVR.length_localizedModule_eq_of_surjective ((intCoordSubst A : MRing (dualBlocks T₂) →ₐ[ℤ]
    MRing (dualBlocks T)) : MRing (dualBlocks T₂) →+* MRing (dualBlocks T)) (subst_surjective hAB) W
    (W.comap (intCoordSubst A)) rfl _ _ e.toAddEquiv fun s x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk J (intCoordSubst A (s * y)) =
        Ideal.Quotient.mk J (intCoordSubst A s) * Ideal.Quotient.mk J (intCoordSubst A y)
      rw [map_mul, map_mul]

theorem sup_span_comap {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (hBA : B * A = 1)
    (Q : Ideal (MRing (dualBlocks T))) (s : MRing (dualBlocks T)) :
    Q.comap (intCoordSubst A) ⊔ Ideal.span {intCoordSubst B s} =
      (Q ⊔ Ideal.span {s}).comap (intCoordSubst A) := by
  rw [← map_eq_comap hBA hAB, ← map_eq_comap hBA hAB, Ideal.map_sup, Ideal.map_span, Set.image_singleton]

theorem divSupp_comap {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (hBA : B * A = 1)
    (Q : Ideal (MRing (dualBlocks T))) (s : MRing (dualBlocks T)) :
    Geo.divSupp (Q.comap (intCoordSubst A)) (intCoordSubst B s) =
      (fun W => W.comap (intCoordSubst A)) '' Geo.divSupp Q s := by
  ext W₂
  have hm := Ideal.comap_minimalPrimes_eq_of_surjective
    (f := ((intCoordSubst A : MRing (dualBlocks T₂) →ₐ[ℤ] MRing (dualBlocks T)) :
      MRing (dualBlocks T₂) →+* MRing (dualBlocks T))) (subst_surjective hAB) (Q ⊔ Ideal.span {s})
  simp only [Ideal.comap_coe] at hm
  constructor
  · rintro ⟨hW, hrel⟩
    rw [sup_span_comap hAB hBA, hm] at hW
    obtain ⟨W, hW, rfl⟩ := hW
    exact ⟨W, ⟨hW, (isRelevant_comap hAB W).1 hrel⟩, rfl⟩
  · rintro ⟨W, ⟨hW, hrel⟩, rfl⟩
    refine ⟨?_, (isRelevant_comap hAB W).2 hrel⟩
    rw [sup_span_comap hAB hBA, hm]
    exact ⟨W, hW, rfl⟩

omit [DecidableEq T] [DecidableEq T₂] in

theorem contDiff_intCoordPt (A : Matrix T T₂ ℤ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (intCoordPt A) := by
  refine contDiff_pi.2 fun p => ?_
  exact ContDiff.sum fun t _ => (contDiff_apply ℝ ℂ _).mul contDiff_const

omit [DecidableEq T₂] in

theorem isSmoothHerm_intCoordLine (A : Matrix T T₂ ℤ) (hA : ∃ B : Matrix T₂ T ℤ, A * B = 1)
    {L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)} (hL : Geo.IsSmoothHerm L) :
    Geo.IsSmoothHerm (intCoordLine A hA L) :=
  hL.comp (contDiff_intCoordPt A).contDiffOn fun _ hz => intCoordPt_ne_zero hA hz

omit [DecidableEq T] in

theorem pt_pt {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hBA : B * A = 1) (z : (Σ _ : Unit, T₂) → ℂ) :
    intCoordPt A (intCoordPt B z) = z := by
  funext ⟨⟨⟩, s⟩
  simp only [intCoordPt, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have h1 : ∀ s', ∑ t, (B s' t : ℂ) * (A t s : ℂ) = (((B * A) s' s : ℤ) : ℂ) := by
    intro s'
    simp [Matrix.mul_apply]
  simp_rw [h1, hBA, Matrix.one_apply]
  simp

theorem line_line {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (hBA : B * A = 1)
    (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)) :
    intCoordLine B ⟨A, hBA⟩ (intCoordLine A ⟨B, hAB⟩ L) = L :=
  hermLine_ext rfl (funext fun z => by
    change L.h (intCoordPt A (intCoordPt B z)) = L.h z
    rw [pt_pt hBA])

omit [DecidableEq T₂] in

theorem line_tensor (A : Matrix T T₂ ℤ) (hA : ∃ B : Matrix T₂ T ℤ, A * B = 1)
    (L M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)) :
    intCoordLine A hA (L.tensor M) = (intCoordLine A hA L).tensor (intCoordLine A hA M) :=
  hermLine_ext rfl rfl

def transFam (A : Matrix T T₂ ℤ) (B : Matrix T₂ T ℤ) (hBA : B * A = 1)
    (I : Ideal (MRing (dualBlocks T₂)) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)) → ℝ) :
    Ideal (MRing (dualBlocks T)) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) → ℝ :=
  fun Q m M => I (Q.comap (intCoordSubst A)) m (fun j => intCoordLine B ⟨A, hBA⟩ (M j))

omit [Fintype T] [DecidableEq T] in

theorem C_charOf_mem (V : Ideal (MRing (dualBlocks T))) :
    (C ((Geo.charOf V : ℕ) : ℤ) : MRing (dualBlocks T)) ∈ V := by
  have h : ((Geo.charOf V : ℕ) : ℤ) ∈ V.comap (C : ℤ →+* MRing (dualBlocks T)) := by
    rw [← Submodule.IsPrincipal.span_singleton_generator (V.comap C), Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.mpr dvd_rfl
  exact h

theorem recR_trans {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (hBA : B * A = 1)
    (hG : IntCoordGeoNum.Statement) (hI : IntCoordArInt.Statement)
    (I : Ideal (MRing (dualBlocks T₂)) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)) → ℝ)
    (Q : Ideal (MRing (dualBlocks T))) (n : ℕ) (M : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T))
    (Ab : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) (s : MRing (dualBlocks T)) (hQ : Geo.IsArithVar Q (n + 1))
    (hM : ∀ j, Geo.IsSmoothHerm (M j)) (hAb : Geo.IsSmoothHerm Ab) (hs : Geo.IsSectionOn Q Ab s) :
    Geo.recR I (Q.comap (intCoordSubst A)) (fun j => intCoordLine B ⟨A, hBA⟩ (M j))
        (intCoordLine B ⟨A, hBA⟩ Ab) (intCoordSubst B s) =
      Geo.recR (transFam A B hBA I) Q M Ab s := by
  have hinj : Set.InjOn (fun W : Ideal (MRing (dualBlocks T)) => W.comap (intCoordSubst A)) (Geo.divSupp Q s) :=
    fun W _ W' _ h => Ideal.comap_injective_of_surjective _ (subst_surjective hAB) h
  unfold Geo.recR
  rw [divSupp_comap hAB hBA, finsum_mem_image hinj, hI T T₂ A B hAB hBA Q n M Ab s hQ hM hAb hs]
  congr 1
  refine finsum_mem_congr rfl fun W hW => ?_
  have hWp : W.IsPrime := hW.1.1.1
  rw [sup_span_comap hAB hBA, multAt_comap hAB hBA _ _ hWp]
  congr 1
  by_cases hh : Geo.IsHorizontal W
  · rw [if_pos ((isHorizontal_comap A W).2 hh), if_pos hh]
    rfl
  · rw [if_neg (mt (isHorizontal_comap A W).1 hh), if_neg hh, charOf_comap]
    obtain ⟨hmp, hp, hdim⟩ := (Geo.divSuppArith Unit (dualBlocks T) Q n Ab s W hQ hs hW).2 hh
    rw [hG T T₂ A B hAB hBA W n (Geo.charOf W) hmp hp (C_charOf_mem W) hdim]
    rfl

theorem isRFamily_trans {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (hBA : B * A = 1)
    (hG : IntCoordGeoNum.Statement) (hI : IntCoordArInt.Statement)
    {I : Ideal (MRing (dualBlocks T₂)) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)) → ℝ}
    (hIR : AI.I2.IsRFamily I) : AI.I2.IsRFamily (transFam A B hBA I) := by
  have hsn : ∀ (n : ℕ) (M : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T))
      (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)),
      (fun j => intCoordLine B ⟨A, hBA⟩
          (Fin.snoc (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) M N j)) =
        Fin.snoc (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂))
          (fun j => intCoordLine B ⟨A, hBA⟩ (M j)) (intCoordLine B ⟨A, hBA⟩ N) :=
    fun n M N => Fin.comp_snoc (intCoordLine B ⟨A, hBA⟩) M N
  refine ⟨fun Q n M Ab Bb hQ hM hA hB => ?_, fun Q n M Ab s a hQ hM hA ha hs hsQ => ?_⟩
  · unfold transFam
    rw [hsn, hsn, hsn, line_tensor]
    exact hIR.1 _ n _ _ _ (isArithVar_comap hAB hBA hQ)
      (fun j => isSmoothHerm_intCoordLine _ _ (hM j)) (isSmoothHerm_intCoordLine _ _ hA)
      (isSmoothHerm_intCoordLine _ _ hB)
  · show I (Q.comap (intCoordSubst A)) (n + 1) (fun j => intCoordLine B ⟨A, hBA⟩
        (Fin.snoc (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) M Ab j)) =
      Geo.recR (transFam A B hBA I) Q M Ab s
    rw [hsn, ← recR_trans hAB hBA hG hI I Q n M Ab s hQ hM hA ⟨a, ha, hs, hsQ⟩]
    refine hIR.2 _ n _ _ (intCoordSubst B s) a (isArithVar_comap hAB hBA hQ)
      (fun j => isSmoothHerm_intCoordLine _ _ (hM j)) (isSmoothHerm_intCoordLine _ _ hA) ha
      (isMultiHomog_subst B hs) fun h => hsQ ?_
    rw [Ideal.mem_comap, subst_subst hAB] at h
    exact h

end IntegralCoordinateChange

open IntegralCoordinateChange in

theorem IntCoordChange.proof (hU : AI.I2.UniqueStatement) (hG : IntCoordGeoNum.Statement)
    (hI : IntCoordArInt.Statement) : IntCoordChange.Statement := by
  intro T T₂ _ _ _ _ A B hAB hBA II hII P n L hn hP hL
  have hIR : ∀ (T' : Type) [Fintype T'], AI.I2.IsRFamily (II Unit (dualBlocks T')) :=
    fun T' _ => AI.I2.IsIntersectionFamily.isRFamily (hII Unit (dualBlocks T'))
  have hJ := isRFamily_trans hAB hBA hG hI (hIR T₂)
  have hPmap : P.map (intCoordSubst A) = P.comap (intCoordSubst B) := map_eq_comap hAB hBA P
  have hP' : Geo.IsArithVar (P.map (intCoordSubst A)) n := by
    rw [hPmap]
    exact isArithVar_comap hBA hAB hP
  rw [hU Unit (dualBlocks T) (II Unit (dualBlocks T)) (transFam A B hBA (II Unit (dualBlocks T₂))) (hIR T) hJ
    (P.map (intCoordSubst A)) n (fun j => intCoordLine A ⟨B, hAB⟩ (L j)) hn hP'
    (fun j => isSmoothHerm_intCoordLine _ _ (hL j))]
  have hcm : (P.map (intCoordSubst A)).comap (intCoordSubst A) = P := by
    rw [hPmap]
    ext f
    rw [Ideal.mem_comap, Ideal.mem_comap, subst_subst hBA]
  change II Unit (dualBlocks T₂) ((P.map (intCoordSubst A)).comap (intCoordSubst A)) n
    (fun j => intCoordLine B ⟨A, hBA⟩ (intCoordLine A ⟨B, hAB⟩ (L j))) = _
  rw [hcm]
  simp only [line_line hAB hBA]

end

end GroundTheory.Heights₂.Heights
