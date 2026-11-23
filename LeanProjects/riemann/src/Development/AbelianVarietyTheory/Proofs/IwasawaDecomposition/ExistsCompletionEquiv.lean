import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlTieOfInertCore
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemDualSetOfMemSpan
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocIdFr

open NumberField IsDedekindDomain IsLocalRing Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.GO.PlWitt
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaceOrbit

theorem exists_hom_of_dense {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    [IsAdicComplete J B] (f : R →+* A) (g : R →+* B) (hs : ∀ (k : ℕ) (a : A), ∃ x, a - f x ∈ I ^ k)
    (hk : ∀ (k : ℕ) x, f x ∈ I ^ k → g x ∈ J ^ k) :
    ∃ h : A →+* B, ∀ (k : ℕ) a x, a - f x ∈ I ^ k → h a - g x ∈ J ^ k := by
  have hsur : ∀ k : ℕ, Function.Surjective ((Ideal.Quotient.mk (I ^ k)).comp f) := fun k y => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hs k a
    exact ⟨x, (Ideal.Quotient.eq.2 hx).symm⟩
  let u : (k : ℕ) → A ⧸ I ^ k →+* B ⧸ J ^ k := fun k =>
    RingHom.liftOfSurjective _ (hsur k) ⟨(Ideal.Quotient.mk (J ^ k)).comp g, fun x hx =>
      Ideal.Quotient.eq_zero_iff_mem.2 (hk k x (Ideal.Quotient.eq_zero_iff_mem.1 hx))⟩
  let φ : (k : ℕ) → A →+* B ⧸ J ^ k := fun k => (u k).comp (Ideal.Quotient.mk _)
  have hφ : ∀ k a x, a - f x ∈ I ^ k → φ k a = Ideal.Quotient.mk _ (g x) := fun k a x h => by
    change u k (Ideal.Quotient.mk _ a) = _
    rw [Ideal.Quotient.eq.2 h]
    exact RingHom.liftOfRightInverse_comp_apply ((Ideal.Quotient.mk (I ^ k)).comp f) _ _ _ x
  have hc : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (φ n) = φ m := by
    intro m n h
    refine RingHom.ext fun a => ?_
    obtain ⟨x, hx⟩ := hs n a
    rw [RingHom.comp_apply, hφ n a x hx, hφ m a x (Ideal.pow_le_pow_right h hx)]
    rfl
  refine ⟨IsAdicComplete.liftRingHom J φ hc, fun k a x h => ?_⟩
  rw [← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom, hφ k a x h]

theorem eq_of_forall_pow {A : Type} [CommRing A] (I : Ideal A) [IsHausdorff I A] {a b : A}
    (h : ∀ k : ℕ, a - b ∈ I ^ k) : a = b :=
  sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact h k)

theorem exists_equiv_of_dense {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    [IsAdicComplete I A] [IsAdicComplete J B] (f : R →+* A) (g : R →+* B)
    (hs : ∀ (k : ℕ) (a : A), ∃ x, a - f x ∈ I ^ k) (hs' : ∀ (k : ℕ) (b : B), ∃ x, b - g x ∈ J ^ k)
    (hk : ∀ (k : ℕ) x, f x ∈ I ^ k ↔ g x ∈ J ^ k) : ∃ e : A ≃+* B, ∀ x, e (f x) = g x := by
  obtain ⟨h, hh⟩ := exists_hom_of_dense I J f g hs fun k x => (hk k x).1
  obtain ⟨h', hh'⟩ := exists_hom_of_dense J I g f hs' fun k x => (hk k x).2
  refine ⟨RingEquiv.ofRingHom h h' (RingHom.ext fun b => eq_of_forall_pow J fun k => ?_)
    (RingHom.ext fun a => eq_of_forall_pow I fun k => ?_), fun x => eq_of_forall_pow J fun k => ?_⟩
  · obtain ⟨x, hx⟩ := hs' k b
    simpa using sub_mem (hh k _ x (hh' k b x hx)) hx
  · obtain ⟨x, hx⟩ := hs k a
    simpa using sub_mem (hh' k _ x (hh k a x hx)) hx
  · exact hh k _ x (by simp)

variable {F : Type} [Field F] [NumberField F] {p n : ℕ} [hp : Fact p.Prime]

theorem exists_completion_equiv {v : HeightOneSpectrum (𝓞 F)} {i : F →+* Qn p n} (h : Good v i) :
    ∃ e : Qn p n ≃+* v.adicCompletion F, (∀ x : F, e (i x) = algebraMap F _ x) ∧
      ∀ y, y ∈ Set.range (algebraMap (Wn p n) (Qn p n)) ↔ e y ∈ v.adicCompletionIntegers F := by
  have hint := h.intAt
  have hd := h.dense
  obtain ⟨g, hg, -, hk⟩ := h
  have hinj := IsFractionRing.injective (Wn p n) (Qn p n)
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by rw [hk, map_natCast, cc_eq_zero]
  have hval : ∀ x : 𝓞 F, Valued.v ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) x : v.adicCompletionIntegers F) :
      v.adicCompletion F) = v.valuation F (x : F) := fun x => by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have hpF : ∀ k : ℕ, ((p : F) ^ k) ≠ 0 := fun k => pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hvp : ∀ k : ℕ, Valued.v ((((p : v.adicCompletionIntegers F) ^ k : v.adicCompletionIntegers F)) :
      v.adicCompletion F) = v.valuation F ((p : F) ^ k) := fun k => by
    simpa using hval ((p : 𝓞 F) ^ k)
  have hvp0 : ∀ k : ℕ, v.valuation F ((p : F) ^ k) ≠ 0 := fun k => by simpa using hpF k
  haveI : IsAdicComplete (Ideal.span {(p : v.adicCompletionIntegers F)}) (v.adicCompletionIntegers F) :=
    (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).1 _ (by
      have := hval p
      rw [map_natCast] at this
      rw [this]
      exact (v.valuation_lt_one_iff_mem (K := F) _).2 hpv)
  obtain ⟨e, he⟩ := exists_equiv_of_dense (Ideal.span {(p : Wn p n)}) (Ideal.span {(p : v.adicCompletionIntegers F)})
    g (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
    (fun k a => by
      obtain ⟨x, z, hx⟩ := hd a k
      rw [hg] at hx
      exact ⟨x, by rw [hinj hx, Ideal.span_singleton_pow, Ideal.mem_span_singleton]; exact ⟨-z, by ring⟩⟩)
    (fun k b => by
      obtain ⟨x, hx⟩ := Idele.exists_valued_sub_le v (a := (b : v.adicCompletion F)) b.2
        (-WithZero.log (v.valuation F ((p : F) ^ k))).toNat
      refine ⟨x, ?_⟩
      rw [Ideal.span_singleton_pow, GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v (by rw [hvp]; exact hvp0 k), hvp]
      refine le_trans hx ?_
      conv_rhs => rw [← WithZero.exp_log (hvp0 k)]
      rw [WithZero.exp_le_exp]
      omega)
    (fun k x => by
      rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow,
        GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v (by rw [hvp]; exact hvp0 k), hvp, hval,
        ← div_le_one₀ (zero_lt_iff.2 (hvp0 k)), ← map_div₀, ← GlobalTheory.UnramCompletion.intAt_iff, hint,
        Ideal.mem_span_singleton']
      refine exists_congr fun y => ?_
      rw [map_div₀, eq_div_iff ((_root_.map_ne_zero i).2 (hpF k)), hg, ← hinj.eq_iff]
      simp)
  refine ⟨IsFractionRing.ringEquivOfRingEquiv e, fun x => ?_, fun y => ⟨?_, fun hy => ?_⟩⟩
  · have : ((IsFractionRing.ringEquivOfRingEquiv (K := Qn p n) (L := v.adicCompletion F) e).toRingHom.comp i) =
        algebraMap F (v.adicCompletion F) :=
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (RingHom.ext fun x => by
        change IsFractionRing.ringEquivOfRingEquiv e (i (x : F)) = _
        rw [hg, IsFractionRing.ringEquivOfRingEquiv_algebraMap, he]
        rfl)
    exact RingHom.congr_fun this x
  · rintro ⟨w, rfl⟩
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact (e w).2
  · refine ⟨e.symm ⟨_, hy⟩, (IsFractionRing.ringEquivOfRingEquiv (K := Qn p n) (L := v.adicCompletion F) e).injective ?_⟩
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, e.apply_symm_apply]
    rfl

theorem exists_first_frame {E : Type} [Field E] [NumberField E] [Algebra F E] {k : ℕ} (w : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F)
    (halg : ∀ a : w.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a))
    (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hsp : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) :
    ∃ fr : GL (Fin k) (w.adicCompletion F), ∀ t : Fin k → w.adicCompletion F,
      (∃ x ∈ Formalism.L2.Herm.locL w Λ, ∀ a, (φ (x a)).1 = t a) ↔
        ∀ a, ((fr⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)).mulVec t a ∈
          w.adicCompletionIntegers F := by
  obtain ⟨B, -, -, hB, -⟩ := GlobalTheory.DualFrame.exists_dual_frames F E (AlgHom.id F E) k 1 (by simp) Λ hfin hsp w
  let π : E ⊗[F] w.adicCompletion F →+* w.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom
  have hinv : (((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) =
      ((B⁻¹ : GL (Fin k) _) : Matrix (Fin k) (Fin k) _).map π := by
    rw [← map_inv]; rfl
  refine ⟨bc π B, fun t => ⟨?_, fun hu => ?_⟩⟩
  · rintro ⟨x, hx, hxt⟩ a
    have ht : t = π ∘ x := funext fun a => (hxt a).symm
    rw [ht, hinv, ← RingHom.map_mulVec]
    refine Formalism.MainNotions.Gaps.Loc.fst_int w φ halg _ ((hB _).1 ?_ a)
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    exact hx
  · refine ⟨_, (hB fun a => (1 : E) ⊗ₜ[F] (((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)).1.mulVec t a)).2
      fun a => Formalism.MainNotions.Gaps.LG.sc_right_mem w _ (hu a), fun a => ?_⟩
    refine (RingHom.map_mulVec π _ _ a).trans ?_
    have : (π ∘ fun a => (1 : E) ⊗ₜ[F] (((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)).1.mulVec t a)) =
        ((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)).1.mulVec t := funext fun a => congrArg Prod.fst (halg _)
    rw [this]
    change ((bc π B).1 *ᵥ _) a = _
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]

end GlobalTheory.PlaceOrbit
