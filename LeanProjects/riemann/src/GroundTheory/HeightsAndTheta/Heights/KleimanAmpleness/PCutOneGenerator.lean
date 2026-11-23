import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutOneGeneratorSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GlobalFunctionsIntegralSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestriction
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDimTie
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace CutOneGenerator

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

theorem mem_sub_of_mem_secs {S : Type u} [CommRing S] {E : Type w} [Field E] [Algebra S E] {M : ℕ}
    {z : Fin (M + 1) → E} {H : SubSystem S z E} {t : E} (ht : t ∈ H.secs) (I : Chart z) :
    t ∈ H.sub I :=
  (Submodule.restrictScalars_mem S _ _).mp ((Submodule.mem_iInf _).mp ht I)

theorem mem_chartRing_of_mem_idealMod {pp : Ideal (Poly k N)} {I : Chart x} {a : Ω}
    (ha : a ∈ idealMod (x := x) pp I) : a ∈ chartRing k x I := by
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨f, s, e, -, hs, hf, hse, rfl⟩ := ha; exact ⟨f, s, e, hs, hf, hse, rfl⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact mul_mem c.2 ha

variable {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {Q : SubSystem k x Ω} {Q' : SubSystem k y K'} {ρ : Ω → K'}

theorem restrict_zero (hR : RestrictData Q hxy Q' ρ) (J : Chart y) : ρ 0 = 0 := by
  have := hR.add J 0 (Q.sub _).zero_mem 0 (Q.sub _).zero_mem
  rw [add_zero] at this
  simpa using this

theorem exists_restrict_mul (hR : RestrictData Q hxy Q' ρ) (J : Chart y) {c q : Ω}
    (hc : c ∈ chartRing k x (liftChart hxy J)) (hq : q ∈ Q.sub (liftChart hxy J)) :
    ∃ b ∈ chartRing k y J, ρ (c * q) = b * ρ q := by
  obtain ⟨f, t, e, ht, hf, hte, rfl⟩ := hc
  exact ⟨_, ⟨f, t, e, ht, hf, hte, rfl⟩, hR.smul J q hq f t e ht hf hte⟩

theorem restrict_twist_eq_zero (hR : RestrictData Q hxy Q' ρ) {pp : Ideal (Poly k N)}
    (hpp : primeOf (S := k) y = pp) (J : Chart y) {z : Ω}
    (hz : z ∈ (Q.twist (idealSys x pp)).sub (liftChart hxy J)) :
    z ∈ Q.sub (liftChart hxy J) ∧ ρ z = 0 := by
  have hgen : ∀ w ∈ Q.sub (liftChart hxy J), ∀ q ∈ idealMod (x := x) pp (liftChart hxy J),
      q * w ∈ Q.sub (liftChart hxy J) ∧ ρ (q * w) = 0 := by
    intro w hw q hq
    have hmw : ∀ a ∈ idealMod (x := x) pp (liftChart hxy J), a * w ∈ Q.sub (liftChart hxy J) :=
      fun a ha => (Q.sub _).smul_mem
        ⟨a, mem_chartRing_of_mem_idealMod (pp := pp) (I := liftChart hxy J) ha⟩ hw
    refine ⟨hmw q hq, ?_⟩
    induction hq using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨f, t, e, hfp, ht, hf, hte, rfl⟩ := ha
      rw [hR.smul J w hw f t e ht hf hte,
        (mem_primeOf_of_isHomogeneous y hf).mp (hpp ▸ hfp), zero_div, zero_mul]
    | zero => rw [zero_mul]; exact restrict_zero hR J
    | add a b ha hb iha ihb =>
      rw [add_mul, hR.add J _ (hmw a ha) _ (hmw b hb), iha, ihb, add_zero]
    | smul c a ha iha =>
      obtain ⟨b, -, hb⟩ := exists_restrict_mul hR J c.2 (hmw a ha)
      rw [chartRing_smul_def, mul_assoc, hb, iha, mul_zero]
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨q, hq, w, hw, rfl⟩ := hz; exact hgen w hw q hq
  | zero => exact ⟨zero_mem _, restrict_zero hR J⟩
  | add a b _ _ ha hb => exact ⟨add_mem ha.1 hb.1, by rw [hR.add J a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
  | smul c a _ ha =>
    refine ⟨(Q.sub _).smul_mem c ha.1, ?_⟩
    obtain ⟨b, -, hb⟩ := exists_restrict_mul hR J c.2 ha.1
    rw [chartRing_smul_def]
    erw [hb]
    rw [ha.2, mul_zero]

theorem exists_eq_mul_of_le (hR : RestrictData Q hxy Q' ρ) {pp : Ideal (Poly k N)}
    (hpp : primeOf (S := k) y = pp) (J : Chart y) {s : Ω} (hs : s ∈ Q.sub (liftChart hxy J))
    (hle : Q.sub (liftChart hxy J) ≤ (Q.twist (idealSys x pp)).sub (liftChart hxy J) ⊔
      Submodule.span (chartRing k x (liftChart hxy J)) {s}) {t : K'} (ht : t ∈ Q'.sub J) :
    ∃ b ∈ chartRing k y J, t = b * ρ s := by
  rw [← hR.span J] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨q, hq, rfl⟩ := ht
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp (hle hq)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨hu', hu0⟩ := restrict_twist_eq_zero hR hpp J hu
    obtain ⟨b, hb, he⟩ := exists_restrict_mul hR J a.2 hs
    refine ⟨b, hb, ?_⟩
    rw [hR.add J u hu' _ ((Q.sub _).smul_mem a hs), hu0, zero_add, chartRing_smul_def, he]
  | zero => exact ⟨0, zero_mem _, (zero_mul _).symm⟩
  | add t t' _ _ ht ht' =>
    obtain ⟨b, hb, rfl⟩ := ht
    obtain ⟨b', hb', rfl⟩ := ht'
    exact ⟨b + b', add_mem hb hb', (add_mul _ _ _).symm⟩
  | smul c t _ ht =>
    obtain ⟨b, hb, rfl⟩ := ht
    exact ⟨c * b, mul_mem c.2 hb, by rw [chartRing_smul_def, mul_assoc]⟩

theorem exists_algHom_ker_eq {R : Type w} [CommRing R] [Algebra k R] (P : Ideal R) [P.IsPrime] :
    ∃ (F : Type w) (_ : Field F) (_ : Algebra k F) (ψ : R →ₐ[k] F), RingHom.ker ψ = P := by
  refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
    (IsScalarTower.toAlgHom k (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  ext a
  rw [RingHom.mem_ker]
  change algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P a) = 0 ↔ _
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end CutOneGenerator

open CutOneGenerator in

theorem CutOneGenerator.proof (hG : GlobalFunctionsIntegral.Statement.{u, w}) :
    CutOneGenerator.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs hgen
  obtain ⟨r, h, hV⟩ := hL
  obtain ⟨j, hXj⟩ := hW.relevant
  have hxj : x j ≠ 0 := by
    intro h0
    apply hXj
    apply hW.le
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j), aeval_X, h0]
  obtain ⟨hprime, hpt⟩ :=
    PrimeFiltration.Point.proof k Ω N x pp hW.isPrime hW.homog hW.le j hxj hXj
  obtain ⟨K', _, _, ψ, hker⟩ := @exists_algHom_ker_eq k _ _ _ _ (chartPrime pp hxj) hprime
  set y : Fin (N + 1) → K' := fun i => ψ (ratio hxj i) with hy
  have hpy : primeOf (S := k) y = pp := hpt K' ψ hker
  have hy0 : y j ≠ 0 := by
    have e : ratio (S := k) hxj j = 1 := Subtype.ext (div_self hxj)
    show ψ (ratio hxj j) ≠ 0
    rw [e, map_one]
    exact one_ne_zero
  have hxy : ∀ i, y i ≠ 0 → x i ≠ 0 := by
    intro i hyi hxi
    apply hyi
    have e : ratio (S := k) hxj i = 0 := Subtype.ext (by show x i / x j = 0; rw [hxi, zero_div])
    show ψ (ratio hxj i) = 0
    rw [e, map_zero]
  have hne : y ≠ 0 := Function.ne_iff.mpr ⟨j, hy0⟩
  obtain ⟨Q', ρ, hR, hV', hdim⟩ :=
    exists_restrictData_isVeryAmpleBy (by rw [hpy]; exact hW.le) hxy (singleChart hy0) L h hV
  have hWy : IsSubvar y (primeOf (S := k) y) (n + 1) := by
    rw [hpy]; exact ⟨hW.isPrime, hW.homog, hpy.le, hW.relevant, hW.dim⟩
  have hdy : dimCl k y = ((n + 1 : ℕ) : Cardinal) := (DimTie.proof k K' N y hne (n + 1)).mp hWy
  have hmul : ∀ t ∈ Q'.secs, ∀ i (hi : y i ≠ 0), ∃ b ∈ chartRing k y (singleChart hi), t = b * ρ s :=
    fun t ht i hi => exists_eq_mul_of_le hR hpy (singleChart hi) (mem_sub_of_mem_secs hs _)
      (hgen i (hxy i hi)) (mem_sub_of_mem_secs ht _)
  have hρs : ρ s ≠ 0 := by
    intro h0
    obtain ⟨Q'', hQ''⟩ := Q'.invertible (singleChart hy0)
    have hbot : Q'.sub (singleChart hy0) = ⊥ := (Submodule.eq_bot_iff _).mpr fun t ht => by
      obtain ⟨b, -, rfl⟩ := exists_eq_mul_of_le hR hpy (singleChart hy0) (mem_sub_of_mem_secs hs _)
        (hgen j (hxy j hy0)) ht
      rw [h0, mul_zero]
    rw [hbot, Submodule.bot_mul] at hQ''
    have h1 : (1 : K') ∈ (⊥ : Submodule (chartRing k y (singleChart hy0)) K') := by
      rw [hQ'']; exact Submodule.one_le.mp le_rfl
    exact one_ne_zero ((Submodule.mem_bot _).mp h1)
  have hint : ∀ l, IsIntegral k (ρ (h l) / ρ s) := fun l => hG k K' N y _ hne fun i hi => by
    obtain ⟨b, hb, he⟩ := hmul (ρ (h l)) (hV'.mem_secs l) i hi
    rw [he, mul_div_cancel_right₀ _ hρs]
    exact hb
  have halg : Algebra.IsAlgebraic k (funField (k := k) (ρ ∘ h)) := by
    apply IntermediateField.isAlgebraic_adjoin
    rintro _ ⟨i, l, -, rfl⟩
    have e : (ρ ∘ h) l / (ρ ∘ h) i = ρ (h l) / ρ s * (ρ (h i) / ρ s)⁻¹ := by
      rw [inv_div, div_mul_div_cancel₀ hρs]; rfl
    rw [e]
    exact (hint l).mul (hint i).inv
  have h0 : dimCl k (ρ ∘ h) = 0 := trdeg_eq_zero
  rw [← hdim, hdy] at h0
  exact Nat.succ_ne_zero n (Nat.cast_eq_zero.mp h0)

end

end GroundTheory.Heights₂.Heights.Kleiman
