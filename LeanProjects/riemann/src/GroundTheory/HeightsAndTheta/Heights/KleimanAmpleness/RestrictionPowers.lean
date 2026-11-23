import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem res_mem_chartRing_of_mem_twistMod_zero {I : Chart x} {a : Ω} (ha : a ∈ twistMod S x 0 I) :
    a ∈ chartRing S x I := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [chartRing_smul_def, mul_one]; exact c.2

theorem res_mem_twistMod_zero_of_mem_chartRing {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ twistMod S x 0 I := by
  have := (twistMod S x 0 I).smul_mem ⟨a, ha⟩ (one_mem_twistMod_zero I)
  rwa [chartRing_smul_def, mul_one] at this

theorem SubSystem.res_mul_mem_pow (H : SubSystem S x Ω) (I : Chart x) {m : ℕ} {a : Ω}
    (ha : a ∈ (H.pow m).sub I) (n : ℕ) {b : Ω} (hb : b ∈ (H.pow n).sub I) :
    a * b ∈ (H.pow (m + n)).sub I := by
  induction n generalizing b with
  | zero =>
    have hb' : b ∈ chartRing S x I := res_mem_chartRing_of_mem_twistMod_zero hb
    have := ((H.pow m).sub I).smul_mem ⟨b, hb'⟩ ha
    rw [chartRing_smul_def] at this
    rw [mul_comm]; exact this
  | succ n ih =>
    change b ∈ ((H.pow n).twist H).sub I at hb
    change a * b ∈ ((H.pow (m + n)).twist H).sub I
    refine Submodule.span_induction (p := fun z _ => a * z ∈ ((H.pow (m + n)).twist H).sub I)
      ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨q, hq, z, hz, rfl⟩
      refine Submodule.subset_span ⟨q, hq, a * z, ih hz, ?_⟩
      simp only [smul_eq_mul]; ring
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
    · intro c u _ hu
      rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
      exact Submodule.smul_mem _ c hu

theorem LineBundle.res_exists_mul_mem_pow (H : LineBundle S x) {I J : Chart x} (hIJ : I.1 ⊆ J.1)
    (n : ℕ) {z : Ω} (hz : z ∈ (H.pow n).sub J) :
    ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧ (a : Ω) * z ∈ (H.pow n).sub I := by
  induction n generalizing z with
  | zero =>
    obtain ⟨a, ha, haz⟩ := ((twistBundle S x 0).mem_iff I J hIJ z).mp hz
    exact ⟨a, ha, haz⟩
  | succ n ih =>
    change z ∈ ((H.pow n).twist H.toSubSystem).sub J at hz
    change ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) * z ∈ ((H.pow n).twist H.toSubSystem).sub I
    refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I,
      IsUnit (chartIncl hIJ a) ∧ (a : Ω) * z ∈ ((H.pow n).twist H.toSubSystem).sub I) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, w, hw, rfl⟩
      obtain ⟨a₁, ha₁, hq'⟩ := (H.mem_iff I J hIJ q).mp hq
      obtain ⟨a₂, ha₂, hw'⟩ := ih hw
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂,
        Submodule.subset_span ⟨_, hq', _, hw', ?_⟩⟩
      simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
    · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [mul_zero]; exact Submodule.zero_mem _⟩
    · rintro u v _ _ ⟨a₁, ha₁, hu⟩ ⟨a₂, ha₂, hv⟩
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have h1 := Submodule.smul_mem _ a₂ hu
      have h2 := Submodule.smul_mem _ a₁ hv
      rw [chartRing_smul_def] at h1 h2
      convert Submodule.add_mem _ h1 h2 using 1
      simp only [Subalgebra.coe_mul]; ring
    · rintro c u _ ⟨a, ha, hu⟩
      obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem hIJ c
      refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
      have := Submodule.smul_mem _ (⟨_, hc⟩ : chartRing S x I) hu
      rw [chartRing_smul_def] at this
      convert this using 1
      rw [chartRing_smul_def]; simp only [Subalgebra.coe_mul]; ring

section AmpleChart

variable {H : SubSystem S x Ω} {σ : Ω} {I : Chart x}

theorem res_ampleChart_mul {a b : Ω} (ha : a ∈ ampleChart H 1 σ I) (hb : b ∈ ampleChart H 1 σ I) :
    a * b ∈ ampleChart H 1 σ I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  rw [one_mul] at hn hm ⊢
  have := H.res_mul_mem_pow I hn m hm
  convert this using 1; ring

theorem res_chartRing_sub_ampleChart {a : Ω} (ha : a ∈ chartRing S x I) : a ∈ ampleChart H 1 σ I :=
  ⟨0, by rw [pow_zero, mul_one, mul_zero]; exact res_mem_twistMod_zero_of_mem_chartRing ha⟩

theorem res_ampleChart_pow {a : Ω} (ha : a ∈ ampleChart H 1 σ I) (n : ℕ) :
    a ^ n ∈ ampleChart H 1 σ I := by
  induction n with
  | zero => rw [pow_zero]; exact res_chartRing_sub_ampleChart (one_mem _)
  | succ n ih => rw [pow_succ]; exact res_ampleChart_mul ih ha

end AmpleChart

variable (x) in

def resUnionChart (I J : Chart x) : Chart x :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩

theorem res_isHomogeneous_prod_X (s : Finset (Fin (N + 1))) :
    (∏ i ∈ s, (X i : Poly S N)).IsHomogeneous s.card := by
  have := IsHomogeneous.prod s (fun i => (X i : Poly S N)) (fun _ => 1)
    (fun i _ => isHomogeneous_X S i)
  simpa using this

theorem res_aeval_prod_X (s : Finset (Fin (N + 1))) :
    aeval x (∏ i ∈ s, (X i : Poly S N)) = ∏ i ∈ s, x i := by
  simp [map_prod]

theorem res_xProd_ne_zero (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)

theorem res_exists_pow_mul_mem_chartRing (I J : Chart x) {u : Ω}
    (hu : u ∈ chartRing S x (resUnionChart x I J)) :
    ∃ M : ℕ, (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * u ∈ chartRing S x I := by
  set t' := xProd J ^ I.1.card / xProd I ^ J.1.card with ht'
  obtain ⟨i₀, hi₀⟩ := I.2.1
  have hx₀ : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  let T : Ω → Prop := fun u => ∃ M : ℕ, t' ^ M * u ∈ chartRing S x I
  have hTmem : ∀ {u}, u ∈ chartRing S x I → T u := fun hu => ⟨0, by rw [pow_zero, one_mul]; exact hu⟩
  have hTmul : ∀ {u v}, T u → T v → T (u * v) := by
    rintro u v ⟨M, hM⟩ ⟨M', hM'⟩
    refine ⟨M + M', ?_⟩
    have := mul_mem hM hM'
    convert this using 1; ring

  have hgen : ∀ i ∈ I.1 ∪ J.1, T (x i₀ / x i) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiI | hiJ
    · exact hTmem ⟨X i₀, X i, 1, X_mem_monos hiI, isHomogeneous_X S i₀, isHomogeneous_X S i,
        by simp⟩
    · have hxi : x i ≠ 0 := (mem_support x).mp (J.2.2 hiJ)
      obtain ⟨a, ha⟩ : ∃ a, I.1.card = a + 1 :=
        ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr I.2.1)).symm⟩
      obtain ⟨c, hc⟩ : ∃ c, (J.1.erase i).card = c := ⟨_, rfl⟩
      have hJc : J.1.card = c + 1 := by rw [← hc, Finset.card_erase_add_one hiJ]
      refine ⟨1, X i₀ * (∏ l ∈ J.1.erase i, (X l : Poly S N)) * (∏ l ∈ J.1, (X l : Poly S N)) ^ a,
        (∏ l ∈ I.1, (X l : Poly S N)) ^ J.1.card, (a + 1) * (c + 1),
        pow_mem (prod_mem fun l hl => X_mem_monos hl) _, ?_, ?_, ?_⟩
      · have h1 := ((isHomogeneous_X S i₀).mul (res_isHomogeneous_prod_X (S := S) (J.1.erase i))).mul
          ((res_isHomogeneous_prod_X (S := S) J.1).pow a)
        convert h1 using 1
        rw [hc, hJc]; ring
      · have h1 := (res_isHomogeneous_prod_X (S := S) I.1).pow J.1.card
        convert h1 using 1
        rw [ha, hJc]
      · have hprod : ∏ l ∈ J.1, x l = x i * ∏ l ∈ J.1.erase i, x l := (Finset.mul_prod_erase _ _ hiJ).symm
        have hxI := res_xProd_ne_zero I
        simp only [map_mul, map_pow, aeval_X, res_aeval_prod_X, ht', xProd]
        unfold xProd at hxI
        rw [ha, hprod]
        field_simp
        ring

  have hmono : ∀ s ∈ monos (S := S) (I.1 ∪ J.1), ∃ e : ℕ, s.IsHomogeneous e ∧
      T (x i₀ ^ e / aeval x s) := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨i, hi, rfl⟩ := hs
      exact ⟨1, isHomogeneous_X S i, by rw [pow_one, aeval_X]; exact hgen i (Finset.mem_coe.mp hi)⟩
    | one => exact ⟨0, isHomogeneous_one _ _, hTmem (by rw [pow_zero, map_one, div_one]; exact one_mem _)⟩
    | mul s s' _ _ hs hs' =>
      obtain ⟨e, he, hT⟩ := hs
      obtain ⟨e', he', hT'⟩ := hs'
      refine ⟨e + e', he.mul he', ?_⟩
      have := hTmul hT hT'
      convert this using 1
      rw [pow_add, map_mul, div_mul_div_comm]
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hu
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (resUnionChart x I J) hs
  obtain ⟨e', he', hT⟩ := hmono s hs
  have hee : e = e' := hse.inj_right he' (fun h => hs0 (by rw [h, map_zero]))
  subst hee
  have h1 : aeval x f / x i₀ ^ e ∈ chartRing S x I :=
    ⟨f, X i₀ ^ e, e, pow_mem (X_mem_monos hi₀) e, hf, isHomogeneous_X_pow i₀ e, by
      rw [map_pow, aeval_X]⟩
  obtain ⟨M, hM⟩ := hTmul (hTmem h1) hT
  refine ⟨M, ?_⟩
  convert hM using 2
  field_simp

theorem res_exists_pow_mul_mem_ampleRing (H : LineBundle S x) {σ b : Ω} {J : Chart x}
    (hb : b ∈ ampleRing H.toSubSystem 1 σ)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H.toSubSystem 1 σ I)
    {z : Ω} (hz : z ∈ ampleChart H.toSubSystem 1 σ J) :
    ∃ E : ℕ, b ^ E * z ∈ ampleRing H.toSubSystem 1 σ := by
  have hloc : ∀ I : Chart x, ∃ E : ℕ, b ^ E * z ∈ ampleChart H.toSubSystem 1 σ I := by
    intro I
    have hIK : I.1 ⊆ (resUnionChart x I J).1 := Finset.subset_union_left
    have hJK : J.1 ⊆ (resUnionChart x I J).1 := Finset.subset_union_right
    obtain ⟨n, hn⟩ := hz
    rw [one_mul] at hn
    have hnK := (H.pow n).mono J (resUnionChart x I J) hJK _ hn
    obtain ⟨a, ha, haz⟩ := H.res_exists_mul_mem_pow hIK n hnK
    have haz' : (a : Ω) * z ∈ ampleChart H.toSubSystem 1 σ I :=
      ⟨n, by rw [one_mul, mul_assoc]; exact haz⟩
    obtain ⟨v, hv⟩ := ha.exists_right_inv
    have hav : (a : Ω) * (v : Ω) = 1 := congrArg Subtype.val hv
    obtain ⟨M, hM⟩ := res_exists_pow_mul_mem_chartRing I J v.2
    obtain ⟨e, he⟩ := hbJ I
    refine ⟨e * M, ?_⟩
    have hxI := res_xProd_ne_zero I
    have hxJ := res_xProd_ne_zero J
    have htt : (xProd J ^ I.1.card / xProd I ^ J.1.card) *
        (xProd I ^ J.1.card / xProd J ^ I.1.card) = 1 := by
      field_simp
    have key : b ^ (e * M) * z = ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * (v : Ω)) *
        (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * ((a : Ω) * z) := by
      have : ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * (v : Ω)) *
          (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * ((a : Ω) * z) =
          ((xProd J ^ I.1.card / xProd I ^ J.1.card) *
            (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * b ^ (e * M) * ((a : Ω) * v) * z := by
        ring
      rw [this, htt, hav]; ring
    rw [key]
    exact res_ampleChart_mul (res_ampleChart_mul (res_chartRing_sub_ampleChart hM) (res_ampleChart_pow he M)) haz'
  choose E hE using hloc
  refine ⟨Finset.univ.sup E, Set.mem_iInter.mpr fun I => ?_⟩
  have hle : E I ≤ Finset.univ.sup E := Finset.le_sup (Finset.mem_univ I)
  have hbI : b ∈ ampleChart H.toSubSystem 1 σ I := Set.mem_iInter.mp hb I
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact res_ampleChart_mul (res_ampleChart_pow hbI _) (hE I)

theorem res_span_chart_le {R : Set Ω} {I J : Chart x} (hIJ : I.1 ⊆ J.1) {z : Ω}
    (hz : z ∈ Submodule.span (chartRing S x I) R) : z ∈ Submodule.span (chartRing S x J) R := by
  refine Submodule.span_induction (p := fun z _ => z ∈ Submodule.span (chartRing S x J) R)
    (fun w hw => Submodule.subset_span hw) (Submodule.zero_mem _)
    (fun _ _ _ _ hu hv => Submodule.add_mem _ hu hv) ?_ hz
  intro c u _ hu
  have := Submodule.smul_mem _ (chartIncl hIJ c) hu
  rw [chartRing_smul_def] at this ⊢
  exact this

theorem res_mem_span_iff_exists_isUnit {R : Set Ω} {I J : Chart x} (hIJ : I.1 ⊆ J.1) (z : Ω) :
    z ∈ Submodule.span (chartRing S x J) R ↔ ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) • z ∈ Submodule.span (chartRing S x I) R := by
  constructor
  · intro hz
    refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) • z ∈ Submodule.span (chartRing S x I) R) ?_ ?_ ?_ ?_ hz
    · intro w hw
      exact ⟨1, by rw [map_one]; exact isUnit_one,
        by rw [OneMemClass.coe_one, one_smul]; exact Submodule.subset_span hw⟩
    · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [smul_zero]; exact Submodule.zero_mem _⟩
    · rintro u v _ _ ⟨a₁, ha₁, hu⟩ ⟨a₂, ha₂, hv⟩
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have h1 := Submodule.smul_mem _ a₂ hu
      have h2 := Submodule.smul_mem _ a₁ hv
      rw [chartRing_smul_def, smul_eq_mul] at h1 h2
      convert Submodule.add_mem _ h1 h2 using 1
      simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
    · rintro c u _ ⟨a, ha, hu⟩
      obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem hIJ c
      refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
      have := Submodule.smul_mem _ (⟨_, hc⟩ : chartRing S x I) hu
      rw [chartRing_smul_def, smul_eq_mul] at this
      convert this using 1
      rw [chartRing_smul_def]; simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
  · rintro ⟨a, ⟨u, hu⟩, haz⟩
    have hJ := res_span_chart_le hIJ haz
    have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hz : z = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • z) := by
      rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
    rw [hz]
    exact Submodule.smul_mem _ _ hJ

end

end GroundTheory.Heights₂.Heights.Kleiman
