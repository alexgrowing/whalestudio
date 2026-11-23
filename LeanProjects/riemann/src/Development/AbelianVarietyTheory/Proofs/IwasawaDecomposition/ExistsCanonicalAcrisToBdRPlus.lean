import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisMembershipSpanIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineXiPowSaturatedQuotientCompleteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisMap

theorem smodEq_iff {R : Type} [CommRing R] (a : R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule R R)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem complete_of_sandwich (p N : ℕ) {B R : Type} [CommRing B] [CommRing R]
    (hB : IsAdicComplete (Ideal.span {(p : B)}) B) (g : B →+* R) (hg : Function.Injective g)
    (h : ∀ r : R, ∃ b : B, (p : R) ^ N * r = g b) : IsAdicComplete (Ideal.span {(p : R)}) R := by
  have key : ∀ (b : B) (k : ℕ), (p : R) ^ (k + N) ∣ g b → (p : B) ^ k ∣ b := by
    rintro b k ⟨y, hy⟩
    obtain ⟨c, hc⟩ := h y
    refine ⟨c, hg ?_⟩
    rw [hy, map_mul, map_pow, map_natCast, ← hc]
    ring
  refine { haus' := fun x hx => ?_, prec' := fun x hx => ?_ }
  · simp only [smodEq_iff, sub_zero] at hx
    obtain ⟨y, hy⟩ := hx N
    obtain ⟨b, hb⟩ := h y
    have : b = 0 := by
      refine IsHausdorff.haus hB.toIsHausdorff b fun k => ?_
      rw [smodEq_iff, sub_zero]
      exact key b k (by rw [← hb, ← hy]; exact hx _)
    rw [hy, hb, this, map_zero]
  · simp only [smodEq_iff] at hx ⊢
    have h1 : ∀ k, ∃ b : B, x (k + N) - x N = g b := fun k => by
      obtain ⟨y, hy⟩ := hx (Nat.le_add_left N k)
      obtain ⟨b, hb⟩ := h y
      exact ⟨-b, by rw [map_neg, ← hb, ← hy]; ring⟩
    choose b hb using h1
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hB.toIsPrecomplete (f := b) (fun {m n} hmn => by
      rw [smodEq_iff]
      refine key _ _ ?_
      rw [map_sub, ← hb, ← hb, sub_sub_sub_cancel_right]
      exact hx (Nat.add_le_add_right hmn N))
    refine ⟨x N + g L, fun n => ?_⟩
    have h2 := map_dvd g ((smodEq_iff _ _ _ _).1 (hL n))
    rw [map_pow, map_natCast, map_sub, ← hb] at h2
    have h3 := dvd_add (hx (Nat.le_add_right n N)) h2
    convert h3 using 1
    ring

theorem exists_extend (p : ℕ) {D R : Type} [CommRing D] [CommRing R]
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) (f : D →+* R) :
    ∃ F : AdicCompletion (Ideal.span {(p : D)}) D →+* R, ∀ d, F (algebraMap D _ d) = f d := by
  have hf : (Ideal.span {(p : D)}).map f ≤ Ideal.span {(p : R)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  refine ⟨((AdicCompletion.ofAlgEquiv (Ideal.span {(p : R)})).symm : _ →+* R).comp
    (GlobalTheory.AdicMaps.adicMap (Ideal.span {(p : D)}) (Ideal.span {(p : R)}) f
      (Ideal.map_le_iff_le_comap.1 hf)), fun d => ?_⟩
  rw [RingHom.comp_apply, GlobalTheory.AdicMaps.adicMap_alg]
  exact (AdicCompletion.ofAlgEquiv (Ideal.span {(p : R)})).symm_apply_apply (f d)

theorem extend_unique (p : ℕ) {D R : Type} [CommRing D] [CommRing R]
    (hR : IsHausdorff (Ideal.span {(p : R)}) R) (F G : AdicCompletion (Ideal.span {(p : D)}) D →+* R)
    (h : ∀ d, F (algebraMap D _ d) = G (algebraMap D _ d)) : F = G := by
  ext1 x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hR _ fun k => ?_
  rw [smodEq_iff, sub_zero]
  obtain ⟨s, z, rfl⟩ := GlobalTheory.PrincipalCompletion.dense (p : D) x k
  refine ⟨F z - G z, ?_⟩
  simp only [map_add, map_mul, map_pow, map_natCast, h]
  ring

theorem exists_lift (p : ℕ) {D P : Type} [CommRing D] [CommRing P] (I : Ideal P) (f : D →+* P)
    (h : ∀ n : ℕ, IsAdicComplete
      (Ideal.span {(p : ((Ideal.Quotient.mk (I ^ n)).comp f).range)})
      ((Ideal.Quotient.mk (I ^ n)).comp f).range) :
    ∃ j : AdicCompletion (Ideal.span {(p : D)}) D →+* AdicCompletion I P,
      (∀ d, j (algebraMap D _ d) = algebraMap P _ (f d)) ∧
      ∀ n x, ∃ d, AdicCompletion.evalₐ I n (j x) = Ideal.Quotient.mk _ (f d) := by
  choose F hF using fun n => exists_extend p (h n) ((Ideal.Quotient.mk (I ^ n)).comp f).rangeRestrict
  have hc : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp
      ((Subring.subtype _).comp (F n)) = (Subring.subtype _).comp (F m) := by
    intro m n hle
    have hm : ∀ x, (Ideal.Quotient.factorPow I hle).comp ((Subring.subtype _).comp (F n)) x ∈
        ((Ideal.Quotient.mk (I ^ m)).comp f).range := fun x => by
      obtain ⟨d, hd⟩ := (F n x).2
      refine ⟨d, ?_⟩
      simp only [RingHom.comp_apply, Subring.subtype_apply, ← hd]
      rfl
    have := extend_unique p (h m).toIsHausdorff (RingHom.codRestrict _ _ hm) (F m) fun d => by
      refine Subtype.ext ?_
      simp only [RingHom.codRestrict_apply, RingHom.comp_apply, hF]
      rfl
    rw [← this]
    rfl
  refine ⟨AdicCompletion.liftRingHom I (fun n => (Subring.subtype _).comp (F n)) hc, fun d => ?_,
    fun n x => ?_⟩
  · refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [AdicCompletion.evalₐ_liftRingHom, RingHom.comp_apply, hF]
    simp [AdicCompletion.algebraMap_apply]
  · obtain ⟨d, hd⟩ := (F n x).2
    exact ⟨d, by rw [AdicCompletion.evalₐ_liftRingHom]; exact hd.symm⟩

variable (l : ℕ) [Fact l.Prime]

theorem exists_isEps : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  refine ⟨ε, Subtype.ext ?_, fun h2 => h1 ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact this
  · have h3 := h 1
    have h4 : rootT ε 1 = 1 := h2
    rw [h4] at h3
    exact (algebraMap (Om l) ℂ_[l]).injective (by rw [← h3, map_one]; rfl)

theorem bound (n : ℕ) (s : Per.AinfP l) (hs : s ∈ Per.Acris0 l) : ∃ a : Per.Ainf l,
    (l : Per.AinfP l) ^ n * s - algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ n := by
  obtain ⟨e, he⟩ := exists_isEps l
  rw [mem_Acris0_iff_span l e he] at hs
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := hy
    rcases le_total k n with hkn | hkn
    · obtain ⟨c, hc⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l k
      have hc' : ((k.factorial : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c) =
          (l : Per.AinfP l) ^ k := by
        have h := congrArg ((algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)) hc
        rwa [map_mul, map_natCast, map_pow, map_natCast, RingHom.comp_apply] at h
      refine ⟨(l : Per.Ainf l) ^ (n - k) * Per.zA l c * xi e ^ k, ?_⟩
      have : (l : Per.AinfP l) ^ n * y = algebraMap (Per.Ainf l) (Per.AinfP l)
          ((l : Per.Ainf l) ^ (n - k) * Per.zA l c * xi e ^ k) := by
        rw [map_mul, map_mul, map_pow, map_pow, map_natCast, ← hk]
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
        rw [Nat.add_sub_cancel_left, pow_add, ← hc']
        ring
      rw [this, sub_self]
      exact zero_mem _
    · refine ⟨0, ?_⟩
      obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero).exists_left_inv
      have hy : y = u * algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ k := by
        rw [← hk, ← mul_assoc, hu, one_mul]
      rw [map_zero, sub_zero, hy, GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
        (Ideal.pow_le_pow_right hkn (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k)))
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    convert add_mem ha hb using 1
    rw [map_add]
    ring
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨c * a, ?_⟩
    convert Ideal.mul_mem_left _ (algebraMap (Per.Ainf l) (Per.AinfP l) c) ha using 1
    rw [map_mul, Algebra.smul_def]
    ring

theorem algebraMap_mem_kerTheta_pow_iff₂ (e : Per.Fl l) (he : IsEps e) (n : ℕ) (a : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ n ↔ a ∈ Ideal.span {xi e ^ n} := by
  have h1 : Per.kerP l ^ n = (Ideal.span {xi e ^ n}).map (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
    rw [GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow]
  rw [h1]
  refine ⟨fun h => ?_, Ideal.mem_map_of_mem _⟩
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (l : Per.Ainf l))] at h
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := h
  rw [Ideal.mem_span_singleton] at hk ⊢
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    refine ih ((GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l e he n).1 _ ?_)
    convert hk using 1
    ring

theorem range_complete (n : ℕ) : IsAdicComplete
    (Ideal.span {(l : ((Ideal.Quotient.mk (Per.kerP l ^ n)).comp (Per.Acris0 l).val.toRingHom).range)})
    ((Ideal.Quotient.mk (Per.kerP l ^ n)).comp (Per.Acris0 l).val.toRingHom).range := by
  obtain ⟨e, he⟩ := exists_isEps l
  let g0 : Per.Ainf l →+* ((Ideal.Quotient.mk (Per.kerP l ^ n)).comp (Per.Acris0 l).val.toRingHom).range :=
    ((Ideal.Quotient.mk (Per.kerP l ^ n)).comp (Per.Acris0 l).val.toRingHom).rangeRestrict.comp
      (algebraMap (Per.Ainf l) (Per.Acris0 l))
  have hg0 : ∀ a, (g0 a).1 = Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) := fun _ => rfl
  have hk : ∀ a, g0 a = 0 ↔ a ∈ Ideal.span {xi e ^ n} := fun a => by
    rw [← algebraMap_mem_kerTheta_pow_iff₂ l e he, ← Ideal.Quotient.eq_zero_iff_mem, ← hg0]
    exact Subtype.ext_iff
  refine complete_of_sandwich l n (GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l e he n).2
    (Ideal.Quotient.lift _ g0 fun a ha => (hk a).2 ha) ?_ ?_
  · refine RingHom.lift_injective_of_ker_le_ideal _ _ fun a ha => (hk a).1 ha
  · rintro ⟨_, s, rfl⟩
    obtain ⟨a, ha⟩ := bound l n s s.2
    refine ⟨Ideal.Quotient.mk _ a, Subtype.ext ?_⟩
    rw [Ideal.Quotient.lift_mk, hg0, ← (Ideal.Quotient.eq).2 ha, map_mul, map_pow, map_natCast,
      Subring.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
    rfl

end GlobalTheory.MemLoc.CrisMap

namespace GlobalTheory.MemLoc

theorem exists_isCrisP : ∀ (l : ℕ) [Fact l.Prime], ∃ j : Per.Acris l →+* Per.BdRp l, IsCrisP j := by
  intro l _
  obtain ⟨j, h0, h1⟩ := CrisMap.exists_lift l (Per.kerP l) (Per.Acris0 l).val.toRingHom
    (CrisMap.range_complete l)
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨e', he0, he1⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  refine ⟨e'.symm.toRingHom.comp (j.comp e.toRingHom), fun a => ?_, fun n => ⟨n, fun x => ?_⟩⟩
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [he, h0, RingEquiv.symm_apply_eq, he0]
    rfl
  · obtain ⟨d, hd⟩ := h1 n (e x)
    obtain ⟨a, ha⟩ := CrisMap.bound l n d d.2
    refine ⟨a, ?_⟩
    have h2 : Per.ev l n (e'.symm (j (e x))) = Ideal.Quotient.mk _ (d : Per.AinfP l) := by
      rw [← he1, RingEquiv.apply_symm_apply]
      exact hd
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [map_mul, map_pow, map_natCast, ← (Ideal.Quotient.eq).2 ha, map_mul, map_pow, map_natCast, h2]

end GlobalTheory.MemLoc
