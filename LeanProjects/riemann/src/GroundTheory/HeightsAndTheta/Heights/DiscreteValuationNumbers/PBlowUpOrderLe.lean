import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOrderLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem subring_map_maximal_cases {D : Type*} [CommRing D] [IsLocalRing D] (C : Subring D)
    (hC : IsLocalRing.maximalIdeal D ≤ ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (m : Ideal C) (hm : m.IsMaximal) :
    m.map C.subtype = ⊤ ∨ IsLocalRing.maximalIdeal D ≤ m.map C.subtype := by
  by_cases h : m ≤ (IsLocalRing.maximalIdeal D).comap C.subtype
  · right
    rw [hm.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal D).ne_top) h]
    exact hC
  · left
    obtain ⟨c, hcm, hc⟩ := Set.not_subset.mp h
    have hu : IsUnit (C.subtype c) := by
      by_contra hnu
      exact hc (IsLocalRing.mem_maximalIdeal _ |>.mpr hnu)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hcm) hu

theorem length_quot_le_of_subring (h₂ : LengthMapIdealLe.Statement.{u})
    (h₃ : IntermediateRingQuotLength.Statement.{u}) {A D : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing D] [IsDomain D] [IsLocalRing D] (hdim : ringKrullDim A = 1)
    (C : Subring D) (f : A →+* C) (hfinj : Function.Injective f)
    (hfrac : ∀ c : C, ∃ a, a ≠ 0 ∧ f a * c ∈ Set.range f)
    (hmax : IsLocalRing.maximalIdeal D ≤
      ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (a : A) (ha : a ≠ 0) :
    Module.length D (D ⧸ Ideal.span {(f a : D)}) ≤ Module.length A (A ⧸ Ideal.span {a}) := by
  let _ : Algebra A C := f.toAlgebra
  have s3 := h₃ A C hdim hfinj
    (fun c => by
      obtain ⟨b, hb, hbc⟩ := hfrac c
      exact ⟨b, hb, by rw [Algebra.smul_def]; exact hbc⟩) a ha
  have s2 : Module.length C (C ⧸ Ideal.span {algebraMap A C a}) ≤
      Module.length A (C ⧸ Ideal.span {algebraMap A C a}) := by
    have h := Submodule.length_le_length_restrictScalars A
      (⊤ : Submodule C (C ⧸ Ideal.span {algebraMap A C a}))
    rwa [Submodule.restrictScalars_top, Module.length_top, Module.length_top] at h
  have s1 := h₂ C D C.subtype (subring_map_maximal_cases C hmax) (Ideal.span {algebraMap A C a})
  rw [Ideal.map_span, Set.image_singleton] at s1
  exact s1.trans (s2.trans s3)

theorem BlowUpOrderLe.proof (h₁ : LocalizedQuotLength.Statement.{u})
    (h₂ : LengthMapIdealLe.Statement.{u}) (h₃ : IntermediateRingQuotLength.Statement.{u})
    (h₄ : BlowUpLocalChart.Statement.{u}) : BlowUpOrderLe.Statement.{u} := by
  intro R _ _ K _ ι _ J _ P hP u G' y hy hG' hrel x hx hG z hz
  have hGp : G'.IsPrime := hG'.1.1
  obtain ⟨G₀, W₀, hG₀p, hW₀p, hG₀, hW₀⟩ := BlowUpLocalChart.exists_quotient_primes hGp
    (le_sup_left.trans hG'.1.2) (le_sup_left.trans hG.1.2)
  have hRHS0 : (0 : ℤ) ≤ divCycle P z (G'.comap (liftForm (J := J))) := by
    unfold divCycle
    split_ifs <;> positivity
  by_cases hL : G' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm z}).minimalPrimes ∧ IsRelevant G'
  swap
  · have h0 : divCycle (blowUpOf P u) (liftForm z) G' = 0 := by
      unfold divCycle
      rw [dif_neg hL]
    rw [h0]
    exact hRHS0
  have hzG : z ∈ G'.comap (liftForm (J := J)) :=
    hL.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hcp : (G'.comap (liftForm (J := J))).IsPrime := hG.1.1
  have hRmin : G'.comap (liftForm (J := J)) ∈ (P ⊔ Ideal.span {z}).minimalPrimes := by
    have h := mem_minimalPrimes_sup_span_mul (P := P) (W := G'.comap (liftForm (J := J))) hz hG
    refine ⟨⟨hcp, sup_le (le_sup_left.trans hG.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hzG)⟩, ?_⟩
    intro q hq hqG
    refine h.2 ⟨hq.1, sup_le (le_sup_left.trans hq.2) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hqG
    exact q.mul_mem_left x (hq.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self z)))
  have hRrel : IsRelevant (G'.comap (liftForm (J := J))) := by
    intro k
    obtain ⟨i, hi⟩ := hL.2 (some k)
    refine ⟨i, fun hmem => hi ?_⟩
    rw [Ideal.mem_comap] at hmem
    simpa [liftForm, rename_X] using hmem
  have hfin := length_localizedQuot_ne_top (P ⊔ Ideal.span {z}) (G'.comap (liftForm (J := J))) hRmin
  unfold divCycle
  rw [dif_pos hL, dif_pos ⟨hRmin, hRrel⟩]
  suffices key : multAt (blowUpOf P u ⊔ Ideal.span {liftForm z}) G' ≤
      multAt (P ⊔ Ideal.span {z}) (G'.comap (liftForm (J := J))) by
    exact_mod_cast ENat.toNat_le_toNat key hfin

  obtain ⟨C, f, hfinj, hfrac, hfcompat, hmax⟩ := h₄ R K ι J P hP u G' y hy hG' hrel x hx hG G₀ hG₀ W₀ hW₀
  have hQp : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  have hSn : IsNoetherianRing (MRing ι R ⧸ P) := inferInstance
  have hAn : IsNoetherianRing (Localization.AtPrime G₀) :=
    IsLocalization.isNoetherianRing G₀.primeCompl _ hSn
  have hAinj : Function.Injective (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀)) :=
    IsLocalization.injective (Localization.AtPrime G₀) (Ideal.primeCompl_le_nonZeroDivisors G₀)
  have hdim : ringKrullDim (Localization.AtPrime G₀) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height G₀ (Localization.AtPrime G₀)]
    have hmap : (G'.comap (liftForm (J := J))).map (Ideal.Quotient.mk P) = G₀ := by
      rw [← hG₀, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have hle : G₀.height ≤ 1 := hmap ▸ Ideal.map_height_le_one_of_mem_minimalPrimes hG
    have hne : G₀.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro hbot
      have hxG : Ideal.Quotient.mk P x ∈ G₀ := by
        rw [← Ideal.mem_comap, hG₀]
        exact hG.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
      rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hxG
      exact hx hxG
    have h1 : G₀.height = 1 := le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
    rw [h1]
    rfl
  set a : Localization.AtPrime G₀ :=
    algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀) (Ideal.Quotient.mk P z) with ha_def
  have ha : a ≠ 0 := by
    intro h0
    rw [ha_def, ← map_zero (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀))] at h0
    exact hz (Ideal.Quotient.eq_zero_iff_mem.mp (hAinj h0))
  have hDom : IsDomain (Localization.AtPrime W₀) := inferInstance
  have hchain := length_quot_le_of_subring h₂ h₃ hdim C f hfinj hfrac hmax a ha
  rw [ha_def, hfcompat z] at hchain
  have e₁ := h₁ (MRing (extIdx ι J) R) (blowUpOf P u) W₀ (liftForm z)
  have e₂ := h₁ (MRing ι R) P G₀ z
  have key : ∀ (H : Ideal (MRing (extIdx ι J) R)) [H.IsPrime] (G : Ideal (MRing ι R)) [G.IsPrime],
      W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = H → G₀.comap (Ideal.Quotient.mk P) = G →
      multAt (blowUpOf P u ⊔ Ideal.span {liftForm z}) H ≤ multAt (P ⊔ Ideal.span {z}) G := by
    intro H _ G _ hH hGG
    subst hH
    subst hGG
    unfold multAt
    exact e₁.le.trans (hchain.trans e₂.ge)
  exact key _ _ hW₀ hG₀

end

end GroundTheory.Heights₂.Heights.NumbersDVR
