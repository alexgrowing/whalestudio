import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LengthLocalizedModuleQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PFFibreMultProof

theorem length_quot_map_of_surjective {L L' : Type*} [CommRing L] [CommRing L'] (θ : L →+* L')
    (hθ : Function.Surjective θ) (I : Ideal L) (hker : RingHom.ker θ ≤ I) :
    Module.length L' (L' ⧸ I.map θ) = Module.length L (L ⧸ I) := by
  have hk : RingHom.ker ((Ideal.Quotient.mk (I.map θ)).comp θ) = I := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hker
  let τ : L ⧸ I ≃+* L' ⧸ I.map θ := (Ideal.quotEquivOfEq hk.symm).trans
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp hθ))
  have e1 : Module.length L (L ⧸ I) = Module.length (L ⧸ I) (L ⧸ I) :=
    Module.length_eq_of_surjective (by exact Ideal.Quotient.mk_surjective)
  have e2 : Module.length L' (L' ⧸ I.map θ) = Module.length (L' ⧸ I.map θ) (L' ⧸ I.map θ) :=
    Module.length_eq_of_surjective (by exact Ideal.Quotient.mk_surjective)
  rw [e1, e2, ObjectsChow.VerticalPartMultiplicity.length_self_eq_of_ringEquiv τ]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem baseSubst_rename (hv : IsBlockMap κ v) (G : GenFibre v P') (t : MRing ι) :
    baseSubst κ G (rename v t) = C (aeval G.x t) := by
  have h : (baseSubst κ G).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom =
      (C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [show (C r : MRing ι) = (r : MRing ι) from eq_intCast C r, map_intCast]
    · intro p
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]
      unfold baseSubst
      rw [eval₂Hom_X']
      have h1 : (v p).1 ∈ Set.range κ := ⟨p.1, (hv.2.2.1 p).symm⟩
      have h2 : v p ∈ Set.range v := ⟨p, rfl⟩
      rw [dif_pos h1, dif_pos h2, hv.2.1 h2.choose_spec]
  exact DFunLike.congr_fun h t

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem baseSubst_X_fib (G : GenFibre v P') (q : Σ k : FibreBlock κ, ι' k.1) :
    baseSubst κ G (X ⟨q.1.1, q.2⟩) = X q := by
  unfold baseSubst
  rw [eval₂Hom_X', dif_neg q.1.2]

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem exists_baseSubst_mul (hv : IsBlockMap κ v) (G : GenFibre v P') (g : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (t : MRing ι) (f : MRing ι'), aeval G.x t ≠ 0 ∧ baseSubst κ G (rename v t) * g = baseSubst κ G f := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    obtain ⟨f, t, ht, rfl⟩ := G.gen c
    refine ⟨t, rename v f, ht, ?_⟩
    rw [baseSubst_rename hv, baseSubst_rename hv, ← C_mul]
    congr 1
    field_simp
  | add g₁ g₂ h₁ h₂ =>
    obtain ⟨t₁, f₁, ht₁, e₁⟩ := h₁
    obtain ⟨t₂, f₂, ht₂, e₂⟩ := h₂
    refine ⟨t₁ * t₂, f₁ * rename v t₂ + rename v t₁ * f₂, by rw [map_mul]; exact mul_ne_zero ht₁ ht₂, ?_⟩
    rw [map_mul, map_mul, map_add, map_mul, map_mul, ← e₁, ← e₂]
    ring
  | mul_X g q h =>
    obtain ⟨t, f, ht, e⟩ := h
    refine ⟨t, f * X ⟨q.1.1, q.2⟩, ht, ?_⟩
    rw [map_mul, ← e, baseSubst_X_fib]
    ring

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem isUnit_baseSubst_rename (hv : IsBlockMap κ v) (G : GenFibre v P') {t : MRing ι} (ht : aeval G.x t ≠ 0) :
    IsUnit (baseSubst κ G (rename v t)) := by
  rw [baseSubst_rename hv]
  exact (isUnit_iff_ne_zero.mpr ht).map C

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem ker_baseSubst_le (hv : IsBlockMap κ v) (G : GenFibre v P') : RingHom.ker (baseSubst κ G) ≤ P' := by
  intro a ha
  rw [RingHom.mem_ker] at ha
  rw [← G.genericFibre_ker_target, RingHom.mem_ker, ← aeval_baseSubst hv, ha, map_zero]

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem fibreIdeal_eq_map (hv : IsBlockMap κ v) (G : GenFibre v P') :
    fibreIdeal κ G = P'.map (baseSubst κ G) := by
  apply le_antisymm
  · intro g hg
    rw [fibreIdeal, RingHom.mem_ker] at hg
    obtain ⟨t, f, ht, e⟩ := exists_baseSubst_mul hv G g
    have hf : f ∈ P' := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker, ← aeval_baseSubst hv, ← e, map_mul, hg, mul_zero]
    rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_baseSubst_rename hv G ht), e]
    exact Ideal.mem_map_of_mem _ hf
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]
    exact ha

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem exists_of_mem_map (hv : IsBlockMap κ v) (G : GenFibre v P') (W : Ideal (MRing ι'))
    {g : MRingOver G.Φ (fibreIdx ι' κ)} (hg : g ∈ W.map (baseSubst κ G)) :
    ∃ (t : MRing ι) (w : MRing ι'), aeval G.x t ≠ 0 ∧ w ∈ W ∧
      baseSubst κ G (rename v t) * g = baseSubst κ G w := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨1, w, by simp, hw, by simp⟩
  | zero => exact ⟨1, 0, by simp, W.zero_mem, by simp⟩
  | add g₁ g₂ _ _ h₁ h₂ =>
    obtain ⟨t₁, w₁, ht₁, hw₁, e₁⟩ := h₁
    obtain ⟨t₂, w₂, ht₂, hw₂, e₂⟩ := h₂
    refine ⟨t₁ * t₂, w₁ * rename v t₂ + rename v t₁ * w₂, by rw [map_mul]; exact mul_ne_zero ht₁ ht₂,
      W.add_mem (W.mul_mem_right _ hw₁) (W.mul_mem_left _ hw₂), ?_⟩
    rw [map_mul, map_mul, map_add, map_mul, map_mul, ← e₁, ← e₂]
    ring
  | smul c g _ h =>
    obtain ⟨t, w, ht, hw, e⟩ := h
    obtain ⟨t', f, ht', e'⟩ := exists_baseSubst_mul hv G c
    refine ⟨t' * t, f * w, by rw [map_mul]; exact mul_ne_zero ht' ht, W.mul_mem_left _ hw, ?_⟩
    rw [smul_eq_mul, map_mul, map_mul, map_mul, ← e, ← e']
    ring

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem comap_fibreOf_and_isPrime (hv : IsBlockMap κ v) (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime]
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') :
    (fibreOf κ G W).comap (baseSubst κ G) = W ∧ (fibreOf κ G W).IsPrime := by
  have htW : ∀ t : MRing ι, aeval G.x t ≠ 0 → rename v t ∉ W := by
    intro t ht h
    have h' : t ∈ imageZ v W := h
    rw [hI, ← G.ker_x, RingHom.mem_ker] at h'
    exact ht h'
  have hc : (fibreOf κ G W).comap (baseSubst κ G) = W := by
    refine le_antisymm (fun a ha => ?_) Ideal.le_comap_map
    obtain ⟨t, w, ht, hw, e⟩ := exists_of_mem_map hv G W ha
    have hk : rename v t * a - w ∈ W := by
      apply hPW
      apply ker_baseSubst_le hv G
      rw [RingHom.mem_ker, map_sub, map_mul, e, sub_self]
    have hta : rename v t * a ∈ W := by simpa using W.add_mem hk hw
    exact ((Ideal.IsPrime.mem_or_mem ‹_› hta).resolve_left (htW t ht))
  refine ⟨hc, Ideal.isPrime_iff.mpr ⟨fun h => ?_, fun {g₁ g₂} h => ?_⟩⟩
  · have h1 : (1 : MRing ι') ∈ W := by
      rw [← hc, Ideal.mem_comap, map_one, h]
      exact Submodule.mem_top
    exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one W).mpr h1)
  · obtain ⟨t₁, f₁, ht₁, e₁⟩ := exists_baseSubst_mul hv G g₁
    obtain ⟨t₂, f₂, ht₂, e₂⟩ := exists_baseSubst_mul hv G g₂
    have hf : f₁ * f₂ ∈ W := by
      rw [← hc, Ideal.mem_comap, map_mul, ← e₁, ← e₂,
        show baseSubst κ G (rename v t₁) * g₁ * (baseSubst κ G (rename v t₂) * g₂) =
          baseSubst κ G (rename v t₁) * baseSubst κ G (rename v t₂) * (g₁ * g₂) by ring]
      exact Ideal.mul_mem_left _ _ h
    rcases Ideal.IsPrime.mem_or_mem ‹_› hf with hf | hf
    · left
      rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_baseSubst_rename hv G ht₁), e₁, ← Ideal.mem_comap, hc]
      exact hf
    · right
      rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_baseSubst_rename hv G ht₂), e₂, ← Ideal.mem_comap, hc]
      exact hf

end PFFibreMultProof

open PFFibreMultProof

theorem PFFibreMult.proof : PFFibreMult.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d e G s W hv hP' hP hW hH hI
  classical
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
  obtain ⟨hc, hQ⟩ := comap_fibreOf_and_isPrime hv G W hPW hI
  have := hQ
  set φ := baseSubst κ G with hφ
  have hWQ : W = (fibreOf κ G W).comap φ := hc.symm
  let θ := Localization.localRingHom W (fibreOf κ G W) φ hWQ
  have hcomp : θ.comp (algebraMap (MRing ι') (Localization.AtPrime W)) =
      (algebraMap _ (Localization.AtPrime (fibreOf κ G W))).comp φ :=
    RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ hWQ z
  have hsurj : Function.Surjective θ := by
    intro y
    obtain ⟨⟨g, h⟩, rfl⟩ := IsLocalization.mk'_surjective (fibreOf κ G W).primeCompl y
    obtain ⟨t, f, ht, e⟩ := exists_baseSubst_mul hv G g
    obtain ⟨t', f', ht', e'⟩ := exists_baseSubst_mul hv G (h : MRingOver G.Φ (fibreIdx ι' κ))
    have htW : ∀ t : MRing ι, aeval G.x t ≠ 0 → rename v t ∉ W := by
      intro t ht h
      have h' : t ∈ imageZ v W := h
      rw [hI, ← G.ker_x, RingHom.mem_ker] at h'
      exact ht h'
    have hf' : f' ∉ W := by
      intro hf'
      apply h.2
      have h1 : φ f' ∈ fibreOf κ G W := by rw [← Ideal.mem_comap, hc]; exact hf'
      rwa [← e', Ideal.unit_mul_mem_iff_mem _ (isUnit_baseSubst_rename hv G ht')] at h1
    have hden : rename v t * f' ∈ W.primeCompl := fun hm =>
      (Ideal.IsPrime.mem_or_mem hWp hm).elim (htW t ht) hf'
    refine ⟨IsLocalization.mk' _ (f * rename v t') ⟨rename v t * f', hden⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [map_mul]
    rw [← e, ← e']
    ring
  have hker : RingHom.ker θ ≤ (P' ⊔ Ideal.span {s}).map (algebraMap (MRing ι') (Localization.AtPrime W)) := by
    intro z hz
    obtain ⟨⟨a, w⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
    rw [RingHom.mem_ker, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨⟨c, hc'⟩, hc0⟩ := hz
    have hcne : c ≠ 0 := fun h0 => hc' (h0 ▸ (fibreOf κ G W).zero_mem)
    have ha : φ a = 0 := (mul_eq_zero.mp hc0).resolve_left hcne
    have haJ : a ∈ P' ⊔ Ideal.span {s} := Ideal.mem_sup_left (ker_baseSubst_le hv G (RingHom.mem_ker.mpr ha))
    change IsLocalization.mk' (Localization.AtPrime W) a w ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ haJ)
  have hJ : (fibreIdeal κ G ⊔ Ideal.span {φ s}).map (algebraMap _ (Localization.AtPrime (fibreOf κ G W))) =
      ((P' ⊔ Ideal.span {s}).map (algebraMap (MRing ι') (Localization.AtPrime W))).map θ := by
    have hJ0 : fibreIdeal κ G ⊔ Ideal.span {φ s} = (P' ⊔ Ideal.span {s}).map φ := by
      rw [fibreIdeal_eq_map hv G, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    rw [hJ0, Ideal.map_map, Ideal.map_map, hcomp]
  unfold multAt
  rw [dif_pos hQ, dif_pos hWp, ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient, hJ,
    length_quot_map_of_surjective θ hsurj _ hker]

end

end GroundTheory.Heights₂.Heights.Inter
