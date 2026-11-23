import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicFormValuesNearPointSpecStatement

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.UpDia

section Local
variable {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]

theorem inc_dil {res : R →+* k} (hs : Function.Surjective res) {t : R} {p q : Pr R V k} (hp : p.Ok res)
    (h : Pr.Inc res t p q) {a : k} (ha : a ≠ 0) : Pr.Inc res t (p.dil a) (q.dil a) := by
  obtain ⟨h1, h2, e, h3, h4⟩ := h
  obtain ⟨b, hb⟩ := hs a⁻¹
  have he : e ∈ q.L := by
    by_contra hn
    rw [h1.off _ hn] at h3
    exact zero_ne_one h3
  have hte : t • e ∈ p.L := by
    by_contra hn
    rw [hp.off _ hn] at h4
    exact zero_ne_one h4
  refine ⟨h1.dil ha, fun y => ?_, b • e, ?_, ?_⟩
  · show y ∈ p.L ↔ y ∈ q.L ∧ a * q.f y = 0
    rw [h2 y, mul_eq_zero, or_iff_right ha]
  · show a * q.f _ = 1
    rw [h1.smul _ _ he, h3, hb, mul_one, mul_inv_cancel₀ ha]
  · show a * p.f _ = 1
    rw [smul_comm, hp.smul _ _ hte, h4, hb, mul_one, mul_inv_cancel₀ ha]

theorem inc_dil_iff {res : R →+* k} (hs : Function.Surjective res) {t : R} {p : Pr R V k} (hp : p.Ok res)
    (q : Pr R V k) {a : k} (ha : a ≠ 0) : Pr.Inc res t (p.dil a) (q.dil a) ↔ Pr.Inc res t p q := by
  refine ⟨fun h => ?_, fun h => inc_dil hs hp h ha⟩
  have := inc_dil hs (hp.dil ha) h (inv_ne_zero ha)
  rwa [Pr.dil_dil, Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one, Pr.dil_one] at this

def dilEquiv {a : k} (ha : a ≠ 0) : Pr R V k ≃ Pr R V k where
  toFun q := q.dil a
  invFun q := q.dil a⁻¹
  left_inv q := by
    show (q.dil a).dil a⁻¹ = q
    rw [Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one]
  right_inv q := by
    show (q.dil a⁻¹).dil a = q
    rw [Pr.dil_dil, mul_inv_cancel₀ ha, Pr.dil_one]

end Local

theorem atV_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J}
    (h : AtV v η) (δ : GA σ J) : AtV v (δ⁻¹ * η * δ) := by
  intro v' hv'
  have h1 := h v' hv'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h1, mul_one, inv_mul_cancel]

theorem upAd_dia : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E), Function.Surjective res → (∀ x, (p x).Ok res) → ∀ g ∈ AdFun S emb, ∀ (v' : HeightOneSpectrum (𝓞 F)) (hv' : (T : 𝓞 F) ∈ v'.asIdeal) (a : ℤ) (δ : GA σ J), v' ∉ bad → (v' = v → (a : k) ≠ 0) → IsDia S v' hv' a δ → ∀ x, upAd res t v p (fun y => g (y * δ)) x = upAd res t v p g (x * δ) := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hP res t hs hok g hg v' hv' a δ hb' ha hδ x
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.adelicForm_values_near_point_spec F E σ n J T f bad ι S emb v hv k p hb hP g hg
  by_cases hvv : v' = v
  · subst hvv
    have ha' := ha rfl
    unfold upAd
    rw [hP.2.2 x δ a hδ, h2 x δ hδ.1]
    refine finsum_mem_eq_of_bijOn (fun q => q.dil (a : k)) ?_ (fun q _ => (h3 a δ x q ha' hδ).symm)
    refine (dilEquiv ha').bijOn' ?_ ?_
    · intro q hq
      exact inc_dil hs (hok x) hq ha'
    · intro q hq
      have := inc_dil hs ((hok x).dil ha') hq (inv_ne_zero ha')
      rw [Pr.dil_dil, inv_mul_cancel₀ ha', Pr.dil_one] at this
      exact this
  · have hp : ∀ y, p (y * δ) = p y := fun y => (hP.2.1 y δ).2 (by
      rw [hδ.1 v (Ne.symm hvv)]; exact one_mem _)
    have key : valAt v p (fun y => g (y * δ)) x = valAt v p g (x * δ) := by
      funext q
      by_cases h : ∃ η, AtV v η ∧ p (x * η) = q
      · have hc := h.choose_spec
        have e : x * δ * (δ⁻¹ * h.choose * δ) = x * h.choose * δ := by group
        have := h1 (x * δ) _ (atV_conj hc.1 δ)
        rw [e, hp, hc.2] at this
        rw [this]
        unfold valAt
        rw [dif_pos h]
      · have h' : ¬ ∃ η, AtV v η ∧ p (x * δ * η) = q := by
          rintro ⟨η, hη, hq⟩
          refine h ⟨δ⁻¹⁻¹ * η * δ⁻¹, atV_conj hη _, ?_⟩
          rw [← hp, ← hq]
          congr 1
          group
        unfold valAt
        rw [dif_neg h, dif_neg h']
    unfold upAd
    rw [hp, key]

end GlobalTheory.LevelHecke.UpDia
