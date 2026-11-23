import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.TypePlacesExhaust

variable {R : Ranks} (H : Host R)

def cInt : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

def conjPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  HeightOneSpectrum.comap ((cInt H).symm : 𝓞 H.E →+* 𝓞 H.E) (cInt H).symm.surjective w

variable {H}

theorem mem_conjPl (w : HeightOneSpectrum (𝓞 H.E)) (y : 𝓞 H.E) :
    y ∈ (conjPl H w).asIdeal ↔ (cInt H).symm y ∈ w.asIdeal := Iff.rfl

theorem isConjPl_conjPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (conjPl H w) := by
  intro x y hy
  have e : y = cInt H x := RingOfIntegers.ext (by rw [hy]; rfl)
  subst e
  rw [mem_conjPl, RingEquiv.symm_apply_apply]

theorem conjPl_injective : Function.Injective (conjPl H) := by
  intro w w' h
  apply HeightOneSpectrum.ext
  ext x
  have := congrArg (fun u : HeightOneSpectrum (𝓞 H.E) => cInt H x ∈ u.asIdeal) h
  simp only [mem_conjPl, RingEquiv.symm_apply_apply] at this
  exact Iff.of_eq this

theorem conjPl_mem_placesOver {p : ℕ} {w : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E p) :
    conjPl H w ∈ placesOver H.E p := by
  show ((p : ℕ) : 𝓞 H.E) ∈ (conjPl H w).asIdeal
  rw [mem_conjPl, map_natCast]
  exact hw

theorem finrank_E (H : Host R) : Module.finrank ℚ H.E = 2 * R.f := by
  rw [H.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring_nf

theorem eq_plGw_or_isConjPl : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k),
    ∃ v : D.nd.PlG k, w = D.naut.plGw k v ∨ IsConjPl D.host (D.naut.plGw k v) w := by
  intro D k w hw
  classical
  set S := placesOver D.host.E (D.host.g k) with hSdef
  set A : Set (HeightOneSpectrum (𝓞 D.host.E)) := D.naut.plGw k '' Set.univ with hAdef
  set B : Set (HeightOneSpectrum (𝓞 D.host.E)) := conjPl D.host '' A with hBdef
  have hAS : A ⊆ S := by
    rintro _ ⟨v, -, rfl⟩
    exact D.naut.plGw_over k v
  have hBS : B ⊆ S := by
    rintro _ ⟨u, hu, rfl⟩
    exact conjPl_mem_placesOver (hAS hu)
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, -, rfl⟩ ⟨_, ⟨v', -, rfl⟩, h⟩
    exact D.naut.plGw_nconj k v' v (h ▸ isConjPl_conjPl _)
  have hS : S.ncard = 2 * D.R.f := by rw [hSdef, D.nd.g_split k, finrank_E]
  have hSfin : S.Finite := Set.finite_of_ncard_pos (by rw [hS]; unfold Ranks.f Ranks.n; positivity)
  have hA : A.ncard = D.R.f := by
    rw [hAdef, Set.ncard_image_of_injective _ (D.naut.plGw_inj k), Set.ncard_univ, Nat.card_eq_fintype_card,
      D.nd.card_PlG k]
  have hB : B.ncard = D.R.f := by
    rw [hBdef, Set.ncard_image_of_injective _ conjPl_injective, hA]
  have hAfin : A.Finite := hSfin.subset hAS
  have hBfin : B.Finite := hSfin.subset hBS
  have hU : A ∪ B = S := Set.eq_of_subset_of_ncard_le (Set.union_subset hAS hBS)
    (by rw [Set.ncard_union_eq hdisj hAfin hBfin, hA, hB, hS]; ring_nf; rfl) hSfin
  rw [← hU] at hw
  rcases hw with ⟨v, -, rfl⟩ | ⟨_, ⟨v, -, rfl⟩, rfl⟩
  · exact ⟨v, Or.inl rfl⟩
  · exact ⟨v, Or.inr (isConjPl_conjPl _)⟩

end GlobalTheory.TypePlacesExhaust
