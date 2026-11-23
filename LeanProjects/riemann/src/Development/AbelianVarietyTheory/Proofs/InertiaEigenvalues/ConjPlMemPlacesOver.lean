import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo

noncomputable section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypePlaceCover

variable {R : Ranks} (H : Host R)

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [H.toHostAx.conjE_apply, H.toHostAx.conjE_apply, Complex.conj_conj]

def conjInt : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)

theorem conjInt_coe (x : 𝓞 H.E) : (conjInt H x : H.E) = H.conj x := rfl

theorem conjInt_conjInt (x : 𝓞 H.E) : conjInt H (conjInt H x) = x :=
  RingOfIntegers.ext (by rw [conjInt_coe, conjInt_coe, conj_conj])

def conjPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  ⟨w.asIdeal.comap (conjInt H), haveI := w.isPrime; Ideal.comap_isPrime _ _, fun h0 => w.ne_bot (by
    rw [eq_bot_iff]
    intro x hx
    have : conjInt H x ∈ w.asIdeal.comap (conjInt H) := by rwa [Ideal.mem_comap, conjInt_conjInt]
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot, ← conjInt_conjInt H x, this, map_zero])⟩

theorem mem_conjPl (w : HeightOneSpectrum (𝓞 H.E)) (x : 𝓞 H.E) :
    x ∈ (conjPl H w).asIdeal ↔ conjInt H x ∈ w.asIdeal := Iff.rfl

theorem conjPl_conjPl (w : HeightOneSpectrum (𝓞 H.E)) : conjPl H (conjPl H w) = w :=
  HeightOneSpectrum.ext (by ext x; rw [mem_conjPl, mem_conjPl, conjInt_conjInt])

theorem isConjPl_conjPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (conjPl H w) := by
  intro x y hxy
  have : y = conjInt H x := RingOfIntegers.ext hxy
  rw [mem_conjPl, this, conjInt_conjInt]

theorem conjPl_mem_placesOver {p : ℕ} {w : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E p) :
    conjPl H w ∈ placesOver H.E p := by
  show conjInt H _ ∈ w.asIdeal
  rw [map_natCast]; exact hw

theorem finrank_eq : Module.finrank ℚ H.E = 2 * R.f := by
  have h1 : Module.finrank ℚ H.E = 4 * R.ord := H.finrank_cmField
  have h5 : R.f = 2 * R.ord := rfl
  rw [h1, h5]; ring

theorem place_cover : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k),
    ∃ v : D.nd.PlG k, w = D.naut.plGw k v ∨ IsConjPl D.host (D.naut.plGw k v) w := by
  intro D k w hw
  have hne : ∀ v v' : D.nd.PlG k, D.naut.plGw k v ≠ conjPl D.host (D.naut.plGw k v') := fun v v' e =>
    D.naut.plGw_nconj k v' v (e ▸ isConjPl_conjPl _ _)
  let f : D.nd.PlG k ⊕ D.nd.PlG k → placesOver D.host.E (D.host.g k) :=
    Sum.elim (fun v => ⟨D.naut.plGw k v, D.naut.plGw_over k v⟩)
      fun v => ⟨conjPl D.host (D.naut.plGw k v), conjPl_mem_placesOver _ (D.naut.plGw_over k v)⟩
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) e <;> have e' := congrArg Subtype.val e
    · rw [D.naut.plGw_inj k e']
    · exact absurd e' (hne a b)
    · exact absurd e'.symm (hne b a)
    · have := congrArg (conjPl D.host) e'
      simp only [f, Sum.elim_inr, conjPl_conjPl] at this
      rw [D.naut.plGw_inj k this]
  have hc : Nat.card (placesOver D.host.E (D.host.g k)) = Nat.card (D.nd.PlG k ⊕ D.nd.PlG k) := by
    rw [Nat.card_coe_set_eq, D.nd.g_split k, finrank_eq, Nat.card_sum, Nat.card_eq_fintype_card, D.nd.card_PlG k, two_mul]
  haveI : Finite (placesOver D.host.E (D.host.g k)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_coe_set_eq, D.nd.g_split k]
    exact Module.finrank_pos.ne'
  obtain ⟨x, hx⟩ := ((Nat.bijective_iff_injective_and_card f).2 ⟨hinj, hc.symm⟩).2 ⟨w, hw⟩
  rcases x with v | v
  · exact ⟨v, Or.inl (congrArg Subtype.val hx).symm⟩
  · refine ⟨v, Or.inr ?_⟩
    have e : conjPl D.host (D.naut.plGw k v) = w := congrArg Subtype.val hx
    exact e ▸ isConjPl_conjPl _ _

end GlobalTheory.TypePlaceCover
