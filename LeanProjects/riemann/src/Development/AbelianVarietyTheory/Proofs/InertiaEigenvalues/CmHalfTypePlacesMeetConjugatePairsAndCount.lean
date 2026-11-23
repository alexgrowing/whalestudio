import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimePlaceCmTypeConjugateStatement

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitCount

theorem locDeg_mul_ncard (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} (hl : l.Prime) :
    (placesOver E l).Finite ∧
      ∀ w ∈ placesOver E l, locDeg E w * (placesOver E l).ncard = Module.finrank ℚ E := by
  have : IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible).isPrime
  have hinj : Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 E) → _) :=
    fun _ _ h => HeightOneSpectrum.ext h
  have him : HeightOneSpectrum.asIdeal '' placesOver E l = (Ideal.span {(l : ℤ)}).primesOver (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.isPrime, GlobalTheory.HubLoc.liesOver_of_mem hl hv⟩
    · rintro ⟨hP, hlo⟩
      have hm : ((l : ℕ) : 𝓞 E) ∈ P := by
        have : (l : ℤ) ∈ P.under ℤ := by
          rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
        simpa [Ideal.under, Ideal.mem_comap] using this
      refine ⟨⟨P, hP, ?_⟩, hm, rfl⟩
      rintro rfl
      exact hl.ne_zero (by simpa using hm)
  refine ⟨Set.Finite.of_finite_image (him ▸ Algebra.QuasiFinite.finite_primesOver _) hinj.injOn, fun w hw => ?_⟩
  have := GlobalTheory.HubLoc.liesOver_of_mem hl hw
  have := w.isPrime
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(l : ℤ)}) (𝓞 E) Gal(E/ℚ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) w.asIdeal Gal(E/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(l : ℤ)}) w.asIdeal Gal(E/ℚ), ← him,
    Set.ncard_image_of_injective _ hinj, IsGalois.card_aut_eq_finrank] at h
  rw [← h, mul_comm]
  rfl

section Host
variable {R : Ranks} (H : Host R)

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  obtain ⟨φ⟩ : Nonempty (H.E →+* ℂ) := inferInstance
  apply φ.injective
  rw [GlobalTheory.SplitRowProbe.conj_sqrt, GlobalTheory.SplitRowProbe.conj_sqrt, starRingEnd_self_apply]

def cInt : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem cInt_coe (x : 𝓞 H.E) : (cInt H x : H.E) = H.conj (x : H.E) := rfl

theorem cInt_cInt (x : 𝓞 H.E) : cInt H (cInt H x) = x :=
  RingOfIntegers.ext (by rw [cInt_coe, cInt_coe, conj_conj])

def cPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  HeightOneSpectrum.comap (cInt H).toRingHom (cInt H).surjective w

theorem mem_cPl (w : HeightOneSpectrum (𝓞 H.E)) (x : 𝓞 H.E) :
    x ∈ (cPl H w).asIdeal ↔ cInt H x ∈ w.asIdeal := Iff.rfl

theorem cPl_cPl (w : HeightOneSpectrum (𝓞 H.E)) : cPl H (cPl H w) = w :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cPl, mem_cPl, cInt_cInt])

theorem isConjPl_cPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (cPl H w) := by
  intro x y h
  have : y = cInt H x := RingOfIntegers.ext h
  rw [this, mem_cPl, cInt_cInt]

theorem mem_placesOver_of_conj {l : ℕ} {w w' : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E l)
    (h : IsConjPl H w w') : w' ∈ placesOver H.E l :=
  (h (l : 𝓞 H.E) (l : 𝓞 H.E) (by simp)).1 hw

end Host

theorem columns_count : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ s : Bool, (∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' → Xor' (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s)) ∧ (columns (N := D.nd) D.nbr i s).Finite ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), locDeg D.host.E w * (columns (N := D.nd) D.nbr i s).ncard = D.R.f := by
  intro D i hl s
  have hx : ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor' (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
    intro w hw w' h
    have hw' := mem_placesOver_of_conj D.host hw h
    have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
    have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
    rcases GlobalTheory.T.splitPrime_place_cmType_conjugate D i hl w w' hw hw' h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩
  have hgal := D.host.hostE_isGalois
  obtain ⟨hfin, hdeg⟩ := locDeg_mul_ncard D.host.E hl.1
  set C := columns (N := D.nd) D.nbr i s with hC
  have hsub : C ⊆ placesOver D.host.E (D.nd.l i) := fun w ⟨hw, _⟩ => hw
  have hCf : C.Finite := hfin.subset hsub
  refine ⟨hx, hCf, fun w hw => ?_⟩
  have hinj : Function.Injective (cPl D.host) := Function.LeftInverse.injective (cPl_cPl D.host)
  have hun : placesOver D.host.E (D.nd.l i) = C ∪ cPl D.host '' C := by
    ext v
    constructor
    · intro hv
      rcases hx v hv _ (isConjPl_cPl D.host v) with h | h
      · exact Or.inl h.1
      · exact Or.inr ⟨_, h.1, cPl_cPl D.host v⟩
    · rintro (hv | ⟨u, hu, rfl⟩)
      · exact hsub hv
      · exact mem_placesOver_of_conj D.host (hsub hu) (isConjPl_cPl D.host u)
  have hdis : Disjoint C (cPl D.host '' C) := by
    rw [Set.disjoint_left]
    rintro _ hv ⟨u, hu, rfl⟩
    rcases hx u (hsub hu) _ (isConjPl_cPl D.host u) with h | h
    · exact h.2 hv
    · exact h.2 hu
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have h := hdeg w hw
  rw [hun, Set.ncard_union_eq hdis hCf (hCf.image _), Set.ncard_image_of_injective _ hinj, hfr] at h
  have h2 : 2 * (locDeg D.host.E w * C.ncard) = 2 * D.R.f := by rw [← h]; ring
  omega

end GlobalTheory.SplitCount

end
