import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.SeamExp

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem conjP_seamP {D : D7} {X : Fields} (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    conjPrime₂ (seamP s P) = seamP s (conjPrime₂ P) := by
  ext y
  obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective y
  rw [mem_conjP, mem_seamP, mem_conjP]
  have h : cO D.host.E (RingOfIntegers.mapRingEquiv s.iE x) = RingOfIntegers.mapRingEquiv s.iE (cO X.E x) := by
    apply RingOfIntegers.ext
    show star (s.iE (x : X.E)) = s.iE (star (x : X.E))
    rw [hs.2, star_eq_conj]
  rw [h, mem_seamP]

theorem expS_seam : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (P : HeightOneSpectrum (𝓞 X.E)), expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (seamP s P) = expS SS P := by
  intro D X s hs SS P
  have hm : ∀ Q, seamP s Q ∈ SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding ↔ Q ∈ SS :=
    fun Q => Finset.mem_map' _
  have h1 := hm P
  have h2 := hm (conjPrime₂ P)
  rw [← conjP_seamP s hs] at h2
  unfold expS
  by_cases hP : P ∈ SS
  · rw [if_pos (h1.2 hP), if_pos hP]
  · rw [if_neg (fun h => hP (h1.1 h)), if_neg hP]
    by_cases hQ : conjPrime₂ P ∈ SS
    · rw [if_pos (h2.2 hQ), if_pos hQ]
    · rw [if_neg (fun h => hQ (h2.1 h)), if_neg hQ]

end GlobalTheory.TwU.SeamExp
