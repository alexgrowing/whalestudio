import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Cardinal

noncomputable section

theorem exists_ringHom_complex_of_charZero (F : Type) [Field F] [CharZero F] (hF : #F ≤ 𝔠) :
    Nonempty (F →+* ℂ) := by
  let M := MvPolynomial ℂ F
  let E := FractionRing M
  let L := AlgebraicClosure E
  have : CharZero M := charZero_of_injective_algebraMap (R := F) (MvPolynomial.C_injective _ _)
  have : CharZero E := charZero_of_injective_algebraMap (R := M) (IsFractionRing.injective M E)
  have : CharZero L := charZero_of_injective_algebraMap (R := E) (algebraMap E L).injective
  have hM : #M ≤ 𝔠 := by
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    rw [mk_complex]
    exact max_le (max_le hF le_rfl) aleph0_le_continuum
  have hE : #E = #M := Cardinal.mk_fractionRing M
  have hL : #L ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max E L).trans (max_le (hE ▸ hM) aleph0_le_continuum)
  have hinj : Function.Injective (fun c : ℂ => algebraMap E L (algebraMap M E (X c))) :=
    (algebraMap E L).injective.comp ((IsFractionRing.injective M E).comp MvPolynomial.X_injective)
  have hLc : #L = #ℂ :=
    le_antisymm (hL.trans_eq mk_complex.symm) (Cardinal.mk_le_of_injective hinj)
  obtain ⟨σ⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (by rw [hLc, mk_complex]; exact aleph0_lt_continuum) (Cardinal.eq.1 hLc)
  exact ⟨σ.toRingHom.comp ((algebraMap E L).comp ((algebraMap M E).comp C))⟩

theorem exists_mcPts_not_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (hJ : ¬ J ≤ P) :
    ∃ z, z ∈ mcPts P ∧ z ∉ mcPts J := by
  obtain ⟨_, ⟨hprime, -, hrel⟩, hhor, -⟩ := hP
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.mp hJ
  have := hprime
  let Q := MRing ι ⧸ P
  let F := FractionRing Q
  have hQ : Function.Injective (algebraMap ℤ Q) := by
    have e : algebraMap ℤ Q = (Ideal.Quotient.mk P).comp C := RingHom.ext_int _ _
    rw [e, injective_iff_map_eq_zero]
    intro n hn
    have hn0 : (C n : MRing ι) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hn
    have hn' : n ∈ P.comap (C : ℤ →+* MRing ι) := hn0
    rw [IsHorizontal] at hhor
    rw [hhor] at hn'
    exact (Ideal.mem_bot).mp hn'
  have : CharZero Q := charZero_of_injective_algebraMap hQ
  have : CharZero F := charZero_of_injective_algebraMap (R := Q) (IsFractionRing.injective Q F)
  have hcard : #F ≤ 𝔠 := by
    rw [Cardinal.mk_fractionRing]
    refine (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    exact max_le (max_le (mk_int.le.trans aleph0_le_continuum)
      (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum
  obtain ⟨ψ⟩ := exists_ringHom_complex_of_charZero F hcard
  let φ : MRing ι →+* ℂ := (ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P)
  have hker : ∀ f, φ f = 0 ↔ f ∈ P := by
    intro f
    have hi : Function.Injective (ψ.comp (algebraMap Q F)) :=
      ψ.injective.comp (IsFractionRing.injective Q F)
    rw [show φ f = (ψ.comp (algebraMap Q F)) (Ideal.Quotient.mk P f) from rfl,
      map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]
  let z : (Σ k, ι k) → ℂ := fun p => φ (X p)
  have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ f := by
    intro f
    have h : (eval z).comp (map (Int.castRingHom ℂ)) = φ := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · exact RingHom.congr_fun
          (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C) (φ.comp C)) r
      · simp [z]
    exact RingHom.congr_fun h f
  refine ⟨z, ⟨fun k => ?_, fun f hf => ?_⟩, fun hz => ?_⟩
  · obtain ⟨i, hi⟩ := hrel k
    exact ⟨i, fun h => hi ((hker _).mp h)⟩
  · rw [hev]
    exact (hker f).mpr hf
  · exact hgP ((hker g).mp (by rw [← hev]; exact hz.2 g hgJ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
