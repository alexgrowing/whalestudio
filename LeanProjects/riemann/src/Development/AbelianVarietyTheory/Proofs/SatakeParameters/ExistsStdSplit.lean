import Mathlib
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries

open NumberField IsDedekindDomain Matrix

noncomputable section

namespace GlobalTheory.ColPeriod

open Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.StdReps

theorem splitNonConj_vG {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (i : Fin 2) :
    GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj (Pr.vG i) := by
  intro P hP Q hQ h
  have h1 : cO X.E (Pr.piG i) ∈ Q.asIdeal := decoFin_mem_of_mem_divs hQ
  have h2 : cO X.E (Pr.piG i) ∈ P.asIdeal := decoFin_mem_of_mem_divs hP
  rw [h, mem_conjP, cO_cO] at h1
  obtain ⟨a, b, e⟩ := hPr.piG_cop i
  apply one_notMem P
  rw [← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem exists_std_split {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 E))}
    (hST : GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj ST) {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) :
    ∃ γ : UF E n, ∀ P ∈ ST, localization₂ P.asIdeal (gmap γ.1 N) = stdAt E n P ∧
      localization₂ (conjPrime₂ P).asIdeal (gmap γ.1 N) = stdAt E n (conjPrime₂ P) := by
  obtain ⟨g, hg, hc⟩ := exists_unitary_carries hST hN.1
  let f : Sp E n ≃ₗ[E] Sp E n := Matrix.toLin'OfInv (M := gᴴ) (M' := g) hg (mul_eq_one_comm.1 hg)
  have hf : ∀ x, f x = g *ᵥ x := fun x => rfl
  have hU : f ∈ UF E n := by
    intro x y
    rw [hf, hf, hStd_apply, hStd_apply]
    change star (g *ᵥ x) ⬝ᵥ (g *ᵥ y) = star x ⬝ᵥ y
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hg, one_mulVec]
  have huni : IsUnimodular (hStd E n) (gmap f N) := by
    have e : dual (hStd E n) N = N := hN.2
    change dual (hStd E n) (gmap f N) = gmap f N
    rw [dual_gmap f hU, e]
  refine ⟨⟨f, hU⟩, fun P hP => ?_⟩
  have h : localization₂ P.asIdeal (gmap f N) = stdAt E n P := by
    ext x
    rw [mem_localization_gmap, ← (hc P hP).2, ← hf, LinearEquiv.apply_symm_apply]
  exact ⟨h, le_antisymm (localization_conj_le_of_le stdLat_lattice.fg stdLat_unimodular huni h.ge)
    (localization_conj_le_of_le (gmap_lattice f N hN.1).fg huni stdLat_unimodular h.le)⟩

theorem stdMove : StdMove := by
  intro X Pr hPr i n N hN
  obtain ⟨γ, hγ⟩ := exists_std_split (splitNonConj_vG hPr i) hN
  refine ⟨γ, fun Q hQ => ?_⟩
  have h0 : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have h1 := hPr.piG_norm i
    rw [h, mul_zero] at h1
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast h1.symm)
  rw [← hPr.piG_norm i] at hQ
  rcases Q.isPrime.mem_or_mem hQ with h | h
  · have hm : conjPrime₂ Q ∈ Pr.vG i := (Formalism.L2.Col.mem_divs h0 _).2 (by
      change cO X.E (cO X.E (Pr.piG i)) ∈ Q.asIdeal
      rwa [cO_cO])
    have hcc : conjPrime₂ (conjPrime₂ Q) = Q := by
      ext x
      rw [mem_conjP, mem_conjP, cO_cO]
    have := (hγ _ hm).2
    rwa [hcc] at this
  · exact (hγ _ ((Formalism.L2.Col.mem_divs h0 _).2 h)).1

end GlobalTheory.ColPeriod
