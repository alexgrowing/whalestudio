import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AtMember

set_option synthInstance.maxHeartbeats 400000 in

theorem conj_gen_mem_frame : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt) (t : Bl.ColT w Z), HalfAt (Formalism.L2.Herm.toErrXS t.full.1) (Fr.at (w.st Z) f) := by
  intro B f T w Z t k
  have hpi : (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG := by
    have h5 : (t.full.1.cols.levelZeroCompatibility (w.D Z).u₀).piG = (t.C.herm.levelZeroCompatibility (w.D Z).u₀).piG :=
      congrArg (fun X : Formalism.L2.Herm.ColsHermS (w.D Z) => (X.levelZeroCompatibility (w.D Z).u₀).piG) t.full.2
    exact h5.trans ((t.C.piG (w.D Z).u₀).symm.trans (t.std (w.D Z).u₀).gl.piG)
  show barE (w.D Z) ((Formalism.L2.Herm.toErrXS t.full.1).piG k) ∈
    Ideal.map (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)) ((Fr.at (w.st Z) f).P.pb k).asIdeal
  rw [hpi]
  have hP : (Fr.at (w.st Z) f).P = w.I.C.P := by rw [w.C_eq]; rfl
  rw [hP]
  have hdiv := w.ok.pibar k
  set π : 𝓞 (w.D Z).host.E := w.px.piG k with hπdef
  set b : 𝓞 (w.D Z).host.E := barE (w.D Z) π with hbdef
  have hbc : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) = (w.D Z).host.conj (π : (w.D Z).host.E) := barE_eq_conj _ _
  have hprod : π * b = (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E) := by
    apply RingOfIntegers.ext
    show ((π : (w.D Z).host.E) * (b : (w.D Z).host.E)) = algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E)
    rw [map_natCast, hbc]
    exact w.px.piG_norm k
  have hg0 : (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E) h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h'
    exact ((w.D Z).host.g_prime k).ne_zero h'
  have hπ0 : π ≠ 0 := fun h => hg0 (by rw [← hprod, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hg0 (by rw [← hprod, h, mul_zero])
  have hbK : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) ∈ (w.D Z).host.K := by
    have hπE : ((π : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) ≠ 0 := fun h => hπ0 (RingOfIntegers.ext (h.trans (map_zero (algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E)).symm))
    have e : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) =
        ((w.D Z).host.g k : (w.D Z).host.E) / ((π : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) := by
      rw [eq_div_iff hπE, mul_comm, hbc]
      exact w.px.piG_norm k
    rw [e]
    exact div_mem (natCast_mem _ _) (w.px.piG_K k)
  set y : 𝓞 (w.D Z).host.K := toOK b hbK with hydef
  have hy : algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y = b := algebraMap_toOK b hbK
  rw [← hy]
  apply Ideal.mem_map_of_mem

  have iI : Algebra.IsIntegral (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
  have hPk : ((w.I.C.P.pb k).asIdeal : Ideal (𝓞 (w.D Z).host.K)).IsPrime := (w.I.C.P.pb k).isPrime
  obtain ⟨Q, -, hQp, hQ⟩ := @Ideal.exists_ideal_over_prime_of_isIntegral (𝓞 (w.D Z).host.K) _ (𝓞 (w.D Z).host.E) _
    (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)).toAlgebra iI
    ((w.I.C.P.pb k).asIdeal : Ideal (𝓞 (w.D Z).host.K)) hPk ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) (hx.trans (map_zero _).symm)
      rw [this]; exact Ideal.zero_mem _)
  have hgQ : π * b ∈ Q := by
    rw [hprod, ← map_natCast (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)), ← Ideal.mem_comap, hQ]
    exact w.I.C.P.pb_over k
  rcases hQp.mem_or_mem hgQ with hπQ | hbQ
  ·
    have hQ'p : (Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E)).IsPrime := Ideal.comap_isPrime _ _
    have hbQ' : b ∈ Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E) := by
      rw [Ideal.mem_comap]
      show barE (w.D Z) (barE (w.D Z) π) ∈ Q
      rw [barE_barE]; exact hπQ
    let Q' : HeightOneSpectrum (𝓞 (w.D Z).host.E) :=
      ⟨Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E), hQ'p, fun h => hb0 (by rw [h] at hbQ'; exact (Ideal.mem_bot).1 hbQ')⟩
    have hmem : Q' ∈ (B.primes w.px).vG k := (Formalism.L2.Col.mem_divs hb0 Q').2 hbQ'
    have hd := (hdiv Q').1 hmem
    have hu : y ∈ (HeightOneSpectrum.under (𝓞 (w.D Z).host.K) Q').asIdeal := by
      show algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y ∈ Q'.asIdeal
      rw [hy]; exact hbQ'
    have hd' : HeightOneSpectrum.under (𝓞 (w.D Z).host.K) Q' = w.I.C.P.pb k := hd
    rw [hd'] at hu
    exact hu
  · rw [← hQ]
    have h' : algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y ∈ Q := hy.symm ▸ hbQ
    exact h'

end GlobalTheory.AtMember
