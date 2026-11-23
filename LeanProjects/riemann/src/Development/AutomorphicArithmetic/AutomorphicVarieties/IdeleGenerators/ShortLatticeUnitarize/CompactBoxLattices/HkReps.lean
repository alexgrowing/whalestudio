import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

open NumberField IsDedekindDomain IsLocalRing UpperTheory.V UpperTheory.V.Sd Formalism.L2.Host

theorem UpperTheory.V.Sd.Wc.hkReps :
    UpperTheory.V.Sd.UopSum → UpperTheory.V.Sd.Wc.HkReps := by
  intro hU F _ _ w c
  classical
  haveI : Fintype (ResidueField (HeightOneSpectrum.adicCompletionIntegers F w)) := Fintype.ofFinite _
  let sec := Function.surjInv (residue_surjective (R := HeightOneSpectrum.adicCompletionIntegers F w))
  have hsec : ∀ r, residue _ (sec r) = r :=
    Function.surjInv_eq (residue_surjective (R := HeightOneSpectrum.adicCompletionIntegers F w))
  let S := Finset.univ.image sec
  have hS : Set.BijOn (residue (HeightOneSpectrum.adicCompletionIntegers F w)) (↑S) Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨r, rfl⟩ := hx
      obtain ⟨s, rfl⟩ := hy
      rw [hsec, hsec] at hxy
      rw [hxy]
    · intro r _
      exact ⟨sec r, by simp [S], hsec r⟩
  let e : Fin S.card ≃ S := S.equivFin.symm
  let b : Fin S.card → GL (Fin 2) (HeightOneSpectrum.adicCompletion F w) :=
    fun i => aff ((atFin w) (unif w)) ↑((e i : HeightOneSpectrum.adicCompletionIntegers F w))
  have hsum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion F w)) V) (x : V),
      ∑ u ∈ S, (ρ (aff ((atFin w) (unif w)) ↑u)) x = ∑ i, (ρ (b i)) x := by
    intro V _ _ ρ x
    rw [← Finset.sum_coe_sort S]
    exact (Equiv.sum_comp e (fun u : S => (ρ (aff ((atFin w) (unif w)) ↑(u : HeightOneSpectrum.adicCompletionIntegers F w))) x)).symm
  by_cases hc : c = 0
  · refine ⟨S.card + 1, Fin.cons ((Matrix.GeneralLinearGroup.scalar (Fin 2)) ((atFin w) (unif w)) * (aff ((atFin w) (unif w)) 0)⁻¹) b, fun h => absurd hc h, ?_⟩
    intro V _ _ ρ x hx
    obtain ⟨h1, h2⟩ := hU F w V ρ c x hx
    refine ⟨h1, ?_⟩
    rw [h2 S hS, if_pos hc, Fin.sum_univ_succ, hsum, Fin.cons_zero, add_comm]
    simp only [Fin.cons_succ]
  · refine ⟨S.card, b, fun _ i => ⟨(e i : HeightOneSpectrum.adicCompletionIntegers F w), rfl⟩, ?_⟩
    intro V _ _ ρ x hx
    obtain ⟨h1, h2⟩ := hU F w V ρ c x hx
    refine ⟨h1, ?_⟩
    rw [h2 S hS, if_neg hc, add_zero, hsum]
