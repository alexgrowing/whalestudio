import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ScalQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.H2RightExactModLOfH3Subsingleton
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.arGlob :
    CohP → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Set (HeightOneSpectrum (𝓞 F))), l ≠ 2 → S.Finite → (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) → FinH l (GS Ω S) ∧ SecondCohomologyRightExactModL l (GS Ω S) := by
  intro hP F Ω _ _ _ _ _ l _ S hl hS hab
  obtain ⟨T, rfl⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), S = ↑T := ⟨hS.toFinset, by simp⟩
  have key : ∀ (A : Type) [CommRing A] (M : FRep A (GS Ω (T : Set (HeightOneSpectrum (𝓞 F))))),
      (∀ m : M.X, l • m = 0) → Finite (H1 M.ρ) ∧ Finite (H2 M.ρ) ∧ Subsingleton (Hn M.ρ 3) := by
    intro A _ M hM
    letI : Module (ZMod (l ^ 1)) M.X := AddCommGroup.zmodModule (by simpa using hM)
    obtain ⟨hc, -, ⟨e1, -⟩, ⟨e2, -⟩⟩ := UpperTheory.V.Pa.B2.scal A _ M (l ^ 1)
    obtain ⟨-, h1, h2, h3⟩ := hP.gf F Ω l 1 M.X T (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) one_pos
      (fun v hv => hab v hv) hc
    exact ⟨Finite.of_equiv _ e1.symm.toEquiv, Finite.of_equiv _ e2.symm.toEquiv,
      GlobalTheory.Published.subsingleton_Hn_of_action_eq M.ρ (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)
        (fun _ _ => rfl) 3 (by omega) (h3 hl 3 le_rfl)⟩
  exact ⟨fun A _ M hM => ⟨(key A M hM).1, (key A M hM).2.1⟩,
    UpperTheory.V.Pa.B2.H2_right_exact_mod_l_of_H3_subsingleton l _ fun A _ M hM => (key A M hM).2.2⟩
