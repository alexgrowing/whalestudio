import Formalism.GaloisCohomology.Statement

open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace Formalism.GaloisCohomology

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime]

theorem chi_exists (S : Set (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, ((l:ℕ) : 𝓞 F) ∉ v.asIdeal) :
    ∃ chi : GS Ω S →* ℤ_[l]ˣ, chi.comp (toGS Ω S) = cycZ F Ω l := by
  have hU : UnramOutside S (cycZ F Ω l) := by
    rw [unramOutside_iff S _ (continuous_cycZ F Ω l)]
    intro v hv A hA σ hσ
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq (hS v hv) hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  refine ⟨QuotientGroup.lift (NS Ω S) (cycZ F Ω l) (fun σ h => (MonoidHom.mem_ker).2 (hU σ h)), ?_⟩
  ext σ; rfl

theorem above_finite : (Above F l).Finite := by
  have hl : ((l : ℕ) : 𝓞 F) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap (𝓞 F) F) h
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at h2
    exact (Fact.out : l.Prime).ne_zero h2
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hl
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  show v.asIdeal ∣ Ideal.span {((l : ℕ) : 𝓞 F)}
  rw [Ideal.dvd_span_singleton]
  exact hv

theorem ldata_nonempty : Nonempty (LData F Ω l) := by
  classical
  let S := (above_finite (F := F) l).toFinset
  have hS : (S : Set _) = Above F l := by simp [S]
  obtain ⟨chi, hchi⟩ := chi_exists (F := F) (Ω := Ω) l (S : Set _) (fun v hv h => hv (by rw [hS]; exact h))
  exact ⟨⟨S, hS, fun v => placeOf Ω v.1, fun v => isPlaceOver_placeOf Ω v.1, chi, hchi⟩⟩

end

theorem ldataExists : LDataExists := by
  intro F Ω _ _ _ _ _ l _
  exact ldata_nonempty (F := F) (Ω := Ω) l

end Formalism.GaloisCohomology
