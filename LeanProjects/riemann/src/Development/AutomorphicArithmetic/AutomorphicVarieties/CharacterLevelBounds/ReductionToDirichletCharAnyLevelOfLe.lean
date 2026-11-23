import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.AbLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LayerLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.H0LocalCardBoundedOfClsKerLeKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.EigV
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PartModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.SignLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.VLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RelIndexInfDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LiftGens
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.FactLeLog
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.SumBack
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaAbsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.FactorGS
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.ExistsNumberFieldIsAbFieldFinrankEqDeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.layerex
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AbelianFieldHasMuIffExistsPrimitiveRoot
import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

namespace UpperTheory.V.Chr

section Red

variable (E : Type) [Field E] [NumberField E] [IsCMField E] {N : ℕ} [NeZero N] {H : Subgroup (ZMod N)ˣ}
  {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {Ω' : Type} [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω'] (D : LData E Ω' l)
  (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

omit [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem levH_le_ker {s : ℕ} {χ : DirichletCharacter O N} (h : χ ∈ evenSet O H s) : levH ℚ Ω H ≤ (dirG ℚ Ω χ).ker :=
  fun _ hg => h.1 hg

theorem levH_facts : (levH ℚ Ω H).index = H.index ∧ IsOpen (levH ℚ Ω H : Set (G ℚ Ω)) :=
  ⟨Subgroup.index_comap_of_surjective _ (clsOnto Ω N).1,
    Subgroup.isOpen_mono (H₁ := (cls ℚ Ω N).ker) (fun g hg => by
      show cls ℚ Ω N g ∈ H
      rw [MonoidHom.mem_ker.1 hg]; exact one_mem _) (clsFacts ℚ Ω N).1⟩

theorem reduction_to_dirichletChar_any_level (hE : HasLevel E N H) [HasEnoughRootsOfUnity O (Monoid.exponent ((ZMod N)ˣ ⧸ H))] (h2 : l ≠ 2)
    {e : ℕ} (he : e ≠ 0) (T : Finset (DirichletCharacter O N)) :
    (↑T = evenSet O H e → plusLen D e * eO l O ≤
      ∑ χ ∈ T, (V l e (dirG ℚ Ω χ) + (loss l N (Module.finrank ℚ E) e : ℕ∞) * eO l O)) ∧
    (↑T = evenSet O H (e + 1) → minusLen D e * eO l O ≤
      ∑ χ ∈ T, (V l e (dirG ℚ Ω χ) + (loss l N (Module.finrank ℚ E) e : ℕ∞) * eO l O)) := by
  obtain ⟨c, hc, hp, hm⟩ := partModel E N H hE l O Ω' D Ω e
  rw [(levGal E N H hE).2.1, hp, hm]
  exact ⟨fun hT => (signLe Ω N H l O h2 e _ c hc T hT.ge).trans (Finset.sum_le_sum fun χ hχ =>
      eigLe Ω N H l O e _ he (levH_le_ker O Ω (hT.le hχ))),
    fun hT => (signLe Ω N H l O h2 e _ c hc T hT.ge).trans (Finset.sum_le_sum fun χ hχ =>
      eigLe Ω N H l O e _ he (levH_le_ker O Ω (hT.le hχ)))⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem dirG_pow {s : ℕ} {χ : DirichletCharacter O N} (h : χ ∈ evenSet O H s) : dirG ℚ Ω χ ^ H.index = 1 := by
  unfold evenSet at h
  have hH : H ≤ (MulChar.toUnitHom χ).ker := h.1
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  unfold dirG
  rw [MonoidHom.comp_apply, ← map_pow, ← MonoidHom.mem_ker]
  exact hH (H.pow_index_mem _)

theorem V_le_V' {s e : ℕ} (he : e ≠ 0) {χ : DirichletCharacter O N} (h : χ ∈ evenSet O H s) {N' : ℕ} (hN : N' ≠ 0) :
    V l e (dirG ℚ Ω χ) ≤ V' l N' e (dirG ℚ Ω χ) + ((N'.primeFactors.card * H.index.factorization l : ℕ) : ℕ∞) * eO l O ∧
    (¬ l ∣ H.index → V l e (dirG ℚ Ω χ) = V' l N' e (dirG ℚ Ω χ)) := by
  have hopen : IsOpen ((dirG ℚ Ω χ).ker : Set (G ℚ Ω)) :=
    Subgroup.isOpen_mono (levH_le_ker (O := O) (Ω := Ω) h) (levH_facts (Ω := Ω) (H := H)).2
  have hpow := dirG_pow (O := O) (Ω := Ω) h
  exact vLe Ω l O N' e H.index _ hN he Subgroup.index_ne_zero_of_finite hopen hpow

theorem reduction_to_dirichletChar_any_level_of_le (hE : HasLevel E N H) [HasEnoughRootsOfUnity O (Monoid.exponent ((ZMod N)ˣ ⧸ H))] (h2 : l ≠ 2)
    {e : ℕ} (he : e ≠ 0) (T : Finset (DirichletCharacter O N)) {N' : ℕ} (hN : N' ≠ 0) :
    (↑T = evenSet O H e → plusLen D e * eO l O ≤ ∑ χ ∈ T, (V' l N' e (dirG ℚ Ω χ) +
      ((loss l N (Module.finrank ℚ E) e + N'.primeFactors.card * (Module.finrank ℚ E).factorization l : ℕ) : ℕ∞) * eO l O)) ∧
    (↑T = evenSet O H (e + 1) → minusLen D e * eO l O ≤ ∑ χ ∈ T, (V' l N' e (dirG ℚ Ω χ) +
      ((loss l N (Module.finrank ℚ E) e + N'.primeFactors.card * (Module.finrank ℚ E).factorization l : ℕ) : ℕ∞) * eO l O)) := by
  have hrank : Module.finrank ℚ E = H.index := (levGal E N H hE).2.1
  have key := reduction_to_dirichletChar_any_level (E := E) (O := O) (D := D) (Ω := Ω) hE h2 he T
  have hsum : ∀ s, (↑T : Set (DirichletCharacter O N)) = evenSet O H s →
      ∑ χ ∈ T, (V l e (dirG ℚ Ω χ) + (loss l N (Module.finrank ℚ E) e : ℕ∞) * eO l O) ≤
        ∑ χ ∈ T, (V' l N' e (dirG ℚ Ω χ) +
          ((loss l N (Module.finrank ℚ E) e + N'.primeFactors.card * (Module.finrank ℚ E).factorization l : ℕ) : ℕ∞) * eO l O) := by
    intro s hT
    refine Finset.sum_le_sum fun χ hχ => ?_
    have hχ' : χ ∈ evenSet O H s := by rw [← hT]; exact hχ
    have h1 := (V_le_V' (l := l) (O := O) (Ω := Ω) he hχ' hN).1
    rw [hrank]
    calc V l e (dirG ℚ Ω χ) + (loss l N H.index e : ℕ∞) * eO l O
        ≤ (V' l N' e (dirG ℚ Ω χ) + ((N'.primeFactors.card * H.index.factorization l : ℕ) : ℕ∞) * eO l O) +
          (loss l N H.index e : ℕ∞) * eO l O := add_le_add h1 le_rfl
      _ = _ := by push_cast; ring
  exact ⟨fun hT => (key.1 hT).trans (hsum e hT), fun hT => (key.2 hT).trans (hsum (e + 1) hT)⟩

end Red

end UpperTheory.V.Chr

end
