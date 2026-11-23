import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ProjFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelLeIne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem compIne_map (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) :
    (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) = (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI hMz : NeZero (N / r ^ N.factorization r) := ⟨(Nat.ordCompl_pos r (NeZero.ne N)).ne'⟩
  have hMcop : (N / r ^ N.factorization r).Coprime r := (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
  have fix : ∀ σ ∈ Ine (F := ℚ) A, ∀ ζ : Ω, ζ ^ (N / r ^ N.factorization r) = 1 → σ ζ = ζ :=
    fun σ hσ ζ hζ => (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA _ hMcop ζ hζ).2 σ hσ
  have powOne : ∀ ζ : Ω, ζ ^ (N / r ^ N.factorization r) = 1 →
      ζ ^ (((1 : (ZMod (N / r ^ N.factorization r))ˣ) : ZMod (N / r ^ N.factorization r))).val = ζ := by
    intro ζ hζ
    rw [Units.val_one, ZMod.val_one_eq_one_mod]
    by_cases h1 : N / r ^ N.factorization r = 1
    · rw [h1, pow_one] at hζ
      rw [hζ, one_pow]
    · rw [Nat.mod_eq_of_lt (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hMz.out, h1⟩), pow_one]
  have kerCls : ∀ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω (N / r ^ N.factorization r) σ = 1 := fun σ hσ =>
    (Chr.clsFacts ℚ Ω _).2.2.1 σ 1 (fun ζ hζ => by rw [fix σ hσ ζ hζ, powOne ζ hζ])
  ext u
  rw [Subgroup.mem_map, MonoidHom.mem_ker]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have e := congrArg (fun f => f σ) ((Chr.clsFacts ℚ Ω N).2.1 _ (Nat.ordCompl_dvd N r))
    simp only [MonoidHom.comp_apply] at e
    rw [e]
    exact kerCls σ hσ
  · intro hu
    obtain ⟨v, hv⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r) (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
    obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA v
    refine ⟨σ, hσ, ?_⟩
    apply (Chr.clsFacts ℚ Ω N).2.2.1
    refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).mpr ⟨?_, ?_⟩
    · intro ζ hζ
      rw [hu, powOne ζ hζ]
      exact fix σ hσ ζ hζ
    · rw [← hv, ← hσv]
      rfl

private theorem compIne_unit {O : Type} [CommRing O] {N : ℕ} (r : ℕ) (χ : DirichletCharacter O N) :
    (comp r χ).toUnitHom = χ.toUnitHom.comp (proj r N) := by
  ext u
  simp [UpperTheory.V.HV.comp]

theorem UpperTheory.V.HV.compIne :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ), r.Prime → ∀ A : ValuationSubring Ω, A.valuation (r : Ω) < 1 →
      (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) = (proj r N).range ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] (χ : DirichletCharacter O N), (∀ σ ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω χ σ = Chr.dirG ℚ Ω (comp r χ) σ) ∧
        (Ine (F := ℚ) A ≤ (Chr.dirG ℚ Ω χ).ker ↔ comp r χ = 1) := by
  intro Ω _ _ _ N _ r hr A hA
  have hrange : (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) = (proj r N).range := by
    rw [compIne_map Ω N r hr A hA, (projFacts N r hr).2.2.2.2.2.1]
  refine ⟨hrange, fun O _ _ χ => ?_⟩
  have same : ∀ σ ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω χ σ = Chr.dirG ℚ Ω (comp r χ) σ := by
    intro σ hσ
    have hm : Chr.cls ℚ Ω N σ ∈ (proj r N).range := by
      rw [← hrange]
      exact Subgroup.mem_map_of_mem _ hσ
    obtain ⟨w, hw⟩ := hm
    simp only [Chr.dirG, MonoidHom.comp_apply, compIne_unit]
    rw [← hw, (projFacts N r hr).2.2.1 w]
  refine ⟨same, ⟨fun h => ?_, fun h σ hσ => ?_⟩⟩
  · rw [MulChar.eq_one_iff]
    intro u
    have hm : proj r N u ∈ (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) := by
      rw [hrange]
      exact ⟨u, rfl⟩
    obtain ⟨σ, hσ, hσu⟩ := hm
    have h1 := h hσ
    rw [MonoidHom.mem_ker] at h1
    simp only [Chr.dirG, MonoidHom.comp_apply] at h1
    rw [← MulChar.coe_toUnitHom, compIne_unit, MonoidHom.comp_apply, ← hσu, h1, Units.val_one]
  · rw [MonoidHom.mem_ker, same σ hσ]
    simp only [Chr.dirG, MonoidHom.comp_apply, h]
    ext
    simp
