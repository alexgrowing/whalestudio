import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.Loc2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.OrdinaryFlagThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CharpolyEqProd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.HV UpperTheory.V.Base UpperTheory.V.Z.Win
open UpperTheory.V.Z.Win.Dn

namespace UpperTheory.V.Z.Win.Dn.L3

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem cycZ_ine {A : ValuationSubring Ω} (hA : ¬ A.valuation (l : Ω) < 1) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) : cycZ ℚ Ω l s = 1 := by
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have hv1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).2 (natCast_mem A l)) (not_lt.1 hA)
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun m => ?_)
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hv : ¬ A.valuation ((l ^ m : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, hv1, one_pow]
    exact lt_irrefl _
  have hc : Chr.cls ℚ Ω (l ^ m) s = 1 := (Chr.clsFacts ℚ Ω (l ^ m)).2.2.2.2 A hv hs
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  have h1 : s ζ = ζ ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ.pow_eq_one
  have h2 := Chr.cls_spec (l ^ m) s ζ hζ.pow_eq_one
  rw [hc] at h2
  have h3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h1.symm.trans h2)
  have h4 := ZMod.val_injective _ h3
  simpa using h4

private theorem cls_const (N : ℕ) [NeZero N] : IsLocallyConstant (Chr.cls ℚ Ω N) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' ((Chr.cls ℚ Ω N).ker : Set (G ℚ Ω)),
    (Chr.clsFacts ℚ Ω N).1.preimage (continuous_const_mul x⁻¹), ?_, fun y hy => ?_⟩
  · simp
  · have h : Chr.cls ℚ Ω N (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at h
    exact h.symm

private theorem away_char (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    {A : ValuationSubring Ω} (hA : ¬ A.valuation (l : Ω) < 1) :
    ∃ χ : G K Ω →* (Qbar l)ˣ, Continuous χ ∧ (χ '' (Ine (F := K) A : Set (G K Ω))).Finite ∧
      ∀ g ∈ Ine (F := K) A, χ g = 1 → Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω g) = 1 := by
  let a : (c.O)ˣ →* (Qbar l)ˣ := Units.map (algebraMap c.O (Qbar l)).toMonoidHom
  have ha : Function.Injective a := Units.map_injective (f := (algebraMap c.O (Qbar l)).toMonoidHom)
    (FaithfulSMul.algebraMap_injective c.O (Qbar l))
  let d : G ℚ Ω →* (Qbar l)ˣ := a.comp (Chr.dirG ℚ Ω ψ)
  have hcy : ∀ s, a (chiO ℚ Ω l c.O s) = cycBar ℚ Ω l s := fun s => by
    ext
    rfl
  have hpsi : ∀ s, a (Chr.Psi l e (Chr.dirG ℚ Ω ψ) s) = cycBar ℚ Ω l s ^ (e : ℤ) * d s := fun s => by
    rw [Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow, hcy]
    rfl
  have hdc : Continuous d :=
    ((cls_const N).comp fun u : (ZMod N)ˣ => a (ψ.toUnitHom u)).continuous
  have hcc : Continuous (cycBar ℚ Ω l) := UpperTheory.V.Af.Es.cyc_cont
  have hfull : Continuous (a.comp (Chr.Psi l e (Chr.dirG ℚ Ω ψ))) := by
    have : (a.comp (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) : G ℚ Ω → (Qbar l)ˣ) =
        fun s => cycBar ℚ Ω l s ^ (e : ℤ) * d s := funext hpsi
    rw [this]
    exact ((continuous_zpow (e : ℤ)).comp hcc).mul hdc
  refine ⟨(a.comp (Chr.Psi l e (Chr.dirG ℚ Ω ψ))).comp (galEmb ℚ K Ω),
    hfull.comp (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ K Ω), ?_, fun g _ h => ha (by simpa using h)⟩
  refine (Set.finite_range fun u : (ZMod N)ˣ => a (ψ.toUnitHom u)).subset ?_
  rintro _ ⟨g, hg, rfl⟩
  have hg' : galEmb ℚ K Ω g ∈ Ine (F := ℚ) A := hg
  refine ⟨Chr.cls ℚ Ω N (galEmb ℚ K Ω g), ?_⟩
  have h1 : cycBar ℚ Ω l (galEmb ℚ K Ω g) = 1 := by
    rw [cycBar, MonoidHom.comp_apply, cycZ_ine hA hg', map_one]
  change d (galEmb ℚ K Ω g) = a (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω g))
  rw [hpsi, h1, one_zpow, one_mul]

end UpperTheory.V.Z.Win.Dn.L3

theorem UpperTheory.V.Z.Win.Dn.localConditionRankThreeLink_of_inertia_ordinary :
    IneOfKer → FlagAll → Loc3 := by
  intro hI hF Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ C₀ k hok A _ _ r hr K _ _ _ _ _ hker ρ hρ
  refine ⟨hI K Ω l 3 ρ fun A' hA' => ?_, hF K Ω l 3 ρ fun w hw => ?_⟩
  · obtain ⟨χ, hc, hfin, h1⟩ := L3.away_char c N e ψ K hA'
    refine ⟨χ, hc, hfin, fun g hg hχ => Units.ext ?_⟩
    have hη : η (galEmb ℚ K Ω g) = 1 := by
      have : galEmb ℚ K Ω g ∈ η.ker := hker ▸ galEmb_mem ℚ K Ω g
      exact this
    have hr1 : r (galEmb ℚ K Ω g) = 1 := hr.away A' hA' _ hg hη (h1 g hg hχ)
    have hp : UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω g) = 1 := by
      rw [MonoidHom.comp_apply, hr1, map_one]
    rw [hρ g, hp]
    rfl
  · obtain ⟨A', hA', κ, -, -, hf, -⟩ :=
      Keep.ordFlag3 Ω l c N e ψ η σ g₁ B M H L Φ C₀ k hok A r hr K hker ρ hρ w hw
    exact ⟨A', hA', κ, hf⟩
