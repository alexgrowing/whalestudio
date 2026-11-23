import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.clrk_tr :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (U : Subgroup (G ℚ Ω)), U ≤ galOf ℚ F Ω → GC.clRk l (U.comap (galEmb ℚ F Ω)) = GC.clRk l U := by
  intro Ω _ _ _ l _ F _ _ _ U hU
  haveI : Module.IsTorsionFree F Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩
  have hemb := (galEmbTop ℚ F Ω).1
  have hfam := (galEmbFam ℚ F Ω l).1
  let e : U.comap (galEmb ℚ F Ω) ≃ U :=
    { toFun := fun u => ⟨galEmb ℚ F Ω u.1, u.2⟩
      invFun := fun u => ⟨Kum.toGal F hU u, u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Continuous e := (hemb.continuous.comp continuous_subtype_val).subtype_mk _
  have hc' : Continuous e.symm := (hemb.continuous_iff.2 continuous_subtype_val).subtype_mk _
  have hI : ∀ (A : ValuationSubring Ω) (σ : G F Ω), galEmb ℚ F Ω σ ∈ Ine (F := ℚ) A ↔ σ ∈ Ine (F := F) A :=
    fun A σ => SetLike.ext_iff.1 (hfam A).2 σ
  have hD : ∀ (A : ValuationSubring Ω) (σ : G F Ω), galEmb ℚ F Ω σ ∈ Dec (F := ℚ) A ↔ σ ∈ Dec (F := F) A :=
    fun A σ => SetLike.ext_iff.1 (hfam A).1 σ
  have key : (Kum.XDual 1 U (ZMod l) (ZMod l)).map (LinearEquiv.funCongrLeft (ZMod l) (ZMod l) e).toLinearMap =
      Kum.XDual 1 (U.comap (galEmb ℚ F Ω)) (ZMod l) (ZMod l) := by
    ext φ
    constructor
    · rintro ⟨ψ, ⟨h1, h2, h3, h4⟩, rfl⟩
      exact ⟨h1.comp_continuous hc, fun a b => h2 (e a) (e b), fun A u h => h3 A (e u) ((hI A _).2 h),
        fun A hA u h => h4 A hA (e u) ((hD A _).2 h)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨φ ∘ e.symm, ⟨h1.comp_continuous hc', fun a b => h2 (e.symm a) (e.symm b),
        fun A u h => h3 A (e.symm u) ((hI A _).1 h), fun A hA u h => h4 A hA (e.symm u) ((hD A _).1 h)⟩, rfl⟩
  unfold GC.clRk
  rw [← key]
  exact ((LinearEquiv.funCongrLeft (ZMod l) (ZMod l) e).submoduleMap _).rank_eq.symm
