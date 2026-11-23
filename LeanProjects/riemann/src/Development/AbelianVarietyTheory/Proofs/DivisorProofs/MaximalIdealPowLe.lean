import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSameFibreIsIntegralHom
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainFibFinite
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.KerIdeal

theorem maximalIdeal_pow_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [IsCommMonObj B] (π : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsMonHom π → IsIsogDeg π d →
    ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀),
    (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      (∃ z : Sp R' ⟶ Sp k, z ≫ (η[B]).left = (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ≫ π.left) ↔
        J ≤ RingHom.ker ψ) →
    ∃ M : ℕ, IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ^ M ≤ J := by
  intro k _ _ A B _ _ _ _ π d hA hB hπ hiso x₀ hx₀ J hJ
  have := hA.smooth
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have := hiso.fin
  obtain ⟨s, rfl⟩ := hx₀
  have key : ∀ P : Ideal (A.left.presheaf.stalk ((η[A]).left.base s)), P.IsPrime → J ≤ P →
      P = IsLocalRing.maximalIdeal _ := by
    intro P hP hJP
    haveI := hP
    obtain ⟨z, hz⟩ := (hJ (A.left.presheaf.stalk ((η[A]).left.base s) ⧸ P) (Ideal.Quotient.mk P)).2
      (by rw [Ideal.mk_ker]; exact hJP)
    let q : Sp (A.left.presheaf.stalk ((η[A]).left.base s) ⧸ P) := ⟨⊥, Ideal.bot_prime⟩
    set g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) with hg
    have hgq : g q = ⟨P, hP⟩ := by
      apply PrimeSpectrum.ext
      show Ideal.comap (Ideal.Quotient.mk P) ⊥ = P
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    set x₀ := (η[A]).left.base s with hx₀
    have hy : A.left.fromSpecStalk x₀ (g q) ⤳ x₀ := by
      have : A.left.fromSpecStalk x₀ (g q) ∈ Set.range (A.left.fromSpecStalk x₀) := ⟨_, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have h1 : π.left.base (A.left.fromSpecStalk x₀ (g q)) = (η[B]).left.base (z q) := by
      have := congrArg (fun m => m.base q) hz
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
      exact this.symm
    have h2 : π.left.base x₀ = (η[B]).left.base s := by
      have e : (η[A] ≫ π).left = (η[B]).left := by rw [IsMonHom.one_hom]
      have := congrArg (fun m => m.base s) e
      simpa only [Over.comp_left, Scheme.Hom.comp_base, TopCat.comp_app] using this
    have hzs : z q = s := Subsingleton.elim _ _
    have hyx : A.left.fromSpecStalk x₀ (g q) = x₀ :=
      GlobalTheory.eq_of_specializes_of_isIntegralHom π.left hy (by rw [h1, h2, hzs])
    have hgc : g q = IsLocalRing.closedPoint _ := by
      apply (A.left.fromSpecStalk x₀).isEmbedding.injective
      rw [hyx, Scheme.fromSpecStalk_closedPoint]
    have := congrArg PrimeSpectrum.asIdeal (hgq.symm.trans hgc)
    exact this
  have hrad : IsLocalRing.maximalIdeal _ ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun P ⟨hJP, hP⟩ => (key P hP hJP).ge
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

end GlobalTheory.KerIdeal
