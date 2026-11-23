import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Flat.KonstReg

theorem exists_const_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : Cpt 𝔐.ξ), (∀ n : ℕ, n ≠ 0 → IsUnit ((n : 𝔐.X.presheaf.stalk p.1))) → ∃ g₀ : c.F →+* 𝔐.X.presheaf.stalk p.1, (genMap 𝔐.ξ p).comp g₀ = 𝔐.cst := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 p hunit
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have hs : 𝔐.ξ ≫ (𝔐.f ≫ Y.s) = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 c.F) Ω)) := 𝔐.cst_over
  let h : 𝓞 c.F →+* 𝔐.X.presheaf.stalk p.1 :=
    (𝔐.X.presheaf.germ ⊤ p.1 trivial).hom.comp
      ((𝔐.f ≫ Y.s).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv.hom)
  have hgen : ∀ o : 𝓞 c.F, genMap 𝔐.ξ p (h o) = 𝔐.cst (algebraMap (𝓞 c.F) c.F o) :=
    fun o => Flat.ConstReg.genMap_germ_const 𝔐.ξ (𝔐.f ≫ Y.s) hs p o
  have hu : ∀ o : 𝓞 c.F, o ≠ 0 → IsUnit (h o) := by
    intro o ho
    have hI : (Ideal.span {o}).comap (algebraMap ℤ (𝓞 c.F)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ho (Ideal.mem_span_singleton_self o) (Algebra.IsIntegral.isIntegral o)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hn
    have hnat : IsUnit ((n.natAbs : ℕ) : 𝔐.X.presheaf.stalk p.1) := hunit _ (Int.natAbs_ne_zero.mpr hn0)
    have hint : IsUnit (h (algebraMap ℤ (𝓞 c.F) n)) := by
      rw [eq_intCast (algebraMap ℤ (𝓞 c.F)), map_intCast]
      rcases Int.natAbs_eq n with hn' | hn'
      · rw [hn']
        simpa using hnat
      · rw [hn']
        simpa using hnat
    exact isUnit_of_dvd_unit (map_dvd h hn) hint
  refine ⟨IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) (S := c.F)
    (fun z => hu z.1 (nonZeroDivisors.ne_zero z.2)), ?_⟩
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F))
  ext o
  simp only [RingHom.comp_apply, IsLocalization.lift_eq]
  exact hgen o

end GlobalTheory.CompanionTheory.Ar.Flat.KonstReg
