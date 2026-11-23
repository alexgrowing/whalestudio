import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreeOrthogonalSupportAndSupISpecializes
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.KerAb

theorem subset_abLocus {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Zh : ZHOut ρ M U₀ EE) (hO : S.Over₀ M U₀) :
    (U₀ : Set M.Z) ⊆ abLocus Zh.G := by
  intro z hz
  rw [Zh.ab]
  show S.TT M z = ⊥
  have hpp := (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1
  have h1 : S.perp ⊥ = ⊤ := by
    refine top_unique fun a _ h hh => ?_
    rw [AddSubgroup.mem_bot.mp hh]
    simp [ZH.eStd]
  rw [ZH.ThetaSys.TT, ZH.ThetaSys.HH, hO.supI_eq hz, S.supp, ← h1, hpp]

theorem ker_mem_and_subset_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∀ (R : Type) [CommRing R] (q : Sp R ⟶ M.Z) (V' : Type) [CommRing V'] [IsDomain V'] (h : T.V →+* V') (g' : R →+* V'), Function.Injective h → spMap g' ≫ q = spMap h ≫ ξ → (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) ∈ q ⁻¹' (U₀ : Set M.Z) ∧ (U₀ : Set M.Z) ⊆ abLocus out.G := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm T ξ hξ R _ q V' _ _ h g' hh hq
  refine ⟨?_, subset_abLocus out hAdm.1⟩
  obtain ⟨ξ₀, h₀, -⟩ := hξ
  let w : Sp V' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V')
  let v : Sp (FractionRing T.V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing T.V))
  have e₁ : spMap g' w = (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) :=
    PrimeSpectrum.ext (RingHom.ker_eq_comap_bot g').symm
  have e₂ : spMap h w = jK T.V v := by
    refine PrimeSpectrum.ext ?_
    show Ideal.comap h ⊥ = Ideal.comap (algebraMap T.V (FractionRing T.V)) ⊥
    rw [← RingHom.ker_eq_comap_bot, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hh,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective T.V (FractionRing T.V))]
  have e₃ : q (spMap g' w) = U₀.ι (ξ₀ v) := by
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply, e₂, ← Scheme.Hom.comp_apply, ← h₀, Scheme.Hom.comp_apply]
  rw [← e₁]
  show q (spMap g' w) ∈ U₀
  rw [e₃]
  exact (ξ₀ v).2

end GlobalTheory.UPoinc.KerAb
