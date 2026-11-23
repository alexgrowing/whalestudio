import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

set_option autoImplicit false

namespace GlobalTheory.SteinFibre

theorem mem_asIdeal_iff_algX_mem_under {F : Type} [Field F] [NumberField F] (X : Scheme.{0})
    (p : X ⟶ Sp (𝓞 F)) (z : X) (c : 𝓞 F) :
    c ∈ (p z).asIdeal ↔ ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ c ∈ under z := by
  rw [mem_under_iff, ← Scheme.mem_basicOpen X (U := ⊤) _ z trivial]
  have e1 : X.basicOpen (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ c) =
      ⊤ ⊓ p ⁻¹ᵁ (Sp (𝓞 F)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv c) :=
    Scheme.basicOpen_appLE p ⊤ ⊤ _ _
  rw [e1, basicOpen_eq_of_affine]
  simp only [top_inf_eq]
  change c ∈ (p z).asIdeal ↔ ¬ (p z ∈ PrimeSpectrum.basicOpen c)
  exact ⟨fun h h' => (PrimeSpectrum.mem_basicOpen _ _).1 h' h,
    fun h => by_contra fun h' => h ((PrimeSpectrum.mem_basicOpen _ _).2 h')⟩

end GlobalTheory.SteinFibre

namespace GlobalTheory.IsArithVar

theorem algX_injective {F : Type} [Field F] [NumberField F] {X : Scheme.{0}} {p : X ⟶ Sp (𝓞 F)}
    {e : ℕ} (h : IsArithVar p e) : Function.Injective (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤) := by
  have hc := h.charZero
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  set I := RingHom.ker (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)
  have hI : I ≠ ⊥ := fun hb => ha0 (by
    have : a ∈ I := ha
    rw [hb] at this
    exact this)
  have hn : Ideal.absNorm I ≠ 0 := fun h0 => hI (Ideal.absNorm_eq_zero_iff.1 h0)
  have hm : ((Ideal.absNorm I : ℕ) : 𝓞 F) ∈ I := by exact_mod_cast Ideal.absNorm_mem I
  have : ((Ideal.absNorm I : ℕ) : Γ(X, ⊤)) = 0 := by
    rw [← map_natCast (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)]
    exact hm
  exact hn (Nat.cast_eq_zero.1 this)

theorem asIdeal_eq_bot_of_under_eq_bot : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp (𝓞 F)) (e : ℕ),
    IsArithVar p e → ∀ z : X, GlobalTheory.SteinFibre.under z = ⊥ → (p z).asIdeal = ⊥ := by
  intro F _ _ X _ p e h z hz
  have inj := algX_injective h
  ext c
  rw [GlobalTheory.SteinFibre.mem_asIdeal_iff_algX_mem_under X p z c, hz, Ideal.mem_bot, Ideal.mem_bot]
  exact ⟨fun h0 => inj (by rw [h0, map_zero]), fun h0 => by rw [h0, map_zero]⟩

end GlobalTheory.IsArithVar
