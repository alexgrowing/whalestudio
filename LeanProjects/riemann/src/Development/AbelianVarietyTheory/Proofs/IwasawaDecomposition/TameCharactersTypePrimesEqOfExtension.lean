import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.ChiTr

theorem coreCharacter_fieldInclusion_eq_columnHeckeChar {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {h : B.fields.Ok} {W : Set B.places.Pl}
    (z : Dat (w.st Z) w.I h T W) (j : Fin B.R.m) :
    ChrEq (z.core.chiW ((j : ℕ) + 1) z.core.toCore.σ₀) (w.I.C.mu0 j) := by
  have e := Formalism.IndefR.FWT.chiTie_of_chiR z.core z.R.toRealDat z.geo.fw.alg_eq z.geo.fw.laws.pins.2.2.1 z.geo.fw.chiR j
  rw [e]
  have h1 := z.lev.is.mu0 j
  rw [z.lev.C] at h1
  exact h1

theorem embLL_chi {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (j : Fin B.R.m)
    (p : {p // p ∈ (B.primes w.px).vGs}) (c : (𝓞 B.fields.E ⧸ p.1.asIdeal)ˣ) (y : 𝓞 B.fields.E) (x : B.fields.Eˣ)
    (hx : (x : B.fields.E) = y) (hc : (c : 𝓞 B.fields.E ⧸ p.1.asIdeal) = Ideal.Quotient.mk p.1.asIdeal y) :
    B.embLL ((w.I.Ch.chi j p c : B.fields.Kˣ) : B.fields.K) = (((w.I.C.mu0 j).locK p.1 x : ℂˣ) : ℂ)⁻¹ := by
  have h1 := (w.ok.ch_tied.mu0 j).atg p x y c hx hc
  rw [h1, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem app_chiW {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Type} [Monoid A]
    {H₁ H₂ : Host E} {l₁ : Level H₁} {l₂ : Level H₂} {c₁ : Coeff l₁} {c₂ : Coeff l₂}
    {χ₁ : ℕ → (c₁.F →+* ℂ) → A →* Circle} {χ₂ : ℕ → (c₂.F →+* ℂ) → A →* Circle}
    (hH : HEq H₂ H₁) (hl : HEq l₂ l₁) (hc : HEq c₂ c₁) (hχ : HEq χ₂ χ₁) (n : ℕ) :
    χ₂ n c₂.F.val.toRingHom = χ₁ n c₁.F.val.toRingHom := by
  cases hH; cases hl; cases hc; cases hχ; rfl

end GlobalTheory.Mem.R3.Rw.ChiTr

namespace GlobalTheory.Mem.R3.Rw.ChiTr

theorem embLL_chi_ext : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ Z₁ Z₂ h₁ h₂ W₁ W₂ z₁ z₂ hE hX j₁ j₂ hj p₁ p₂ hp c₁ c₂ hc
  have A₁ := coreCharacter_fieldInclusion_eq_columnHeckeChar z₁ j₁
  have A₂ := coreCharacter_fieldInclusion_eq_columnHeckeChar z₂ j₂
  have eH := hX.H
  have el := hX.l
  have ec := hX.c
  have eχ := hX.chiW
  obtain ⟨hP, -⟩ := hE
  clear hX
  rcases B₂ with ⟨P₂⟩
  change P₂ = B₁.toPre at hP
  subst hP
  have ec₀ := app_chiW eH el ec eχ ((j₁ : ℕ) + 1)
  rw [← hj] at A₂
  have A₂' : ChrEq (D := (w₁.st Z₁).toD7) (z₁.core.chiW ((j₁ : ℕ) + 1) z₁.core.Q.c.F.val.toRingHom) (w₂.I.C.mu0 j₂) := by
    rw [← ec₀]
    exact A₂
  have hχ : w₁.I.C.mu0 j₁ = w₂.I.C.mu0 j₂ := (GlobalTheory.ChrEqUnique.chrEq_unique _).1 _ _ _ A₁ A₂'
  rcases p₂ with ⟨q₂, hq₂⟩
  have eq : q₂ = p₁.1 := eq_of_heq hp
  subst eq
  have ecc : c₂ = c₁ := eq_of_heq hc
  subst ecc
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c₂ : 𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)
  have hy0 : ((y : 𝓞 B₁.fields.E) : B₁.fields.E) ≠ 0 := by
    intro h0
    have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
    rw [h0', map_zero] at hy
    exact c₂.ne_zero hy.symm
  rw [embLL_chi w₂ j₂ _ c₂ y (Units.mk0 _ hy0) rfl hy.symm, embLL_chi w₁ j₁ p₁ c₂ y (Units.mk0 _ hy0) rfl hy.symm, hχ]

end GlobalTheory.Mem.R3.Rw.ChiTr
