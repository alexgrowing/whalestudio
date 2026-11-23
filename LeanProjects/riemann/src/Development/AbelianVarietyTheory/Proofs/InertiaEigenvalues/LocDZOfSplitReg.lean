import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolLpCharOfUnr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DepthZeroAssembly

open GlobalTheory.WeilDeligne (WD Weil ineIncl TeichmullerInertiaLabelCondition Wild Wild_le_Ine)
open GlobalTheory.SplitRead.BlockParam (charPol_lpChar_of_unr twistIrr)

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w} {g : ℕ} [Fact g.Prime]

theorem lab_lpChar_of_unr (τ : AlgebraicClosure (ZMod g) →* ℂ) (γ : G E Ω) (x χ : WD h) (hx : x.unr)
    (hd : χ.lpDim = 1) (u : ZMod g) (hχ : WD.lab τ γ χ = X - C u) :
    WD.lab τ γ (x.lpChar χ) = (X - C u) ^ x.lpDim := by
  have H : TeichmullerInertiaLabelCondition B w τ γ := by
    by_contra H
    rw [WD.lab_of_not H] at hχ
    have := congrArg natDegree hχ
    rw [natDegree_one, natDegree_X_sub_C] at this
    exact zero_ne_one this
  have htχ : WD.tame χ := WD.tame_of_natDegree_lab (by rw [hχ, natDegree_X_sub_C, hd])
  have hc1 : ∀ σ : Ine (F := E) B, (σ : G E Ω) ∈ Wild E B → χ.charPol (ineIncl h σ) = X - C 1 := by
    intro σ hσ
    have := (WD.tame_iff_inePol χ).1 htχ σ hσ
    rw [WD.inePol_of_mem_Ine _ σ.2, hd, pow_one] at this
    rw [C_1]; exact this
  have hdim : (x.lpChar χ).lpDim = x.lpDim := by
    obtain ⟨σ, hσ⟩ : ∃ σ : Ine (F := E) B, (σ : G E Ω) ∈ Wild E B := ⟨1, (Wild E B).one_mem⟩
    have h1 := charPol_lpChar_of_unr x χ hx σ 1 (hc1 σ hσ)
    rw [← WD.charPol_natDegree (x.lpChar χ) (ineIncl h σ), h1, natDegree_pow, natDegree_X_sub_C, mul_one]
  have ht : WD.tame (x.lpChar χ) := by
    rw [WD.tame_iff_inePol]
    intro σ hσ
    rw [WD.inePol_of_mem_Ine _ (Wild_le_Ine hσ), hdim,
      charPol_lpChar_of_unr x χ hx ⟨σ, Wild_le_Ine hσ⟩ 1 (hc1 ⟨σ, Wild_le_Ine hσ⟩ hσ), C_1]
  set p := χ.charPol (ineIncl h ⟨γ, H.2.1⟩) with hp
  have hpm : p.Monic := WD.charPol_monic _ _
  have hpd : p.natDegree = 1 := by rw [hp, WD.charPol_natDegree, hd]
  have hpe : p = X - C (-p.coeff 0) := by rw [map_neg, sub_neg_eq_add]; exact hpm.eq_X_add_C hpd
  have hχ' := (WD.lab_eq_iff_of_tame H htχ).1 hχ
  have hr1 := WD.rootsBar_X_sub_C_pow u 1
  rw [pow_one, one_nsmul] at hr1
  rw [WD.inePol_of_mem_Ine _ H.2.1, ← hp, hpe, roots_X_sub_C, hr1,
    Multiset.map_singleton, Multiset.singleton_inj] at hχ'
  rw [WD.lab_eq_iff_of_tame H ht, WD.inePol_of_mem_Ine _ H.2.1,
    charPol_lpChar_of_unr x χ hx ⟨γ, H.2.1⟩ (-p.coeff 0) (hpe ▸ rfl), roots_pow, roots_X_sub_C,
    WD.rootsBar_X_sub_C_pow, Multiset.map_nsmul, Multiset.map_singleton, hχ'.2]
  exact ⟨(monic_X_sub_C u).pow _, rfl⟩

end Local

end GlobalTheory.DepthZeroAssembly

namespace GlobalTheory.DepthZeroAssembly

open GlobalTheory.WeilDeligne (WD)
open GlobalTheory.SplitRead.BlockParam (twistIrr)

theorem locDZ_of_split_reg : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), SplitLoc hL D → RegLoc hL D → LocDZ hL D := by
  intro hL D hS hR k v χ hχ u π ρ f ht hlab hser hsq hnr hx
  obtain ⟨π₁, π₂, hsph, e, y, hy1, hy2⟩ := hS k v χ hχ u π ρ f ht hlab hser hnr hx
  obtain ⟨hm1, hl1⟩ := hR k v π₁ ρ f hser hsq ⟨y, hy1, hy2⟩
  have L : RecLaws (rcAt hL D (D.naut.plGw k v)) :=
    (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))).recLaws
  have e' : Nonempty (π.π.Equiv (GlobalTheory.SmGL.prod₂ π₁.π (twistIrr π₂ χ hχ).π)) := e
  have e1 := L.prod D.R.r D.R.t π₁ (twistIrr π₂ χ hχ) π e'
  have e2 := L.twist D.R.t χ (Irr.ofDet 1 χ hχ) π₂ (twistIrr π₂ χ hχ) ⟨.refl _⟩ ⟨.refl _⟩
  have hu := (L.sph _ π₂).2 hsph
  refine ⟨?_, ?_⟩
  · rw [e1, WD.monomial_sum_iff, e2, WD.monomial_char_iff _ _ (L.dim _ _)]
    exact ⟨hm1, WD.unr_mono0 _ hu⟩
  · unfold labAt at hl1 hlab ⊢
    rw [e1, WD.lab_lpSum, e2, lab_lpChar_of_unr _ _ _ _ hu (L.dim _ _) u hlab, hl1, L.dim]

end GlobalTheory.DepthZeroAssembly
