import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOfNotApartOfNotSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorFixedByProductLocalLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutRepDefiniteUnitarySpannedBySplitComponentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryIntegralBelowPlaceCompactOpenStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutFormFixedByIntegralPointsAlmostAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLevelAwayDefiniteUnitaryLevelFromLocalLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedOfFixedByLocalLevelsStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem apart_of_apart_not_apart {w w₀ u : HeightOneSpectrum (𝓞 E)} (hw : Apart w w₀) (hu : ¬ Apart u w₀) : Apart u w := by
  unfold Apart at *
  intro h
  exact hw (h.symm.trans (not_not.1 hu))

theorem mem_levelOf_iff_of_locU {w₀ w : HeightOneSpectrum (𝓞 E)} {H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)}
    (hle : ∀ w, H w ≤ locU a w) (hfib : ∀ w u, ¬ Apart w u → H w = H u) (hw : Apart w w₀) {x : UA E a}
    (hx : x ∈ locU a w) : x ∈ levelOf a w₀ H ↔ x ∈ H w := by
  have hx' := (GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx
  constructor
  · intro h
    obtain ⟨y, hy, e⟩ := (mem_levelOf.1 h).2.2 w hw
    rw [← eq_of_cLoc_eq (hle w hy) hx e]
    exact hy
  · intro h
    refine mem_levelOf.2 ⟨hx'.1, fun u hu => hx'.2 u (apart_of_apart_not_apart hw hu), fun w' hw' => ?_⟩
    by_cases hw'w : Apart w' w
    · exact ⟨1, one_mem _, by rw [map_one, hx'.2 w' hw'w]⟩
    · exact ⟨x, by rw [hfib w' w hw'w]; exact h, rfl⟩

theorem map_eq_image {w : HeightOneSpectrum (𝓞 E)} {L : Subgroup (UA E a)} (hL : L ≤ locU a w)
    (e : locU a w ≃ₜ* GL (Fin a) (w.adicCompletion E)) (he : ∀ x : locU a w, e x = cLoc w (x : UA E a)) :
    ((L.map (cLoc w) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) =
      e '' ((L.subgroupOf (locU a w) : Subgroup (locU a w)) : Set (locU a w)) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hL hx⟩, Subgroup.mem_subgroupOf.2 hx, he _⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, Subgroup.mem_subgroupOf.1 hy, (he y).symm⟩

theorem injective_of_compAlong {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W}
    (hirr : σ.IsIrreducible) (f : W →ₗ[ℂ] (UA E a → ℂ)) (hf0 : f ≠ 0)
    (hf : ∀ (x : locU a w) v, f (σ (((cLoc w).comp (locU a w).subtype) x) v) = RU E a x (f v)) :
    Function.Injective f := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  rw [← LinearMap.ker_eq_bot]
  refine (((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hirr).2 _ (fun g u hu => ?_)).resolve_right fun h => hf0 ?_
  · rw [LinearMap.mem_ker] at hu ⊢
    have := hf (e.symm g) u
    have hg : ((cLoc w).comp (locU a w).subtype) (e.symm g) = g := by
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← he, e.apply_symm_apply]
    rw [hg] at this
    rw [this, hu, map_zero]
  · refine LinearMap.ext fun v => ?_
    have : v ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    simpa using this

theorem fix_of_fixed {U : Submodule ℂ (UA E a → ℂ)} {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hc : IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ)
    {J : Subgroup (GL (Fin a) (w.adicCompletion E))} (hJ : GlobalTheory.PRep.fixed σ.ρ J ≠ ⊥) :
    ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ J → RU E a x φ = φ := by
  obtain ⟨hirr, f, hf0, hfU, hf⟩ := hc
  have hinj := injective_of_compAlong hw hirr f hf0 hf
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hJ
  refine ⟨f v, hfU v, fun h => hv0 (hinj (by rw [h, map_zero])), fun x hx hxJ => ?_⟩
  have := hf ⟨x, hx⟩ v
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, GlobalTheory.LGrp.mem_fixed.1 hv _ hxJ] at this
  exact this.symm

theorem fixed_ne_bot_of_fix {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) {w : HeightOneSpectrum (𝓞 E)}
    (hw : IsSplitAt w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hc : IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ)
    {L : Subgroup (UA E a)} (hL : L ≤ locU a w) {φ : UA E a → ℂ} (hφU : φ ∈ U) (hφ0 : φ ≠ 0)
    (hφ : ∀ x ∈ L, RU E a x φ = φ) : GlobalTheory.PRep.fixed σ.ρ (L.map (cLoc w)) ≠ ⊥ := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hp : (cLoc w).comp (locU a w).subtype = e.toMulEquiv.toMonoidHom := MonoidHom.ext fun x => (he x).symm
  have hirr : Representation.IsIrreducible (σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) := by
    rw [hp]; exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ.ρ e.toMulEquiv σ.irred
  have hsup := GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component E a U hU w hw σ hc φ hφU
  let ι := {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}
  have hf' : ∀ (i : ι) (g : locU a w) (u : σ.V), i.1 ((σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) g u) =
      ((RU E a).comp (locU a w).subtype) g (i.1 u) := fun i g u => i.2.2 g u
  have hK : ∀ k ∈ {x : locU a w | (x : UA E a) ∈ L}, ((RU E a).comp (locU a w).subtype) k φ = (1 : ℂ) • φ :=
    fun k hk => by rw [one_smul]; exact hφ k.1 hk
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.SplitEigen.exists_eigen_of_mem_iSup (ι := ι) ((RU E a).comp (locU a w).subtype)
    (σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) hirr (fun i => i.1) hf'
    {x : locU a w | (x : UA E a) ∈ L} (fun _ => 1) φ hφ0 hK hsup
  refine (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 ?_, hv0⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hv ⟨x, hL hx⟩ hx
  rw [one_smul] at this
  exact this

theorem KGL_le_map {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) :
    GlobalTheory.LFun.KGL w a ≤ (intU a w).map (cLoc w) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  intro g hg
  have h1 : cLoc w ((e.symm g : locU a w) : UA E a) = g := by rw [← he, e.apply_symm_apply]
  exact ⟨(e.symm g).1, mem_intU_of (e.symm g).2 (by rw [h1]; exact hg), h1⟩

end GlobalTheory.Cong.AdaptLev

end
