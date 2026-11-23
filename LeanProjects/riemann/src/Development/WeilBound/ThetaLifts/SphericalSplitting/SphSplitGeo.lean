import Development.WeilBound.ThetaLifts.SphericalLattices.SphSplitOf
import Development.WeilBound.ThetaLifts.SphericalLattices.BelowIffRows
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KCoinvOfNarrow
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.BernsteinClosure.RamifiedMultiplicityOne

noncomputable section

namespace PositivityTheory.Sph.SplitPl

open scoped Matrix Topology
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
  GlobalTheory.SplitFlip PositivityTheory.KCo

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

open GlobalTheory.CompanionTheory.KCoNarrow

theorem irrAt_ne (hS : SurjSt) (hI : IrrStNe) {om : Rep σ X W} {v : Pl F}
    {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {ν α : (Fv F v)ˣ →* ℂˣ} (hnd : n ≤ d)
    (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) (hν : USm ν) (hα : USm α) (h1 : ν ≠ 1) : IrrAt om v := by
  rintro N ⟨hAN, hNS, hst⟩
  rcases hI _ n d ν α hnd hν h1 hα (N.map ι) ((aug_le_map hb hD).trans (Submodule.map_mono hAN)) (by
      rintro h₀ _ ⟨ψ, hψ, rfl⟩ -
      obtain ⟨h, hh, hr⟩ := hD.rightOnto h₀
      obtain ⟨ψ₁, h₁, ha, e⟩ := hr ψ (hNS hψ)
      exact ⟨ψ₁, hst h hh ψ hψ ψ₁ h₁ ha, e⟩) with h | h
  · right
    refine le_antisymm hNS fun φ hφ => ?_
    obtain ⟨φ₀, h₀, hf, ha⟩ := exists_full hS hb hD hν h1 hφ
    obtain ⟨χ, hχ, e⟩ := h _ hf
    have e' : χ = φ₀ := hb.2.1 (hNS hχ) h₀ e
    have := add_mem (hAN ha) (e' ▸ hχ)
    rwa [sub_add_cancel] at this
  · left
    refine le_antisymm (fun φ hφ => ?_) hAN
    obtain ⟨φ₀, h₀, hf, ha⟩ := exists_full hS hb hD hν h1 (hNS hφ)
    have hN0 : φ₀ ∈ N := by
      have := sub_mem hφ (hAN ha)
      rwa [sub_sub_cancel] at this
    have := add_mem ha (mem_augAt hb hD h₀ (h _ ⟨φ₀, hN0, rfl⟩ hf))
    rwa [sub_add_cancel] at this

theorem pair_case2 (hI : IrrStNe) (hL : LatSt) {B : Base F E} (hBg : B.IsGood σ)
    {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') {M : Model σ X W} (hM : M.IsGood B.ψ)
    {χX χW : Chr F E} {om : Rep σ X W} (hom : M.IsWeil B.ψ χX χW om) (hHX : IsHecke F E χX) (hHW : IsHecke F E χW)
    (hnd : n ≤ d) (v : Pl F) (t : E →ₐ[F] Fv F v) : SphAt M B.ψ om v ∨ IrrAt om v := by
  obtain ⟨⟨ι₀, hι₀⟩, s1, s2, k⟩ := dictionary_extended F E σ n d B X W M om χX χW hBg ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  have hu := (section_statement F E σ hBg.cm v t).2
  by_cases h1 : chrW χW t = 1
  · left
    have := hX.lat
    have := hW.lat
    obtain ⟨b, hb⟩ := exists_isSplitBasis t X.L hBg.cm
    obtain ⟨c, hc⟩ := exists_isSplitBasis t W.L hBg.cm
    obtain ⟨δ, hδ⟩ := SplitDict.exists_cond hBg.std v
    obtain ⟨ι, hι, hv, hg, hh⟩ := SplitDict.model_Bar hBg hX hW (hM.vac v) hom hb hc hδ (b' := δ • b) rfl
    rw [h1] at hg hh
    refine sphAt_of (α := chrW χX t) hL hι.bij (hM.vac v).1 hv (fun g₀ => ?_) (fun h₀ => ?_)
    · obtain ⟨g, hg', e⟩ := s1 ((δ • b) * g₀ * (δ • b)⁻¹)
      refine ⟨g, hg', ?_⟩
      have := hg g hg'
      rwa [show SplitDict.inB t (δ • b) g = g₀ by
        rw [SplitDict.inB, show Matrix.GeneralLinearGroup.map (piW t) g.1 = (δ • b) * g₀ * (δ • b)⁻¹ from Units.ext e]
        group] at this
    · obtain ⟨h, hh', e⟩ := s2 (c * h₀ * c⁻¹)
      refine ⟨h, hh', ?_⟩
      have := hh h hh'
      rwa [show SplitDict.inB t c h = h₀ by
        rw [SplitDict.inB, show Matrix.GeneralLinearGroup.map (piW t) h.1 = c * h₀ * c⁻¹ from Units.ext e]
        group] at this
  · right
    refine irrAt_ne surjectivity_statement hI hnd hι₀.bij ⟨fun g hg => ⟨_, (k ι₀ hι₀).1 g hg
      (Matrix.GeneralLinearGroup.map (piW t) g.1) rfl⟩, fun g₀ => ?_, fun g hg => ⟨_, (k ι₀ hι₀).2 g hg
        (Matrix.GeneralLinearGroup.map (piW t) g.1) rfl⟩, fun g₀ => ?_⟩ (hu χW hHW) (hu χX hHX) h1
    · obtain ⟨g, hg, e⟩ := s1 g₀
      exact ⟨g, hg, (k ι₀ hι₀).1 g hg g₀ e⟩
    · obtain ⟨g, hg, e⟩ := s2 g₀
      exact ⟨g, hg, (k ι₀ hι₀).2 g hg g₀ e⟩

end PositivityTheory.Sph.SplitPl

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

theorem sphSplit_ne (hI : GlobalTheory.CompanionTheory.KCoNarrow.IrrStNe) (hL : LatSt) : SphSplit := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v ⟨t⟩
  exact ⟨SplitPl.pair_case2 hI hL hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hT.chars.heckeβ
      (PositivityTheory.KCo.isHecke_div hT.chars.heckeβ hT.chars.heckeα) (Nat.le_add_right a a') v t,
    SplitPl.pair_case2 hI hL hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' hT.chars.heckeα
      (PositivityTheory.KCo.isHecke_div hT.chars.heckeα hT.chars.heckeβ) (Nat.le_add_left a' a) v t⟩

theorem sphSplit_geo : SphSplit :=
  sphSplit_ne (GlobalTheory.CompanionTheory.KCoNarrow.irrSt_narrow PositivityTheory.BernsteinRamification.Close.narrowBern) latSt

end PositivityTheory.Sph

end
