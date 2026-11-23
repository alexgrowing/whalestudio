import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoExcludedParameterOfLiftParameters
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.TwistChart

variable {D : D7}

theorem isIdemOf_idem {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) :
    IsIdemOf φ (GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ)) := by
  refine ⟨GlobalTheory.EmbChart.isSplitIdem_idem _, ?_, GlobalTheory.SplitProjChart.rdA_idem φ⟩
  rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add, add_sub_cancel]
  rfl

theorem exists_unif (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ ϖ : (Fv D.host.F v)ˣ, ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) =
      ValuativeRel.uniformizer (Fv D.host.F v) := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (Fv D.host.F v))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact ValuativeRel.uniformizer_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

theorem unit_section {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) {e : AE D} (he : IsIdemOf φ e) :
    ∃ U : (Fv D.host.F v)ˣ →* (AE D)ˣ, (∀ y, (1 - e) * (U y : AE D) = 1 - e ∧ rdA φ (U y : AE D) = y) ∧
      ∀ (x : AE D) (y : (Fv D.host.F v)ˣ), (1 - e) * x = 1 - e → rdA φ x = y → x = U y := by
  have hπ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hee : e * e = e := he.1.1
  obtain ⟨sec, hsec⟩ : ∃ sec : Fv D.host.F v → AE D, ∀ y, rdA φ (sec y) = y :=
    ⟨fun y => (hπ.1 y).choose, fun y => (hπ.1 y).choose_spec⟩
  have hf1 : ∀ y, (1 - e) * ((1 - e) + e * sec y) = 1 - e := fun y => by
    linear_combination (1 - sec y) * hee
  have hf2 : ∀ y, rdA φ ((1 - e) + e * sec y) = y := fun y => by
    rw [map_add, map_sub, map_mul, map_one, he.2.2, hsec]; ring
  have key : ∀ x y, (1 - e) * x = 1 - e → rdA φ x = y → x = (1 - e) + e * sec y := by
    intro x y h1 h2
    have h3 : e * (x - sec y) = 0 := (hπ.2.1 _).1 (by rw [map_sub, h2, hsec, sub_self])
    have h4 : e * x = e * sec y := by rw [mul_sub] at h3; exact sub_eq_zero.1 h3
    calc x = (1 - e) * x + e * x := by ring
      _ = (1 - e) + e * sec y := by rw [h1, h4]
  have hmul : ∀ y z, (1 - e) + e * sec (y * z) = ((1 - e) + e * sec y) * ((1 - e) + e * sec z) := fun y z =>
    (key _ _ (by rw [← mul_assoc, hf1, hf1]) (by rw [map_mul, hf2, hf2])).symm
  have hone : (1 - e) + e * sec 1 = 1 := (key 1 1 (mul_one _) (map_one _)).symm
  let f : (Fv D.host.F v)ˣ → (AE D)ˣ := fun y =>
    ⟨(1 - e) + e * sec y, (1 - e) + e * sec ((y⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v),
      by rw [← hmul, Units.mul_inv, hone], by rw [← hmul, Units.inv_mul, hone]⟩
  exact ⟨MonoidHom.mk' f fun y z => Units.ext (by simp only [f, Units.val_mul]; exact hmul y z),
    fun y => ⟨hf1 y, hf2 y⟩, fun x y h1 h2 => key x y h1 h2⟩

end GlobalTheory.TwistChart

namespace GlobalTheory.TwistChart

variable {D : D7}

def blockEquiv (n r k t : ℕ) (h : n = r + k * t) : Fin r ⊕ Blocks k t ≃ Fin n :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sigmaEquivProd _ _).trans finProdFinEquiv)).trans
    (finSumFinEquiv.trans (finCongr h.symm))

theorem blockEquiv_inl (n r k t : ℕ) (h : n = r + k * t) (i : Fin r) : ((blockEquiv n r k t h (.inl i) : Fin n) : ℕ) = i := by
  simp [blockEquiv]

theorem exists_isChart (s : PiLocalization₂ D) (k : ℕ) (hrank : s.V.rank = D.R.r + k * D.R.t) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (φ : SplitProj D v) {e : AE D} (he : IsIdemOf φ e) : ∃ ι, IsChart s k φ ι := by
  have hπ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hJ := GlobalTheory.NoExcl.isHermND_gram s.V
  let ε := blockEquiv s.V.rank D.R.r k D.R.t hrank
  let re : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) ≃* GL (Fin s.V.rank) (Fv D.host.F v) :=
    Units.mapEquiv (Matrix.reindexAlgEquiv (Fv D.host.F v) (Fv D.host.F v) ε).toRingEquiv.toMulEquiv
  let L := GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (GlobalTheory.AdelicU.chartEmb hπ) (frCo φ s.β)
  let ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V :=
    (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v).comp (L.symm.toMulEquiv.toMonoidHom.comp re.toMonoidHom)
  refine ⟨ι, ε, blockEquiv_inl _ _ _ _ hrank, fun y => ⟨?_, ?_⟩⟩
  · change GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v (ι y)) = ι y
    simp only [ι, MonoidHom.comp_apply, GlobalTheory.AdelicU.proj_emb_self]
  · have h1 : grpCo φ s.V (frCo φ s.β) (ι y) = GlobalTheory.SplitHecke.rho s.V (rdA φ) (frCo φ s.β) (ι y) := by
      refine Units.ext ?_
      rw [GlobalTheory.SplitHecke.rho_val]
      rfl
    rw [h1, GlobalTheory.AdelicU.rho_eq_splitEquivIn hπ s.V hJ]
    simp only [ι, L, MonoidHom.comp_apply, GlobalTheory.AdelicU.proj_emb_self]
    have h2 : L (L.symm (re y)) = re y := L.apply_symm_apply _
    change (L (L.symm (re y))).1.submatrix ε ε = y.1
    rw [h2]
    ext i j
    simp [re]

end GlobalTheory.TwistChart

namespace GlobalTheory.TwistChart

open GlobalTheory.ChainOnto GlobalTheory.ChainTw

theorem charts_at_twist : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, (∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP) ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → (∃ e, IsIdemOf φ e) ∧ (∃ x ϖ, IsLocUnif φ x ϖ) ∧ (∃ ι, IsChart s j φ ι) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : (Fv D.host.F v)ˣ →* ℂˣ, GlobalTheory.SmGL.IsUnitaryChar μ ∧ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) := by
  intro D c w hw j _ s hs PP hPP
  classical
  have hPg : PP ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_right _ hPP
  obtain ⟨-, ⟨es, hes, -⟩, -⟩ := hw.com.split
  refine ⟨?_, fun v φ _ => ?_⟩
  · obtain ⟨v, φ, -, h⟩ := (GlobalTheory.SplitIdemDict.idem_dictionary D).1 _ _ (hes PP hPg)
    exact ⟨v, φ, h⟩
  have he := isIdemOf_idem φ
  obtain ⟨U, hU1, hU2⟩ := unit_section φ he
  have huniq := (GlobalTheory.SplitProjChart.chart_rdA D v φ _ he).2.2.2.2
  obtain ⟨hr, -, hst⟩ := hs
  refine ⟨⟨_, he⟩, ?_, exists_isChart s j hst.rank φ he, fun χ => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := exists_unif (D := D) v
    exact ⟨U ϖ, ϖ, _, he, (hU1 ϖ).1, (hU1 ϖ).2, hϖ⟩
  · refine ⟨(Circle.toUnits.comp χ).comp U, fun y => ?_, fun x y ⟨e', he', h1, h2⟩ => ?_⟩
    · exact Circle.norm_coe _
    · obtain rfl := huniq e' he'
      have hx : x = U y := Units.ext (hU2 _ _ h1 h2)
      rw [hx]
      rfl

end GlobalTheory.TwistChart
