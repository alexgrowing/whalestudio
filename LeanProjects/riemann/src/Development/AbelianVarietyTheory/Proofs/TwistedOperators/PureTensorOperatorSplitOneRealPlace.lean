import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace GlobalTheory.TrSplit

open MeasureTheory

theorem sigmaFinite_update {ι : Type*} [DecidableEq ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (w : ι) (c : α w) (i : ι) :
    SigmaFinite (Function.update μ w (Measure.dirac c) i) := by
  rcases eq_or_ne i w with rfl | h
  · rw [Function.update_self]; infer_instance
  · rw [Function.update_of_ne h]; infer_instance

theorem map_update_prod_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (w : ι) (c : α w)
    [∀ i, SigmaFinite (Function.update μ w (Measure.dirac c) i)] :
    ((μ w).prod (Measure.pi (Function.update μ w (Measure.dirac c)))).map
      (fun p => Function.update p.2 w p.1) = Measure.pi μ := by
  have hm : Measurable fun p : α w × (∀ i, α i) => Function.update p.2 w p.1 :=
    (measurable_update' (a := w)).comp measurable_swap
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have e : (fun p : α w × (∀ i, α i) => Function.update p.2 w p.1) ⁻¹' Set.univ.pi s =
      s w ×ˢ Set.univ.pi (Function.update s w Set.univ) := by
    ext ⟨x, a⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h w, fun i => ?_⟩
      rcases eq_or_ne i w with rfl | hi
      · simp
      · simpa [Function.update_of_ne hi] using h i
    · rintro ⟨h1, h2⟩ i
      rcases eq_or_ne i w with rfl | hi
      · simpa using h1
      · simpa [Function.update_of_ne hi] using h2 i
  rw [e, Measure.prod_prod, Measure.pi_pi, Fintype.prod_eq_mul_prod_compl w,
    Fintype.prod_eq_mul_prod_compl w (fun i => μ i (s i))]
  simp only [Function.update_self, Measure.dirac_apply_of_mem (Set.mem_univ c), one_mul]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≠ w := by simpa using hi
  simp [Function.update_of_ne hi']

end GlobalTheory.TrSplit

noncomputable section

namespace GlobalTheory.TrSplit

open MeasureTheory GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem projArch_archFinEquiv_symm (u : InfinitePlace F) (p : (∀ u, GArch σ J u) × GFin σ J) :
    projArch σ J u ((archFinEquiv σ J).symm p) = p.1 u :=
  congrFun (congrArg Prod.fst ((archFinEquiv σ J).apply_symm_apply p)) u

theorem projFin_archFinEquiv_symm (p : (∀ u, GArch σ J u) × GFin σ J) :
    projFin σ J ((archFinEquiv σ J).symm p) = p.2 :=
  congrArg Prod.snd ((archFinEquiv σ J).apply_symm_apply p)

theorem proj_archFinEquiv_symm (v : HeightOneSpectrum (𝓞 F)) (p : (∀ u, GArch σ J u) × GFin σ J) :
    proj σ J v ((archFinEquiv σ J).symm p) = projFinLoc σ J v p.2 := by
  rw [← projFinLoc_projFin, projFin_archFinEquiv_symm]

variable (σ J) in

def killAt [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) :
    ((∀ u, GArch σ J u) × GFin σ J) →* GAd σ J :=
  ((archFinEquiv σ J).symm : ((∀ u, GArch σ J u) × GFin σ J) →* GAd σ J).comp
    (MonoidHom.prodMap
      { toFun := fun a => Function.update a w 1
        map_one' := by simp
        map_mul' := fun a b => by
          funext u
          rcases eq_or_ne u w with rfl | h
          · simp
          · simp [Function.update_of_ne h] }
      (MonoidHom.id _))

theorem killAt_apply [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (z : (∀ u, GArch σ J u) × GFin σ J) :
    killAt σ J w z = (archFinEquiv σ J).symm (Function.update z.1 w 1, z.2) := rfl

theorem continuous_killAt [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) : Continuous (killAt σ J w) := by
  change Continuous fun z : (∀ u, GArch σ J u) × GFin σ J => (archFinEquiv σ J).symm (Function.update z.1 w 1, z.2)
  exact (archFinEquiv σ J).symm.continuous.comp ((continuous_fst.update w continuous_const).prodMk continuous_snd)

theorem embArch_mul_killAt [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (x : GArch σ J w)
    (a : ∀ u, GArch σ J u) (b : GFin σ J) :
    embArch σ J w x * killAt σ J w (a, b) = (archFinEquiv σ J).symm (Function.update a w x, b) := by
  refine GAd_ext σ J (fun u => ?_) fun v => ?_
  · rw [map_mul, killAt_apply, projArch_archFinEquiv_symm, projArch_archFinEquiv_symm]
    rcases eq_or_ne u w with rfl | h
    · simp
    · simp [Function.update_of_ne h, projArch_embArch_ne σ J h]
  · rw [map_mul, killAt_apply, proj_archFinEquiv_symm, proj_archFinEquiv_symm, proj_embArch, one_mul]

theorem commute_embArch_killAt [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (x : GArch σ J w)
    (z : (∀ u, GArch σ J u) × GFin σ J) :
    embArch σ J w x * killAt σ J w z = killAt σ J w z * embArch σ J w x := by
  refine GAd_ext σ J (fun u => ?_) fun v => ?_
  · rw [map_mul, map_mul, killAt_apply, projArch_archFinEquiv_symm]
    rcases eq_or_ne u w with rfl | h
    · simp
    · simp [Function.update_of_ne h, projArch_embArch_ne σ J h]
  · rw [map_mul, map_mul, proj_embArch, one_mul, mul_one]

end GlobalTheory.TrSplit

namespace GlobalTheory.TrSplit

open MeasureTheory GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exists_repOp_tensor_eq_mul {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
    {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)} {μ : Measure (GAd σ J)}
    (hμ : IsRestrictedProd σ J L μa μf μ) {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}
    (hfa : ∀ w, fa w ∈ CcArch σ J w) (hff : IsFinFamily σ J L ff)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : GAd σ J →* (H →L[ℂ] H)} (hπ : IsUnitaryRep π) (w : InfinitePlace F) :
    ∃ Q : H →L[ℂ] H, (∀ g, Q * π (embArch σ J w g) = π (embArch σ J w g) * Q) ∧
      repOp π μ (tensor σ J fa ff) = repOp (π.comp (embArch σ J w)) (μa w) (fa w) * Q := by
  classical
  have := hμ.haar_arch
  have := hμ.haar_loc
  have := hμ.haar
  obtain ⟨ν, hν⟩ := (existsUnique_isRestrictedProdFin σ J L μf hμ.eventually_eq_one).exists
  haveI : ν.IsHaarMeasure := (isRestrictedProdFin_iff.1 hν).2.1
  have hmap := hμ.map_archFin hν
  let μa' := Function.update μa w (Measure.dirac 1)
  haveI : ∀ u, SigmaFinite (μa' u) := sigmaFinite_update μa w 1
  let ρ := (Measure.pi μa').prod ν
  let fa' : ∀ u, GArch σ J u → ℂ := Function.update fa w (fun _ => 1)
  let Ψ : (∀ u, GArch σ J u) × GFin σ J → ℂ := fun z => (∏ u, fa' u (z.1 u)) * tensorFin σ J ff z.2
  let π' := π.comp (killAt σ J w)
  have hπ' : IsUnitaryRep π' :=
    ⟨fun g v => hπ.norm_apply _ v, fun v => (hπ.continuous_apply v).comp (continuous_killAt w)⟩
  have hπw : IsUnitaryRep (π.comp (embArch σ J w)) :=
    ⟨fun g v => hπ.norm_apply _ v, fun v => (hπ.continuous_apply v).comp (continuous_embArch σ J w)⟩
  have hcfa : ∀ u, Continuous (fa u) := fun u => continuous_of_mem_ccSmooth (continuous_archCoord σ J u) (hfa u)
  have h1 : Integrable (fun a : ∀ u, GArch σ J u => ∏ u, fa' u (a u)) (Measure.pi μa') :=
    Integrable.fintype_prod_dep (f := fa') (μ := μa') fun u => by
      rcases eq_or_ne u w with rfl | h
      · simp [fa', μa']
      · rw [show fa' u = fa u from Function.update_of_ne h _ _, show μa' u = μa u from Function.update_of_ne h _ _]
        exact (hcfa u).integrable_of_hasCompactSupport (hfa u).1
  have h2 : Integrable (tensorFin σ J ff) ν :=
    hff.tensorFin_mem.1.continuous.integrable_of_hasCompactSupport hff.tensorFin_mem.2
  have hΨint : Integrable Ψ ρ := h1.mul_prod h2
  have hQ := hπ'.isRepOp_of_integrable hΨint
    (fun v => hΨint.aestronglyMeasurable.smul (hπ'.continuous_apply v).aestronglyMeasurable)
  refine ⟨repOp π' ρ Ψ, fun x => ?_, ?_⟩
  · ext v
    simp only [ContinuousLinearMap.mul_apply]
    rw [(hQ _).2, (hQ v).2, ← ContinuousLinearMap.integral_comp_comm _ (hQ v).1]
    congr 1
    funext z
    simp only [map_smul, π', MonoidHom.comp_apply]
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul,
      commute_embArch_killAt]
  · have hfc := continuous_of_mem_ccAd (tensor_mem_ccAd hfa hff)
    set f := tensor σ J fa ff with hfdef
    let e := archFinEquiv σ J
    ext v
    rw [ContinuousLinearMap.mul_apply, hπ.repOp_apply hfc.1 hfc.2, hπw.repOp_apply (hcfa w) (hfa w).1, (hQ v).2]
    let Fn : (∀ u, GArch σ J u) × GFin σ J → H := fun y => f (e.symm y) • π (e.symm y) v
    have hFc : Continuous Fn :=
      (hfc.1.comp e.symm.continuous).smul ((hπ.continuous_apply v).comp e.symm.continuous)
    have hFint : Integrable Fn ((Measure.pi μa).prod ν) := by
      rw [← hmap]
      have : Integrable (fun g => f g • π g v) μ :=
        (hfc.1.smul (hπ.continuous_apply v)).integrable_of_hasCompactSupport hfc.2.smul_right
      refine (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv Fn).2 ?_
      convert this using 1
      funext g
      change f (e.symm (e g)) • π (e.symm (e g)) v = _
      rw [e.symm_apply_apply]
    have h1 : ∫ g, f g • π g v ∂μ = ∫ y, Fn y ∂((Measure.pi μa).prod ν) := by
      rw [← hmap]
      rw [show (e : GAd σ J → _) = e.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
      congr 1
      funext g
      change _ = f (e.symm (e g)) • π (e.symm (e g)) v
      rw [e.symm_apply_apply]
    let T : GArch σ J w × ((∀ u, GArch σ J u) × GFin σ J) → (∀ u, GArch σ J u) × GFin σ J :=
      fun p => (Function.update p.2.1 w p.1, p.2.2)
    have hU : Measurable fun p : GArch σ J w × (∀ u, GArch σ J u) => Function.update p.2 w p.1 :=
      (measurable_update' (a := w)).comp measurable_swap
    have hTm : Measurable T :=
      ((measurable_update' (a := w)).comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).prodMk
        (measurable_snd.comp measurable_snd)
    have hT : MeasurePreserving T ((μa w).prod ρ) ((Measure.pi μa).prod ν) := by
      refine ⟨hTm, ?_⟩
      have hA := map_update_prod_pi μa w (1 : GArch σ J w)
      have hassoc := (measurePreserving_prodAssoc (μa w) (Measure.pi μa') ν).map_eq
      show Measure.map T ((μa w).prod ((Measure.pi μa').prod ν)) = _
      rw [← hassoc, Measure.map_map hTm MeasurableEquiv.prodAssoc.measurable]
      have e1 : T ∘ MeasurableEquiv.prodAssoc =
          Prod.map (fun p : GArch σ J w × (∀ u, GArch σ J u) => Function.update p.2 w p.1) id := by
        funext ⟨⟨x, a⟩, b⟩
        rfl
      rw [e1, ← Measure.map_prod_map _ _ hU measurable_id, hA, Measure.map_id]
    have hpt : ∀ x (z : (∀ u, GArch σ J u) × GFin σ J),
        Fn (T (x, z)) = fa w x • π (embArch σ J w x) (Ψ z • π' z v) := by
      rintro x ⟨a, b⟩
      have hg : e.symm (Function.update a w x, b) = embArch σ J w x * killAt σ J w (a, b) :=
        (embArch_mul_killAt w x a b).symm
      have hf : f (e.symm (Function.update a w x, b)) = fa w x * Ψ (a, b) := by
        simp only [hfdef, e, tensor, projArch_archFinEquiv_symm, proj_archFinEquiv_symm, Ψ, fa', tensorFin]
        rw [Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w
          (fun u => Function.update fa w (fun _ => (1 : ℂ)) u (a u))]
        simp only [Function.update_self, one_mul]
        rw [Finset.prod_congr rfl fun u hu => (show fa u (Function.update a w x u) =
          Function.update fa w (fun _ => (1 : ℂ)) u (a u) by
            have hu' : u ≠ w := by simpa using hu
            simp [Function.update_of_ne hu'])]
        ring
      change f (e.symm (Function.update a w x, b)) • π (e.symm (Function.update a w x, b)) v = _
      rw [hf, hg, map_mul, mul_smul, ContinuousLinearMap.mul_apply, map_smul]
      rfl
    rw [h1, ← hT.map_eq, integral_map hT.measurable.aemeasurable (hT.map_eq ▸ hFc.aestronglyMeasurable),
      integral_prod _ (by
        have := (hT.map_eq ▸ hFint : Integrable Fn (((μa w).prod ρ).map T))
        exact this.comp_aemeasurable hT.measurable.aemeasurable)]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [hpt]
    rw [integral_smul, ContinuousLinearMap.integral_comp_comm _ (hQ v).1]
    rfl

end GlobalTheory.TrSplit

namespace GlobalTheory.TrSplit

theorem repOp_tensor_split : ∀ (D : D7) (V : HSp D) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ w, ∃ Q : H →L[ℂ] H, (∀ g, Q * π (embArch D.sp.cm.sig V.gram w g) = π (embArch D.sp.cm.sig V.gram w g) * Q) ∧ repOp π μ (tensor D.sp.cm.sig V.gram fa ff) = repOp (π.comp (embArch D.sp.cm.sig V.gram w)) (μa w) (fa w) * Q := by
  intro D V μa μf μ hμ fa ff hfa hff H _ _ _ π hπ w
  exact exists_repOp_tensor_eq_mul hμ hfa hff hπ w

end GlobalTheory.TrSplit
