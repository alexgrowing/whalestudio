import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ChartGlue
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (cokernel)

namespace GlobalTheory

namespace Vert.Flag

variable {X Y : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl : Flag E N) (π : Y ⟶ X)

def pull : Flag ((Scheme.Modules.pullback π).obj E) N where
  F i := (Scheme.Modules.pullback π).obj (fl.F i)
  ι i := (Scheme.Modules.pullback π).map (fl.ι i)
  isSubbundle i := SubPull.isSubbundle_pullback X Y π _ _ _ i (fl.isVB i) (fl.isSubbundle i)
  isVB i := (fl.isVB i).pullback π
  step i := (Scheme.Modules.pullback π).map (fl.step i)
  step_ι i := by rw [← Functor.map_comp, fl.step_ι]
  isIso_last := inferInstance

def pullGrIso (i : Fin N) : (Scheme.Modules.pullback π).obj (fl.gr i) ≅ (fl.pull π).gr i :=
  Limits.PreservesCokernel.iso (Scheme.Modules.pullback π) (fl.step i)

theorem map_π_pullGrIso (i : Fin N) :
    (Scheme.Modules.pullback π).map (fl.π i) ≫ (fl.pullGrIso π i).hom = (fl.pull π).π i := by
  have e := Limits.π_comp_cokernelComparison (fl.step i) (Scheme.Modules.pullback π)
  rw [← Limits.PreservesCokernel.iso_inv] at e
  have e' := congrArg (· ≫ (Limits.PreservesCokernel.iso (Scheme.Modules.pullback π) (fl.step i)).hom) e
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at e'
  exact e'.symm

end Vert.Flag

namespace VMetric

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
  {E : X.Modules} {r : ℕ} (fl : Vert.Flag E r) (π : Y ⟶ X) (i : Fin r)

def pullStep (a : AdaptedChart (stepSeq fl i) i 1) : AdaptedChart (stepSeq (fl.pull π) i) i 1 :=
  have := (fl.isVB i.castSucc).isQuasicoherent
  have := (fl.isVB_gr i).isQuasicoherent
  { U := π ⁻¹ᵁ a.U
    e := fun j => pullbackSections π _ le_rfl (a.e j)
    t := fun j => pullbackSections π _ le_rfl (a.t j)
    he := a.he.pullback π
    ht := by
      have h := (a.ht.pullback π).map_iso (fl.pullGrIso π i).hom
      convert h using 2 with j
      rw [← QCoh.pullback_map_app_pullbackSections]
      exact (congr(($(fl.map_π_pullGrIso π i)).app _ _)).symm }

theorem pullStep_frame (a : AdaptedChart (stepSeq fl i) i 1) (j : Fin i ⊕ Fin 1) :
    (pullStep fl π i a).frame j = pullbackSections π _ le_rfl (a.frame j) := by
  have := ((fl.isVB i.succ)).isQuasicoherent
  rcases j with j | j
  · exact QCoh.pullback_map_app_pullbackSections π (fl.step i) _ _
  · rfl

variable {fl π i}

theorem gram_pullStep (h : VMetric p E r) (hπ : π ≫ p = q) (a : AdaptedChart (stepSeq fl i) i 1)
    {z : CxPts q σ} (hz : z ∈ ptsIn q σ (π ⁻¹ᵁ a.U)) :
    (((h.pull π hπ).stepMet (fl.pull π) i).met σ).gram (pullStep fl π i a).frame z =
      ((h.stepMet fl i).met σ).gram a.frame (PtsOver.map π hπ _ z) := by
  have hz' : PtsOver.map π hπ _ z ∈ ptsIn p σ a.U := hz
  ext j l
  change (((h.pull π hπ).met σ).restrict ((fl.pull π).isSubbundle i.succ)
    ((fl.pull π).isVB i.succ)).form _ _ z =
    ((h.met σ).restrict (fl.isSubbundle i.succ) (fl.isVB i.succ)).form _ _ _
  refine (Met.form_restrict _ _ _ _ _ hz).trans (Eq.trans ?_ (Met.form_restrict _ _ _ _ _ hz').symm)
  have e (j) : ((fl.pull π).ι i.succ).app (π ⁻¹ᵁ a.U) ((pullStep fl π i a).frame j) =
      pullbackSections π E le_rfl ((fl.ι i.succ).app a.U (a.frame j)) := by
    rw [pullStep_frame]
    exact QCoh.pullback_map_app_pullbackSections π _ _ _
  rw [e j, e l]
  exact Met.form_pull _ π hπ _ _ _ hz

theorem _root_.GlobalTheory.Met.bcDens_eq_of_gram {S : ShortComplex X.Modules} {S' : ShortComplex Y.Modules}
    {r s : ℕ} {h : Met p σ S.X₂ (r + s)} {h' : Met q σ S'.X₂ (r + s)} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r)
    (h₃' : IsVB S'.X₃ s) (H : h.IsCInf) (H' : h'.IsCInf) (a : AdaptedChart S r s)
    (a' : AdaptedChart S' r s) (c : AlgChart p σ 1) (c' : AlgChart q σ 1) {y : CxPts p σ}
    {z : CxPts q σ} (hy : y ∈ c.e.source) (hz : z ∈ c'.e.source) (ha : y ∈ ptsIn p σ a.U)
    (ha' : z ∈ ptsIn q σ a'.U) (he : c'.e z = c.e y)
    (hg : ∀ᶠ v in 𝓝 (c'.e z), h'.gram a'.frame (c'.e.symm v) = h.gram a.frame (c.e.symm v)) :
    h'.bcDens hS' h₁' h₃' c' z = h.bcDens hS h₁ h₃ c y := by
  rw [Met.bcDens_eq hS' h₁' h₃' a' c' H' hz ha', Met.bcDens_eq hS h₁ h₃ a c H hy ha, Met.bcForm,
    Met.bcForm, extTrace_congr hg, he]

theorem bcDens_pullStep {h : VMetric p E r} (H : h.IsCInf) (hπ : π ≫ p = q) (c : AlgChart p σ 1)
    (c' : AlgChart q σ 1) {z : CxPts q σ} (hz : z ∈ c'.e.source)
    (hz' : PtsOver.map π hπ _ z ∈ c.e.source)
    (he : ∀ w ∈ c'.e.source, PtsOver.map π hπ _ w ∈ c.e.source →
      c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) :
    (((h.pull π hπ).stepMet (fl.pull π) i).met σ).bcDens (stepSeq_shortExact (fl.pull π) i)
        ((fl.pull π).isVB i.castSucc) ((fl.pull π).isVB_gr i) c' z =
      ((h.stepMet fl i).met σ).bcDens (stepSeq_shortExact fl i) (fl.isVB i.castSucc)
        (fl.isVB_gr i) c (PtsOver.map π hπ _ z) := by
  obtain ⟨a, ha⟩ := Met.exists_adapted (stepSeq_shortExact fl i) (fl.isVB i.castSucc)
    (fl.isVB_gr i) (PtsOver.map π hπ _ z)
  have ha' : z ∈ ptsIn q σ (π ⁻¹ᵁ a.U) := ha
  have H₁ : (h.stepMet fl i).IsCInf := H.restrict _ _
  have H₂ : ((h.pull π hπ).stepMet (fl.pull π) i).IsCInf := (H.pull π hπ).restrict _ _
  have hm : Continuous (PtsOver.map π hπ (spMap σ)) := PtsOver.continuous_map π hπ _
  have hS : IsOpen (c'.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' (c.e.source ∩ ptsIn p σ a.U)) :=
    c'.e.open_source.inter ((c.e.open_source.inter (isOpen_ptsIn _)).preimage hm)
  have hn := (isOpen_over c'.e hS).mem_nhds (mem_over c'.e hz (S := _) ⟨hz, hz', ha⟩)
  refine Met.bcDens_eq_of_gram _ _ _ _ _ _ (H₁ σ) (H₂ σ) a (pullStep fl π i a) c c' hz' hz ha ha'
    (he z hz hz') ?_
  filter_upwards [hn] with v hv
  obtain ⟨h₁, h₂, h₃⟩ := hv.2
  have e₁ : c.e.symm v = PtsOver.map π hπ _ (c'.e.symm v) := by
    have := he _ h₁ h₂
    rw [c'.e.right_inv hv.1] at this
    exact (congrArg c.e.symm this).trans (c.e.left_inv h₂)
  rw [e₁]
  exact gram_pullStep h hπ a h₃

end VMetric

end GlobalTheory
