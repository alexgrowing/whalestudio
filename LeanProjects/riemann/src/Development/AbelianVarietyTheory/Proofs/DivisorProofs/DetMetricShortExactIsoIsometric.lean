import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricIsometricOfIsometry
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoSeq

open GlobalTheory.VBExt (AdaptedChart)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
  {S S' : ShortComplex X.Modules} {r s : ℕ}

theorem f_inv (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂) (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) :
    S'.f ≫ e₂.inv = e₁.inv ≫ S.f := by
  rw [Iso.comp_inv_eq, Category.assoc, ← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

def homThird (hS : S.ShortExact) (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂)
    (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) : S.X₃ ⟶ S'.X₃ :=
  (Limits.CokernelCofork.IsColimit.desc' hS.gIsCokernel (e₂.hom ≫ S'.g) (by
    rw [← Category.assoc, ← he, Category.assoc, S'.zero, Limits.comp_zero])).1

theorem g_homThird (hS : S.ShortExact) (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂)
    (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) : S.g ≫ homThird hS e₁ e₂ he = e₂.hom ≫ S'.g :=
  (Limits.CokernelCofork.IsColimit.desc' hS.gIsCokernel _ _).2

def isoThird (hS : S.ShortExact) (hS' : S'.ShortExact) (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂)
    (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) : S.X₃ ≅ S'.X₃ where
  hom := homThird hS e₁ e₂ he
  inv := homThird hS' e₁.symm e₂.symm (f_inv e₁ e₂ he).symm
  hom_inv_id := Limits.Cofork.IsColimit.hom_ext hS.gIsCokernel (by
    change S.g ≫ _ ≫ _ = S.g ≫ 𝟙 _
    rw [← Category.assoc, g_homThird, Category.assoc, g_homThird, Iso.symm_hom,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id])
  inv_hom_id := Limits.Cofork.IsColimit.hom_ext hS'.gIsCokernel (by
    change S'.g ≫ _ ≫ _ = S'.g ≫ 𝟙 _
    rw [← Category.assoc, g_homThird, Category.assoc, g_homThird, Iso.symm_hom,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id])

theorem g_isoThird (hS : S.ShortExact) (hS' : S'.ShortExact) (e₁ : S.X₁ ≅ S'.X₁)
    (e₂ : S.X₂ ≅ S'.X₂) (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) :
    S.g ≫ (isoThird hS hS' e₁ e₂ he).hom = e₂.hom ≫ S'.g :=
  g_homThird hS e₁ e₂ he

variable (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂) (e₃ : S.X₃ ≅ S'.X₃)
  (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) (hg : S.g ≫ e₃.hom = e₂.hom ≫ S'.g)

include hg in

theorem app_g (U : X.Opens) (x : Γ(S.X₂, U)) :
    S'.g.app U (e₂.hom.app U x) = e₃.hom.app U (S.g.app U x) := by
  have := congr(($(hg)).app U x)
  simpa [Scheme.Modules.Hom.comp_app] using this.symm

include he in

theorem app_f (U : X.Opens) (x : Γ(S.X₁, U)) :
    S'.f.app U (e₁.hom.app U x) = e₂.hom.app U (S.f.app U x) := by
  have := congr(($(he)).app U x)
  simpa [Scheme.Modules.Hom.comp_app] using this

def mapChart (a : AdaptedChart S r s) : AdaptedChart S' r s where
  U := a.U
  e i := e₁.hom.app a.U (a.e i)
  t i := e₂.hom.app a.U (a.t i)
  he := a.he.map_iso e₁.hom
  ht := by
    have := a.ht.map_iso e₃.hom
    convert this using 2 with i
    exact app_g e₂ e₃ hg _ _

include he in

theorem mapChart_frame (a : AdaptedChart S r s) (j : Fin r ⊕ Fin s) :
    (mapChart e₁ e₂ e₃ hg a).frame j = e₂.hom.app a.U (a.frame j) := by
  rcases j with j | j
  · exact app_f e₁ e₂ he _ _
  · rfl

theorem mapChart_quot (a : AdaptedChart S r s) :
    (mapChart e₁ e₂ e₃ hg a).quot = a.quot.map e₃ := by
  simp only [AdaptedChart.quot, Chart.map, mapChart, Chart.mk.injEq, true_and]
  exact heq_of_eq (funext fun i => app_g e₂ e₃ hg _ _)

end GlobalTheory.IsoSeq

namespace GlobalTheory.IsoSeq

open GlobalTheory.VBExt (AdaptedChart)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
  {S S' : ShortComplex X.Modules} {r s : ℕ}
  {e₁ : S.X₁ ≅ S'.X₁} {e₂ : S.X₂ ≅ S'.X₂} {e₃ : S.X₃ ≅ S'.X₃}
  (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) (hg : S.g ≫ e₃.hom = e₂.hom ≫ S'.g)
  {h : VMetric p S.X₂ (r + s)} {h' : VMetric p S'.X₂ (r + s)}

include he in

theorem gram_mapChart (hI : h.IsIsometry h' e₂) (σ : k →+* ℂ) (a : AdaptedChart S r s)
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ a.U) :
    (h'.met σ).gram (mapChart e₁ e₂ e₃ hg a).frame y = (h.met σ).gram a.frame y := by
  ext i j
  simp only [Met.gram, Matrix.of_apply, mapChart_frame e₁ e₂ e₃ he hg]
  exact hI σ a.U _ _ y hy

include he hg in

theorem quot_isIsometry (hS : S.ShortExact) (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r)
    (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (hI : h.IsIsometry h' e₂) :
    (h.quot hS h₁ h₃).IsIsometry (h'.quot hS' h₁' h₃') e₃ := by
  rw [VMetric.isIsometry_iff]
  refine VMetric.ext (funext fun σ => Met.ext_of_exists fun y => ?_)
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  refine ⟨(mapChart e₁ e₂ e₃ hg a).quot, ha, ?_⟩
  change ((h'.met σ).quot hS' h₁' h₃').G _ y = (((h.met σ).quot hS h₁ h₃).map e₃).G _ y
  rw [Met.quot_G _ hS' h₁' h₃' (mapChart e₁ e₂ e₃ hg a) ha, mapChart_quot e₁ e₂ e₃ hg,
    Met.map_G _ _ _ ha, Met.quot_G _ hS h₁ h₃ a ha, gram_mapChart he hg hI σ a ha]

include he hg in

theorem bcMeas_eq (hS : S.ShortExact) (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r)
    (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (H : h.IsCInf) (H' : h'.IsCInf)
    (hI : h.IsIsometry h' e₂) (σ : k →+* ℂ) :
    (h.met σ).bcMeas hS h₁ h₃ = (h'.met σ).bcMeas hS' h₁' h₃' := by
  refine part_congr fun c y hy => ?_
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  refine (Met.bcDens_eq_of_gram hS hS' h₁ h₃ h₁' h₃' (H σ) (H' σ) a (mapChart e₁ e₂ e₃ hg a) c c hy hy
    ha ha rfl ?_).symm
  filter_upwards [(ChartGlue.isOpen_over c.e (isOpen_ptsIn a.U)).mem_nhds
    (ChartGlue.mem_over c.e hy ha)] with v hv
  exact gram_mapChart he hg hI σ a hv.2

end GlobalTheory.IsoSeq

namespace GlobalTheory

theorem isometric_detQuot_and_bcInt_eq_of_iso : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (S S' : ShortComplex X.Modules) (r s : ℕ) (h : VMetric p S.X₂ (r + s)) (h' : VMetric p S'.X₂ (r + s)) (H : h.IsCInf) (H' : h'.IsCInf) (hS : S.ShortExact) (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂), e₁.hom ≫ S'.f = S.f ≫ e₂.hom → h.IsIsometry h' e₂ → (VMetric.det (H.quot hS h₁ h₃)).Isometric (VMetric.det (H'.quot hS' h₁' h₃')) ∧ h.bcInt hS h₁ h₃ = h'.bcInt hS' h₁' h₃' := by
  intro k _ X p S S' r s h h' H H' hS hS' h₁ h₃ h₁' h₃' e₁ e₂ he hI
  have hg := IsoSeq.g_isoThird hS hS' e₁ e₂ he
  refine ⟨GlobalTheory.CurveDens.det_isometric_of_isIsometry k X p _ _ s _ _ (H.quot hS h₁ h₃) (H'.quot hS' h₁' h₃')
    (IsoSeq.isoThird hS hS' e₁ e₂ he) (IsoSeq.quot_isIsometry he hg hS hS' h₁ h₃ h₁' h₃' hI), ?_⟩
  exact finsum_congr fun σ => by
    rw [IsoSeq.bcMeas_eq he hg hS hS' h₁ h₃ h₁' h₃' H H' hI σ]

end GlobalTheory
