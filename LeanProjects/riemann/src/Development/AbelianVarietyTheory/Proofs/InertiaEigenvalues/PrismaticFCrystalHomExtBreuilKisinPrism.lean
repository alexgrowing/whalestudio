import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemiBCInjectiveOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescentStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} {R : Type} [CommRing R]

theorem FHom.ext_u {M M' : FCrys l R} {u u' : FHom M M'} (h : ∀ P, u.u P = u'.u P) : u = u' := by
  cases u; cases u'
  congr
  funext P
  exact h P

theorem FHom.eq_of_tr {M M' : FCrys l R} (u u' : FHom M M') {P Q : Obj l R} (g : Hom P Q)
    (hP : u.u P = u'.u P) : u.u Q = u'.u Q := by
  let v : M.M P →ₛₗ[g.f] M'.M Q := (M'.tr g).comp (u.u P)
  obtain ⟨w, -, hw⟩ := M.tr_bc g (M'.M Q) v
  have h1 := hw (u.u Q) fun x => by simp [v, u.u_tr]
  have h2 := hw (u'.u Q) fun x => by simp [v, u'.u_tr, hP]
  rw [h1, h2]

theorem FHom.eq_of_inj {M M' : FCrys l R} (u u' : FHom M M') {B C : Obj l R} (h : Hom B C)
    (hinj : Function.Injective h.f) (hC : u.u C = u'.u C) : u.u B = u'.u B := by
  haveI := M'.fin B
  haveI := M'.proj B
  have hi : Function.Injective (M'.tr h) :=
    semiBC_injective_of_injective _ _ h.f hinj _ _ (M'.tr h) (M'.tr_bc h)
  ext x
  apply hi
  rw [← u.u_tr, ← u'.u_tr, hC]

theorem fhom_ext_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M M' : FCrys l ↥(OL K))
    (u u' : FHom M M'), u.u bk.prism = u'.u bk.prism → u = u' := by
  intro l _ K bk M M' u u' hbk
  apply FHom.ext_u
  intro B
  obtain ⟨C, h, ⟨g⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  have hC := FHom.eq_of_tr u u' g hbk
  exact FHom.eq_of_inj u u' h (GlobalTheory.T.prism_cover_injective_and_descent l _ B C h hc).1 hC

end GlobalTheory.BSP
