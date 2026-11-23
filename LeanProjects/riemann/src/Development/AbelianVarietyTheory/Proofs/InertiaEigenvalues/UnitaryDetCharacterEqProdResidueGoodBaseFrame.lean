import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterProductFormula
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUnitIsDetRoot

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwistDetStabAll

open Classical GlobalTheory.TwistDetStab

variable {D : D7}

theorem exists_finUnit_isDetRoot {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {k : GA D V} (hk : k ∈ GfC V)
    (hst : Lev.finE V k ∈ St β) : ∃ x : (AE D)ˣ, Formalism.L2.Pj.FinUnit x ∧ IsDetRoot V k x := by
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  obtain ⟨a, ha, -⟩ := GlobalTheory.VecInv.exists_det_int hst
  have hd : finPart D (mt V k).det ∈ intAE D := GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (ha ▸ a.2)
  have hw : (finHom V k).1.det - 1 ∈ intAE D :=
    sub_mem (hdet ▸ hd) (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (_root_.mul_one _))
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, -⟩ := GlobalTheory.OddRoot.exists_root_odd D 1 odd_one _ _ hw (one_nsmul _).symm hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, ?_⟩
  have hk1 : infHom V k = 1 := hk
  rw [hk1, Units.val_one, Matrix.det_one] at hdet'
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  refine Prod.ext (((he _).1.trans ?_).trans (he _).1.symm) (((he _).2.trans ?_).trans (he _).2.symm)
  · change infPart D (Y : AE D) = infPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet', GlobalTheory.UnitDetRoot.infPart_sigR_one D _ hY1, hY1, _root_.mul_one]
  · change finPart D (Y : AE D) = finPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet, GlobalTheory.DetRootCong.finPart_sigR, hY2]
    exact hroot

theorem chi_detAt {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A) (ht : t.Good)
    {β : GL (Fin V.rank) (Lev.EAf D)} {κ : GA D V} (hst : Lev.finE V κ ∈ St β) (he : idem t.Q * idem t.Q = idem t.Q) :
    t.chi (GlobalTheory.VecInv.detAt (idem t.Q) he V κ) =
      ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  have hPi : ∀ P ∈ t.Q, idemAt P * idemAt P = idemAt P := fun P hP => (ht.split.isIdemAt hP).1.1
  have hsplit : GlobalTheory.VecInv.detAt (idem t.Q) he V κ =
      ∏ P ∈ t.Q.attach, GlobalTheory.VecInv.detAt (idemAt P.1) (hPi P.1 P.2) V κ := by
    ext
    rw [Units.coe_prod]
    show idem t.Q * (mt V κ).det + (1 - idem t.Q) = ∏ P ∈ t.Q.attach, (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1))
    rw [Finset.prod_attach t.Q (fun P => idemAt P * (mt V κ).det + (1 - idemAt P)),
      prod_val _ ht.split t.Q (Finset.Subset.refl _)]
  rw [hsplit, map_prod,
    ← Finset.prod_attach t.Q (fun PP => t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))))]
  refine Finset.prod_congr rfl fun P _ => ?_
  refine ht.res P.1 P.2 _ ?_ (GlobalTheory.StabDet.toEAf_detAt_mem hst _ (hPi P.1 P.2)) _
    (GlobalTheory.StabDet.res_detAt hst _ (hPi P.1 P.2) P.1 (ht.split.isIdemAt P.2)).symm
  show (1 - idemAt P.1) * (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1)) = 1 - idemAt P.1
  linear_combination (1 - (mt V κ).det) * hPi P.1 P.2

def offUnit {R : Type} [CommRing R] (f : R) (hf : f * f = f) (x : Rˣ) : Rˣ where
  val := f + (1 - f) * x.val
  inv := f + (1 - f) * (x⁻¹).val
  val_inv := by
    linear_combination (1 - f) ^ 2 * x.mul_inv + (2 - x.val - (x⁻¹).val) * hf
  inv_val := by
    linear_combination (1 - f) ^ 2 * x.mul_inv + (2 - x.val - (x⁻¹).val) * hf

theorem cmRing_idempotent_unitRatio_identity {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ z, c (c z) = z) (e d x : R) (h1 : e * e = e)
    (h2 : e * c e = 0) (hd : c d * d = 1) (hx : x = d * c x) :
    (e * d + (1 - e)) * ((e + c e) + (1 - (e + c e)) * x) =
      d * c ((e * d + (1 - e)) * ((e + c e) + (1 - (e + c e)) * x)) := by
  have h3 : c e * c e = c e := by rw [← map_mul, h1]
  have k : (e * d + (1 - e)) * ((e + c e) + (1 - (e + c e)) * x) = e * d + c e + (1 - (e + c e)) * x := by
    linear_combination (d - 1) * (1 - x) * (h1 + h2)
  rw [k]
  simp only [map_add, map_mul, map_sub, map_one, hc]
  linear_combination (1 - (e + c e)) * hx - c e * hd

theorem finPart_off_mem (f y : AE D) (hf : f * f = f) (hy : finPart D y ∈ intAE D) :
    finPart D (f + (1 - f) * y) ∈ intAE D := by
  have h1 : finPart D f ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hf])
  have h2 : finPart D (1 - f) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by
    rw [← RingHom.map_mul]; congr 1; linear_combination hf)
  rw [RingHom.map_add, RingHom.map_mul]
  exact add_mem h1 (GlobalTheory.HeckeConj.mul_mem_intAE D h2 hy)

theorem detChar_eq_prod_res_of_frame {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A) (ht : t.Good)
    (β : GL (Fin V.rank) (Lev.EAf D)) {κ : GA D V} (hκ : κ ∈ GfC V) (hst : Lev.finE V κ ∈ St β) :
    detChar V t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  obtain ⟨x, ⟨hx1, hx2, hx3⟩, hx⟩ := exists_finUnit_isDetRoot hκ hst
  have he : idem t.Q * idem t.Q = idem t.Q := idem_mul_self ht.split
  have hce : idem t.Q * cA D (idem t.Q) = 0 := ht.split.isIdemSum.2
  have hcc : cA D (idem t.Q) * cA D (idem t.Q) = cA D (idem t.Q) := by rw [← RingHom.map_mul, he]
  have hf : (idem t.Q + cA D (idem t.Q)) * (idem t.Q + cA D (idem t.Q)) = idem t.Q + cA D (idem t.Q) := by
    linear_combination he + hcc + 2 * hce
  have hroot : IsDetRoot V κ (GlobalTheory.VecInv.detAt (idem t.Q) he V κ * offUnit _ hf x) :=
    cmRing_idempotent_unitRatio_identity (cA D) GlobalTheory.DualPairCheck.cA_cA (idem t.Q) (mt V κ).det x he hce (det_conj_mul V κ) hx
  have hw : t.chi (offUnit _ hf x) = 1 := by
    refine ht.unram _ ?_ (finPart_off_mem _ _ hf hx2) (finPart_off_mem _ _ hf hx3) ?_
    · show infPart D (_ + (1 - _) * (x : AE D)) = 1
      rw [RingHom.map_add, RingHom.map_mul, hx1, RingHom.map_sub, RingHom.map_one]
      ring
    · show (idem t.Q + cA D (idem t.Q)) * ((idem t.Q + cA D (idem t.Q)) + (1 - (idem t.Q + cA D (idem t.Q))) * (x : AE D)) = _
      linear_combination (1 - (x : AE D)) * hf
  rw [detChar_eq ht.real hroot, map_mul, hw, _root_.mul_one, chi_detAt t ht hst he]

theorem detChar_eq_prod_res : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ {A : Type} [CommGroup A] (t : Twist D A),
    t.Good → ∀ {κ : GA D T}, κ ∈ GfC T → Lev.finE T κ ∈ St B.F.βT →
    detChar T t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ))) :=
  fun B _ _ _ t ht _ hκ hst => detChar_eq_prod_res_of_frame t ht B.F.βT hκ hst

end GlobalTheory.TwistDetStabAll

end
