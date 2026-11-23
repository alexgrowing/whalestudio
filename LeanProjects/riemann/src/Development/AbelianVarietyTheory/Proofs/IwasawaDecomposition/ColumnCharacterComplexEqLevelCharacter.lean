import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParLevOfQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section
namespace GlobalTheory.Mem.ChiType

theorem embLL_chiAt_eq_levChi : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (i : Fin X.toD7.R.m) (w : Pl X.toD7.host.E) (hw : w ∈ (X.B.primes px).vGs) (u : (kP w)ˣ),
      X.toD7.what₂.embLL ((Formalism.L2.Col.chiAt I.Ch ⟨w, hw⟩ (i : ℕ) u : X.B.fields.Kˣ) : X.B.fields.K) =
        ((L.chi ((i : ℕ) + 1) w u : ℂˣ) : ℂ) := by
  intro X px I U L hI hL i w hw u
  have hw' : w ∈ L.Pg := hL.Pg ▸ hw
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP w)
  have hu0 : (u : kP w) ≠ 0 := u.ne_zero
  have ha0 : ((a : 𝓞 X.toD7.host.E) : X.toD7.host.E) ≠ 0 := by
    intro h0
    apply hu0
    rw [← ha, (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 X.toD7.host.E) X.toD7.host.E).1 h0, map_zero]
  let k : X.toD7.host.Eˣ := Units.mk0 _ ha0
  have h1 := (hI.ch_tied.mu0 i).atg ⟨w, hw⟩ k a u rfl ha.symm
  have h2 := hL.is.chi i w hw' a k u rfl ha.symm
  rw [hL.C] at h2
  have h2' : (L.chi ((i : ℕ) + 1) w u : ℂˣ) = ((((Top.Fr.at X I.C).mu0 i).locK w k))⁻¹ := by
    rw [← h2, MonoidHom.inv_apply, inv_inv]
  have e : Formalism.L2.Col.chiAt I.Ch ⟨w, hw⟩ (i : ℕ) u = I.Ch.chi i ⟨w, hw⟩ u := by
    simp only [Formalism.L2.Col.chiAt, Formalism.L2.Col.extChi]
    rw [dif_pos (show (i : ℕ) < X.B.R.m from i.2)]
    rfl
  rw [e, h2', Units.val_inv_eq_inv_val]
  change _ = (((((I.C.mu0 i).locK (⟨w, hw⟩ : {w // w ∈ (X.B.primes px).vGs}).1) k : ℂˣ) : ℂ))⁻¹
  rw [h1, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
  rfl

end GlobalTheory.Mem.ChiType
