import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.HermitianForms.TiedBrInj
import Formalism.LocalToGlobal.HermitianForms.Interlace
import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts NumberField

variable {D : D7}

def BeOnFam {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  Formalism.MainNotions.FamU Fm fun D u => Formalism.L2.Ker.BeOnTie D u

private theorem interlace_lamTr_sgTr' {u : D.what₂.Word} (Tf : FormsTied D u) (τ : D.what₂.Tau) :
    Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) := by
  intro i
  obtain ⟨h1, h2⟩ := sg_interlace Tf.valP τ i
  exact ⟨by simpa [lamTr, sgTr, wSh] using h1, by simpa [lamTr, sgTr, wSh] using h2⟩

def bZ (u : D.what₂.Word) (z0 : Fin (D.R.N D.R.m) → D.host.E) :
    Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E :=
  fun a b => if hb : (b : ℕ) < D.R.N D.R.m - 1 then iXm D a ⟨b, hb⟩ else z0 a / ((D.mem u).A.T : D.host.E)

def mZ (u : D.what₂.Word) (z0 : Fin (D.R.N D.R.m) → D.host.E) :
    D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ :=
  atInf (embT D) (bZ u z0)⁻¹

def LowerMapTie {u : D.what₂.Word} (Tf : FormsTied D u) : Prop :=
  IsUnit (bZ u Tf.til.z0).det → ∀ (ψ : (D.mem u).P.Wz) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ CSpan ((D.fm u).lam D.R.m) →
    (∀ s, Tf.eWz ψ c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl).eY s)) →
    Tf.valP.eW ((D.mem u).P.lowerMap ψ) c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P)

structure LowerLevelCompatible {u : D.what₂.Word} (Tf : FormsTied D u) : Prop where
  beOn : Formalism.L2.Ker.BeOnTie D u
  map : LowerMapTie Tf

theorem LowerMapTie.pt_eq {u : D.what₂.Word} {Tf : FormsTied D u} (h : LowerMapTie Tf) (hB : IsUnit (bZ u Tf.til.z0).det) (φ : Fn D u D.R.m) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hP : P ∈ CSpan ((D.fm u).lam D.R.m))
    (hv : ∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl).eY s)) :
    Tf.valP.eW (Pt D u φ) c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) :=
  h hB ((D.mem u).P.evz φ) c P hP hv

theorem archimedeanSignatureMatching_of_trivial_branching {u : D.what₂.Word} (Tf : FormsTied D u) (P : Pend D u)
    (hP : ∀ τ, P.br τ = Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) : ArchimedeanSignatureMatching P := by
  intro τ
  rw [hP τ]
  exact Formalism.L2.Ker.brOneIsBr D u τ (interlace_lamTr_sgTr' Tf τ)

theorem mZ_isUnit {u : D.what₂.Word} {z0 : Fin (D.R.N D.R.m) → D.host.E} (hB : IsUnit (bZ u z0).det) (τ : D.what₂.Tau) :
    IsUnit (mZ u z0 τ).det := by
  have h1 : IsUnit ((bZ u z0)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ hB
  have h2 : IsUnit ((embT D τ).mapMatrix (bZ u z0)⁻¹).det := by
    rw [← RingHom.map_det]
    exact h1.map _
  exact h2

end Formalism.L2.Forms
