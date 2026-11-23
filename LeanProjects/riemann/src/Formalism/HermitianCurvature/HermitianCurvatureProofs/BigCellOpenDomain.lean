import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordKeyIdentity

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellOpenDomain

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem qdom_open (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (QDom k r z z') := by
  have h1 : IsOpen {q : (Fin r → ℂ) × ℂ | ∀ a, q.1 a ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun a =>
      isOpen_ne_fun ((continuous_apply a).comp continuous_fst) continuous_const
  have h2 : IsOpen {q : (Fin r → ℂ) × ℂ | Tz k r z * Tz k r z' < Complex.normSq q.2} :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd)
  exact h1.inter h2

theorem c_apply (n : ℕ) (a : Fin r) (s : Set ((Fin r → ℂ) × ℂ)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => q.1 a) s :=
  ((contDiff_apply ℝ ℂ a).comp contDiff_fst).contDiffOn

theorem c_inv (z z' : Fin (2 * r + k + 1) → ℂ) (n : ℕ) (a : Fin r) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => (star (q.1 a))⁻¹) (QDom k r z z') := by
  have h0 : ContDiff ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => q.1 a) :=
    (contDiff_apply ℝ ℂ a).comp contDiff_fst
  have hc : ContDiff ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => star (q.1 a)) :=
    Complex.conjCLE.contDiff.comp h0
  exact hc.contDiffOn.inv (fun q hq => star_ne_zero.2 ((show (∀ a, q.1 a ≠ 0) ∧ _ from hq).1 a))

theorem mu_entry (D : RealPlaceData k r Wp Wq) (n : ℕ) (a b : Fin (k + 1)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => D.μsec q.2 a b) (QDom k r D.z D.z') := by
  have hle : (n : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  exact ((D.sec.1 a b).of_le hle).comp (s := QDom k r D.z D.z') contDiff_snd.contDiffOn fun q hq => hq.2

theorem gq_contDiffOn (D : RealPlaceData k r Wp Wq) (n : ℕ) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q => gq D q) (QDom k r D.z D.z') := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  show ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => bigCell k r q.1 (D.μsec q.2) i j) _
  unfold bigCell
  split_ifs <;> first
    | exact contDiffOn_const
    | exact c_apply n _ _
    | exact c_inv D.z D.z' n _
    | exact mu_entry D n _ _

end Formalism.FourierDecayAlt.P.BigCellOpenDomain

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bessel_smooth_of_parts : Formalism.FourierDecayAlt.JF.JqSmoothOfParts := by
  intro hW hGD k r Wp Wq _ _ _ _ _ _ D A m F hT hF
  have hg := BigCellOpenDomain.gq_contDiffOn D m
  refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
  have hG := hGD k r Wp Wq D q hq
  obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hT hF).1 (gq D q) ⟨WordKeyIdentity.glev0 hG.1, hG.2⟩
  refine ⟨QDom k r D.z D.z' ∩ (fun q => gq D q) ⁻¹' U,
    hg.continuousOn.isOpen_inter_preimage (BigCellOpenDomain.qdom_open D.z D.z') hU, ⟨hq, hgU⟩, ?_⟩
  have hcomp : ContDiffOn ℝ (m : WithTop ℕ∞) (F' ∘ fun q => gq D q)
      (QDom k r D.z D.z' ∩ (QDom k r D.z D.z' ∩ (fun q => gq D q) ⁻¹' U)) :=
    hc.comp (hg.mono Set.inter_subset_left) fun x hx => hx.2.2
  refine hcomp.congr fun x hx => ?_
  exact he _ hx.2.2 (WordKeyIdentity.glev0 (hGD k r Wp Wq D x hx.1).1)

end Formalism.FourierDecayAlt.P
