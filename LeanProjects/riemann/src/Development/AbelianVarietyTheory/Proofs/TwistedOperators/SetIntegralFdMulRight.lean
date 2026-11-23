import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToPairMul
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

theorem setIntegral_fd_mul_right : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {X : Node} (M : Vol G)
    {K : Subgroup (GL (Fin (G.V X).rank) (Formalism.IndefR.Lev.EAf D))}, M.IsAt X K → ∀ (k : GA D (G.V X)),
    MeasurePreserving (fun g : GA D (G.V X) => g * k) (M.ν X) (M.ν X) → Measurable (fun g : GA D (G.V X) => g * k⁻¹) →
    ∀ φ : GA D (G.V X) → ℂ, (∀ γ ∈ GQ (G.V X), ∀ g, φ (γ * g) = φ g) →
    ∫ g in M.fd X, φ (g * k) ∂M.ν X = ∫ g in M.fd X, φ g ∂M.ν X := by
  intro D T L sc G X M K hM k hk hk' φ hφ
  obtain ⟨hH, hF⟩ := hM.haar_fund
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (G.V X).gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig (G.V X).gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig (G.V X).gram
  haveI : Countable (GQ (G.V X)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (G.V X).gram
  haveI := hH
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ (G.V X))
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ (G.V X)) (M.ν X)

  let e : GA D (G.V X) ≃ᵐ GA D (G.V X) :=
    { toFun := fun g => g * k, invFun := fun g => g * k⁻¹,
      left_inv := fun g => by simp, right_inv := fun g => by simp,
      measurable_toFun := hk.measurable, measurable_invFun := hk' }

  have hF' : IsFundamentalDomain (GQ (G.V X)) ((fun g : GA D (G.V X) => g * k) ⁻¹' M.fd X) (M.ν X) :=
    hF.preimage_of_equiv hk.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
  rw [hF.setIntegral_eq hF' (f := fun g => φ (g * k)) (fun γ x => by
      simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hφ γ γ.2 _)]
  exact hk.setIntegral_preimage_emb e.measurableEmbedding φ (M.fd X)

end GlobalTheory.RowReal
