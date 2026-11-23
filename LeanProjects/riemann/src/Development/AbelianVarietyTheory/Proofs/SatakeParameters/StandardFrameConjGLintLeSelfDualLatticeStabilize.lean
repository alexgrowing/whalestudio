import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.SplitFrameLattice

set_option maxHeartbeats 1000000 in

theorem glint_mul_frame_basis : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V V.rank) (sp : SplitPlace D.host.E)
    (β β' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    β * β' = 1 → β' * β = 1 →
    (∀ κ, Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ κ) =
      β * ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm) * β') →
    (∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank ↔ Ps.ψ κ ∈ Formalism.L2.Theta.KsphC V ∅) →
    ∀ (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) →
    (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) →
    (∀ x ∈ Formalism.L2.Theta.intAE D,
      sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) →
    sp.proj (GlobalTheory.NJoin.tensCast hF ε) = 1 →
    (∀ z, Formalism.IndefR.Mult.IntVec z → (fun a => ε * B.mulVec z a) ∈ Formalism.L2.NTheta.LamHat V) →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, Formalism.IndefR.Mult.IntVec z ∧ (fun a => ε * y a) = fun a => ε * B.mulVec z a) →
    ∀ g ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v),
    ∀ z : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
      (∀ i, z i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) →
      ∃ z' : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
        (∀ i, z' i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) ∧
        (g : Matrix (Fin V.rank) (Fin V.rank) _).mulVec
            ((β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z) =
          (β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z' := by
  intro D hF V Ps sp β β' hββ' hβ'β hfr hK ε sec B hsec hsecI hint hε b1 b2 g hg z hz
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+*
      sp.v.adicCompletion (maximalRealSubfield D.host.E) :=
    sp.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom
  have hfun : (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) = ⇑φ := rfl
  have hφε : φ ε = 1 := hε
  rw [hfun]
  obtain ⟨emb, htriv, hloc⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E V.rank sp
  have hκ : emb g ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank :=
    GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp (emb g) (htriv g) (by rw [hloc]; exact hg)
  have hKs := (hK (emb g)).1 hκ
  have hz0 : Formalism.IndefR.Mult.IntVec (sec ∘ z) := fun i => hsecI _ (hz i)
  have hy := b1 _ hz0
  have hy' := (hKs.2.1 _).1 hy
  obtain ⟨z'', hz'', e⟩ := b2 _ hy'
  refine ⟨φ ∘ z'', fun i => hint _ (hz'' i), ?_⟩
  have mv : ∀ (M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) x,
      φ ∘ (M.mulVec x) = (M.map φ).mulVec (φ ∘ x) := fun M x => funext fun i => RingHom.map_mulVec φ M x i
  have hε' : ∀ w : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      φ ∘ (fun a => ε * w a) = φ ∘ w := fun w => funext fun a => by
    simp only [Function.comp_apply, map_mul, hφε, one_mul]
  have hg' : (((emb g).1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map
      (GlobalTheory.NJoin.tensCast hF).symm).map φ = (g : Matrix (Fin V.rank) (Fin V.rank) _) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    show sp.proj (GlobalTheory.NJoin.tensCast hF ((GlobalTheory.NJoin.tensCast hF).symm _)) = _
    rw [RingEquiv.apply_symm_apply]
    conv_rhs => rw [← hloc g]
    rfl
  have hM : (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ (emb g))).map φ =
      β.map φ * (g : Matrix (Fin V.rank) (Fin V.rank) _) * β'.map φ := by
    rw [hfr (emb g), Matrix.map_mul, Matrix.map_mul, hg']
  have hzφ : φ ∘ (sec ∘ z) = z := funext fun i => hsec _
  have hβ : β'.map φ * β.map φ = 1 := by
    rw [← Matrix.map_mul, hβ'β, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have E := congrArg (fun w => φ ∘ w) e
  rw [hε', hε', mv, mv, hε', mv, hzφ, hM] at E
  have E2 := congrArg (fun w => (β'.map φ).mulVec w) E
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hβ, Matrix.one_mul] at E2
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
  exact E2

end GlobalTheory.SplitFrameLattice
