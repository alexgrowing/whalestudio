import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdapt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.MemK2HpIffBeta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxAsm

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

def DClause (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
    (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (Idx D.R.rS D.R.k) (FpX X p)) : Prop :=
  ∀ (ψ : KvA X p.1 →* GL (Idx D.R.rS D.R.k) (Op X p)),
    (∀ x : KvA X p.1, ((MassDataIdxRed.glRed (algebraMap (Op X p) (FpX X p)) (ψ x) : GL (Idx D.R.rS D.R.k) (FpX X p)) :
        Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) =
      ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) *
        (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))) →
    ∀ (π : Op X p →+* ZMod (gOf p)), RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)} →
    ∀ (x : KvH X u p.1) (B : GL (Fin D.R.k) (Op X p)), ψ (inclH X u p x) = hEmbGL D.R.rS D.R.k B →
      (x ∈ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1) ↔
        MassDataIdxRed.glRed π B ∈ Formalism.DoubleCosetMeasures.upUniG (ZMod (gOf p)) D.R.k)

def DClauseAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p), IsSplitEquiv X p θ →
    ∀ (Q : GL (Idx D.R.rS D.R.k) (FpX X p)) (l : Idx D.R.rS D.R.k → FpX X p), (∀ s, ¬ IsW s → l s ≠ 0) →
      (∀ s, ¬ IsW s → ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm) =
          (Pi.single s (1 : FpX X p) : Idx D.R.rS D.R.k → FpX X p)) →
      (∀ s, ¬ IsW s → (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ
        ((Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ
          (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm)) =
        l s • (Pi.single (dlH s) (1 : FpX X p) : Idx D.R.rS D.R.k → FpX X p)) →
      LatBasis X p θ (reindex₂ X p Q) → WClause X hb u p θ Q → DClause X hb u p θ Q

theorem hModelU_of (hD : DClauseAll) (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word)
    (hT : X.MeasTie hb) (hL : X.LevelSubgroupNormalized) (p : TypX X) (hA : HAdaptQ X hb u p) : HModelU X hb u p := by
  obtain ⟨θ, hθ, Q, l, hl, hy1, hy2, hLB, hW⟩ := hA
  obtain ⟨ψ, hψ, hker, hform⟩ := latCoreX_holds X p θ hθ Q hLB (KvA X p.1) rfl
  obtain ⟨π, hπ, hπk⟩ := MassDataIdxSteps.stResZ_holds X p
  refine ⟨ψ, 1, π, 1, hψ, hker, fun x => ?_, hπ, hπk, fun x B hB => ?_⟩
  · rw [inv_one, one_mul, mul_one]
    exact hH_of_form X u p θ hθ Q l hl hy1 hy2 ψ hform x
  · rw [inv_one, one_mul, mul_one] at hB
    rw [inv_one, one_mul, mul_one]
    exact hD X hb hK u hT hL p θ hθ Q l hl hy1 hy2 hLB hW ψ hform π hπk x B hB

def HAdaptAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X, HAdaptQ X hb u p

theorem hModelAll_of (hA : HAdaptAll) (hD : DClauseAll) : HModelAll :=
  fun X hb hK u hT hL p => hModelU_of hD X hb hK u hT hL p (hA X hb hK u hT hL p)

end PIW.MassDataColumns
