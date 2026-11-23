import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MeasCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RescaleCore
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Matrix

namespace Formalism.L2.SG.Pf.Rescale

section Gram

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hE_swap (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by
  simp only [hE, Formalism.UG.hform, AlgHom.coe_toRingHom, map_sum, map_mul, hσ]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [hJ.1]
  ring

theorem standard_gram_nondegenerate : Formalism.L2.SG.Pf.RescaleCore.GramStdND := by
  intro F E _ _ _ σ n J r P T hσ hJ hS
  obtain ⟨hee, hff, hef, hez, hfz, hzz, hT⟩ := hS
  intro hdet
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet

  have tE : ∀ a : Fin r, tupH P (Fin.castAdd r (Fin.castSucc a)) = P.e a := by
    intro a; simp [tupH, F0, Fin.append_left, Fin.snoc_castSucc]
  have tZ : tupH P (Fin.castAdd r (Fin.last r)) = P.z := by
    simp [tupH, F0, Fin.append_left, Fin.snoc_last]
  have tF : ∀ a : Fin r, tupH P (Fin.natAdd (r + 1) a) = P.f a := by
    intro a; simp [tupH, Fin.append_right]
  have hsum : ∀ i, (gramE σ J (tupH P) *ᵥ v) i =
      (∑ b : Fin r, hE σ J (tupH P i) (P.e b) * v (Fin.castAdd r (Fin.castSucc b))) +
        hE σ J (tupH P i) P.z * v (Fin.castAdd r (Fin.last r)) +
        ∑ b : Fin r, hE σ J (tupH P i) (P.f b) * v (Fin.natAdd (r + 1) b) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, gramE]
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
    simp only [tE, tZ, tF]
  have hrow : ∀ i, (gramE σ J (tupH P) *ᵥ v) i = 0 := fun i => congrFun hv i
  have vF : ∀ a : Fin r, v (Fin.natAdd (r + 1) a) = 0 := by
    intro a
    have h := hrow (Fin.castAdd r (Fin.castSucc a))
    rw [hsum, tE] at h
    simp only [hee, zero_mul, Finset.sum_const_zero, zero_add, hez, hef, ite_mul, one_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact h
  have hze : ∀ b, hE σ J P.z (P.e b) = 0 := fun b => by rw [hE_swap σ J hσ hJ, hez, map_zero]
  have hzf : ∀ b, hE σ J P.z (P.f b) = 0 := fun b => by rw [hE_swap σ J hσ hJ, hfz, map_zero]
  have hfe : ∀ a b, hE σ J (P.f a) (P.e b) = if b = a then 1 else 0 := fun a b => by
    rw [hE_swap σ J hσ hJ, hef]; split_ifs <;> simp
  have hfz' : ∀ a, hE σ J (P.f a) P.z = 0 := hfz
  have vZ : v (Fin.castAdd r (Fin.last r)) = 0 := by
    have h := hrow (Fin.castAdd r (Fin.last r))
    rw [hsum, tZ] at h
    simp only [hze, hzf, zero_mul, Finset.sum_const_zero, zero_add, add_zero] at h
    have hne : hE σ J P.z P.z ≠ 0 := by
      rw [hzz]
      intro h0
      exact hT (neg_eq_zero.1 ((algebraMap F E).injective (by rw [h0, map_zero])))
    exact (mul_eq_zero.1 h).resolve_left hne
  have vE : ∀ a : Fin r, v (Fin.castAdd r (Fin.castSucc a)) = 0 := by
    intro a
    have h := hrow (Fin.natAdd (r + 1) a)
    rw [hsum, tF] at h
    simp only [hfe, hfz', hff, zero_mul, Finset.sum_const_zero, add_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  apply hv0
  funext i
  refine Fin.addCases (fun j => ?_) (fun a => ?_) i
  · refine Fin.lastCases ?_ (fun a => ?_) j
    · exact vZ
    · exact vE a
  · exact vF a

end Gram

end Formalism.L2.SG.Pf.Rescale

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

namespace Formalism.L2.SG.Pf.Rescale

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hform_crdX (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply,
    X.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem hE_crdX (X : HidaSetting D) (v w : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w) = X.ιE.symm ((VS D).hT v w) := by
  show Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J _ _ = _
  rw [← hform_crdX X v w, RingEquiv.symm_apply_apply]

theorem frame_stdX (X : HidaSetting D) (u : D.what₂.Word) :
    (Formalism.L2.SG.TypedSets.frameOf X u).IsStd X.B.I.cm.sig X.B.I.J (((D.mem u).A.T : ℕ) : X.B.I.F) := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun a => ?_, ?_, ?_⟩
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.eX b)) = 0
    rw [hE_crdX, X.ee, map_zero]
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.fY a)) (crdOf X.B.I X.ιE X.bas (X.fY b)) = 0
    rw [hE_crdX, X.ff, map_zero]
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.fY b)) = _
    rw [hE_crdX, X.ef]
    split_ifs <;> simp
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) = 0
    rw [hE_crdX, (X.zu_orth u a).1, map_zero]
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.fY a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) = 0
    rw [hE_crdX, (X.zu_orth u a).2, map_zero]
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.zu u)) (crdOf X.B.I X.ιE X.bas (X.zu u)) = _
    rw [hE_crdX, X.zu_norm]
    simp
  · exact Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

def withMeasL (X : HidaSetting D) (mg : Formalism.L2.SG.Measures.MeasG X.B.I.cm.sig X.B.I.J D.R.rS)
    (hg : mg.IsTextNorm)
    (mw : ∀ u, Formalism.L2.SG.Measures.MeasW X.B.I.cm.sig X.B.I.J
      (⟨fun a => crdOf X.B.I X.ιE X.bas (X.eX a), fun a => crdOf X.B.I X.ιE X.bas (X.fY a),
        crdOf X.B.I X.ιE X.bas (X.zu u)⟩ : Formalism.L2.SG.Sub.Frame X.B.I.E X.B.I.n D.R.rS))
    (hw : ∀ u, (mw u).IsTextNorm) : HidaSetting D :=
  { X with measG := mg, measG_norm := hg, measW := mw, measW_norm := hw }

variable (D) in

def RescaleStep3L : Prop :=
  ∀ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I), X.MeasTie hb →
    ∃ (mg : Formalism.L2.SG.Measures.MeasG X.B.I.cm.sig X.B.I.J D.R.rS) (hg : mg.IsTextNorm)
      (mw : ∀ u, Formalism.L2.SG.Measures.MeasW X.B.I.cm.sig X.B.I.J
        (⟨fun a => crdOf X.B.I X.ιE X.bas (X.eX a), fun a => crdOf X.B.I X.ιE X.bas (X.fY a),
          crdOf X.B.I X.ιE X.bas (X.zu u)⟩ : Formalism.L2.SG.Sub.Frame X.B.I.E X.B.I.n D.R.rS))
      (hw : ∀ u, (mw u).IsTextNorm),
      (withMeasL X mg hg mw hw).MeasTie hb ∧
      ∃ ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧
        Formalism.L2.SG.LocVol.IsStdChar ψ ∧
        Formalism.L2.SG.MassDataConc.MeasCompatψ (withMeasL X mg hg mw hw) ψ ∧
        ∀ w, Formalism.L2.SG.LocVol.LocCompatX (withMeasL X mg hg mw hw) ψ w

end Formalism.L2.SG.Pf.Rescale
