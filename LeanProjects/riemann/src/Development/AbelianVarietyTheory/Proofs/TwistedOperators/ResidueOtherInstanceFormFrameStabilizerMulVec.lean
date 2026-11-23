import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem cast_hA_add {I J : Formalism.MainNotions.S.AutInst} (e : I = J) (y z z' : Formalism.L2.SG.HidaSetting.VA J) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) (z + z'))) =
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) z)) +
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) z')) := by
  subst e
  simp only [cast_eq]
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem cast_hA_smul {I J : Formalism.MainNotions.S.AutInst} (e : I = J) (c : TensorProduct J.F J.E (Formalism.MainNotions.S.Af J.F))
    (y z : Formalism.L2.SG.HidaSetting.VA J) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) (c • z))) =
    c * cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) z)) := by
  subst e
  simp only [cast_eq]
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hT_add' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (y z z' : Fin (Yc D 0).rank → EAf D) : hT X h y (z + z') = hT X h y z + hT X h y z' :=
  cast_hA_add h y z z'

theorem hT_smul' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (c : EAf D) (y z : Fin (Yc D 0).rank → EAf D) : hT X h y (c • z) = c * hT X h y z :=
  cast_hA_smul h c y z

end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar
open Classical
theorem resT_of_mem' {D : D7} (PP : Pl D.host.E) (x : EAf D) (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resT PP x = Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ := dif_pos hx
end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar.ResStab

open Classical Matrix

theorem mem_res_eq {R k : Type} [CommRing R] [CommRing k] {S : Subring R} (ρ : S →+* k) {x : R} (s : S)
    (hx : x = s) : ∃ hm : x ∈ S, ρ ⟨x, hm⟩ = ρ s := by
  subst hx
  exact ⟨s.2, rfl⟩

theorem res_conj_mulVec {R k : Type} [CommRing R] [CommRing k] (S : Subring R) (ρ : S →+* k) (r : R → k) (hr : ∀ x (hx : x ∈ S), r x = ρ ⟨x, hx⟩) {n : ℕ}
    (f : (Fin n → R) → R) (hadd : ∀ z z', f (z + z') = f z + f z') (hsmul : ∀ (c : R) z, f (c • z) = c * f z) (β : GL (Fin n) R) (Y : Matrix (Fin n) (Fin n) S) (w : Fin n → Fin n → R)
    (N : Matrix (Fin n) (Fin n) R)
    (hNY : N = (β : Matrix (Fin n) (Fin n) R) * Y.map S.subtype * ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R))
    (hw : ∀ i j, ∃ hm : (((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ w j) i ∈ S,
      ρ ⟨_, hm⟩ = if i = j then 1 else 0)
    (hf : ∀ z, (∀ i, (((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ z) i ∈ S) → f z ∈ S) (j : Fin n) :
    ∃ hx : f (N *ᵥ w j) ∈ S,
      ρ ⟨_, hx⟩ = ∑ l, r (f (w l)) * ρ (Y l j) := by
  subst hNY
  set B : Matrix (Fin n) (Fin n) R := (β : Matrix (Fin n) (Fin n) R) with hB
  set Bi : Matrix (Fin n) (Fin n) R := ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hBi
  have hBiB : Bi * B = 1 := by rw [hBi, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBBi : B * Bi = 1 := by rw [hBi, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one]

  let b : Fin n → Fin n → R := fun m i => B i m
  have hb : ∀ m, Bi *ᵥ b m = Pi.single m 1 := by
    intro m
    have : b m = B *ᵥ Pi.single m 1 := by
      funext i
      simp [b, Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, hBiB, Matrix.one_mulVec]
  have ht : ∀ m, f (b m) ∈ S := by
    intro m
    refine hf _ fun i => ?_
    rw [hb m]
    by_cases hi : i = m
    · subst hi; simp only [Pi.single_eq_same]; exact S.one_mem
    · rw [Pi.single_eq_of_ne hi]; exact S.zero_mem
  let t : Fin n → S := fun m => ⟨f (b m), ht m⟩

  have hdec : ∀ z, f z = ∑ m, (Bi *ᵥ z) m * f (b m) := by
    intro z
    have hz : z = ∑ m, (Bi *ᵥ z) m • b m := by
      funext i
      have := congrFun (show B *ᵥ (Bi *ᵥ z) = z by rw [Matrix.mulVec_mulVec, hBBi, Matrix.one_mulVec]) i
      rw [← this, Finset.sum_apply]
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, b]
      exact Finset.sum_congr rfl fun m _ => mul_comm _ _
    let fl : (Fin n → R) →ₗ[R] R := ⟨⟨f, hadd⟩, hsmul⟩
    show fl z = _
    conv_lhs => rw [hz]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rfl
  have hval : ∀ z (v : Fin n → S), (∀ m, (Bi *ᵥ z) m = v m) → f z = ((∑ m, v m * t m : S) : R) := by
    intro z v hv
    rw [hdec z]
    push_cast
    exact Finset.sum_congr rfl fun m _ => by rw [hv m]

  let c : Fin n → Fin n → S := fun l i => ⟨(Bi *ᵥ w l) i, (hw i l).1⟩
  have hc : ∀ l i, ρ (c l i) = if i = l then 1 else 0 := fun l i => (hw i l).2

  have hwl : ∀ l, r (f (w l)) = ρ (t l) := by
    intro l
    obtain ⟨hm, e⟩ := mem_res_eq ρ _ (hval (w l) (c l) fun m => rfl)
    rw [hr _ hm, e, map_sum]
    simp only [map_mul, hc]
    simp

  have hN : ∀ m, (Bi *ᵥ ((B * Y.map S.subtype * Bi) *ᵥ w j)) m = ((∑ i, Y m i * c j i : S) : R) := by
    intro m
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBiB, Matrix.one_mul, ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Subring.coe_subtype, c]
    push_cast
    rfl
  obtain ⟨hm, e⟩ := mem_res_eq ρ _ (hval _ (fun m => ∑ i, Y m i * c j i) hN)
  refine ⟨hm, ?_⟩
  rw [e]
  simp only [hwl, map_sum, map_mul, hc]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end GlobalTheory.SeeConjChar.ResStab

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem resT_hT_mulVec_stab : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D), RedIs β PP w → ∀ N ∈ St β, ∀ y : Fin (Yc D 0).rank → EAf D, (∀ z : Fin (Yc D 0).rank → EAf D, (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h y z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ j, GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec N.val (w j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec N.val (w j))) = ∑ l, GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (w l)) * (redFn β PP N).val l j := by
  intro D X h β PP w hw N hN y hy j
  obtain ⟨Y, rfl⟩ := hN
  have hval : (Formalism.L2.DIV.frGL β Y).val =
      β.val * Y.val.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (β⁻¹).val := by
    simp only [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul]
    rfl
  have hred : ∀ l, ((Formalism.L2.DIV.redFn β PP (Formalism.L2.DIV.frGL β Y)).val l j) =
      Formalism.L2.DIV.resS D.host.F PP (Y.val l j) := by
    intro l
    rw [Formalism.L2.DIV.redFn_frGL]
    rfl
  obtain ⟨hm, e⟩ := ResStab.res_conj_mulVec (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.DIV.resS D.host.F PP) (resT PP) (resT_of_mem' PP)
    (hT X h y) (hT_add' X h y) (fun c z => hT_smul' X h c y z) β Y.val w _ hval hw hy j
  refine ⟨hm, ?_⟩
  exact (resT_of_mem' PP _ hm).trans (e.trans (Finset.sum_congr rfl fun l _ =>
    congrArg (fun t => resT PP (hT X h y (w l)) * t) (hred l).symm))

end GlobalTheory.SeeConjChar
