import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugation
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace GlobalTheory.CompanionTheory.HermSc

section Abstract

variable {M : Type} [AddCommGroup M] [TopologicalSpace M]

theorem sub_mem_ker (S : AddSubgroup M) (P : M →+ M) (hPm : ∀ x, P x ∈ S) (hPs : ∀ s ∈ S, P s = s) (x : M) :
    x - P x ∈ P.ker := by
  rw [AddMonoidHom.mem_ker, map_sub, hPs _ (hPm x), sub_self]

def imKer [IsTopologicalAddGroup M] (S : AddSubgroup M) (P : M →+ M) (hPc : Continuous P) (hPm : ∀ x, P x ∈ S)
    (hPs : ∀ s ∈ S, P s = s) : (S × P.ker) ≃ₜ+ M where
  toFun p := p.1.1 + p.2.1
  invFun x := (⟨P x, hPm x⟩, ⟨x - P x, sub_mem_ker S P hPm hPs x⟩)
  left_inv p := by
    have h2 : P p.2.1 = 0 := p.2.2
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change P (p.1.1 + p.2.1) = p.1.1
      rw [map_add, hPs _ p.1.2, h2, add_zero]
    · change (p.1.1 + p.2.1) - P (p.1.1 + p.2.1) = p.2.1
      rw [map_add, hPs _ p.1.2, h2, add_zero, add_sub_cancel_left]
  right_inv x := by
    change P x + (x - P x) = x
    abel
  map_add' p q := by
    change (p.1.1 + q.1.1) + (p.2.1 + q.2.1) = (p.1.1 + p.2.1) + (q.1.1 + q.2.1)
    abel
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (hPc.subtype_mk _).prodMk ((continuous_id.sub hPc).subtype_mk _)

theorem char_restr [IsTopologicalAddGroup M] [LocallyCompactSpace M] [SecondCountableTopology M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] (S : AddSubgroup M) [LocallyCompactSpace S] (P : M →+ M)
    (hPc : Continuous P) (hPm : ∀ x, P x ∈ S) (hPs : ∀ s ∈ S, P s = s)
    (U : M ≃ₜ+ M) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) (hfix : ∀ x, P x = 0 → U x = x) :
    addEquivAddHaarChar (GlobalTheory.CompanionTheory.CgMod.restr S U hU hU') = addEquivAddHaarChar U := by
  haveI : SecondCountableTopology S := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space S := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : SecondCountableTopology P.ker := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space P.ker := Topology.IsEmbedding.subtypeVal.t2Space
  have hcl : IsClosed (P.ker : Set M) := by
    have : (P.ker : Set M) = P ⁻¹' {0} := by
      ext x; simp [AddMonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hPc
  haveI : LocallyCompactSpace P.ker := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set Ψ := imKer S P hPc hPm hPs with hΨ
  set T := GlobalTheory.CompanionTheory.CgMod.restr S U hU hU' with hT
  have e : ((Ψ.symm.trans (GlobalTheory.ModuLR.prodCE T (ContinuousAddEquiv.refl P.ker))).trans Ψ) = U := by
    ext x
    obtain ⟨p, rfl⟩ := Ψ.surjective x
    change Ψ (GlobalTheory.ModuLR.prodCE T (ContinuousAddEquiv.refl P.ker) (Ψ.symm (Ψ p))) = U (Ψ p)
    have hl : Ψ.symm (Ψ p) = p := Ψ.left_inv p
    rw [hl]
    change U p.1.1 + p.2.1 = U (p.1.1 + p.2.1)
    rw [map_add, hfix _ p.2.2]
  rw [← e, GlobalTheory.ModuLR.addEquivAddHaarChar_transport Ψ, GlobalTheory.T.addEquivAddHaarChar_prodCongr, addEquivAddHaarChar_refl, mul_one]

end Abstract

section Main

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.HermVol GlobalTheory.CompanionTheory.CgMod PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem char_herm [BorelSpace (Mx D n n)] [LocallyCompactSpace (hermA D n)] (a : GL (Fin n) (AE D)) :
    addEquivAddHaarChar (restr (hermA D n) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) (lr_herm a) (lr_herm_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (hermA D n) (hermPartHom D n) continuous_hermPart hermPart_mem
    (fun s hs => hermPart_of_mem hs) (mulCE d e hde)
    (fun s hs => hermPart_anti hd hs) (fun s hs => hermPart_anti he hs)
    (fun x => hermPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_herm a) (lr_herm_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  exact (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)

theorem smul_herm {e : AE D} (hc : cA D e = e) (x : hermA D n) : e • x.1 ∈ hermA D n := by
  change adj (e • x.1) = e • x.1
  have h : adj x.1 = x.1 := x.2
  rw [adj_smul, h, hc]

def smulH (e : AE D) (hc : cA D e = e) : hermA D n →+ hermA D n where
  toFun x := ⟨e • x.1, smul_herm hc x⟩
  map_zero' := Subtype.ext (smul_zero e)
  map_add' x y := Subtype.ext (smul_add e x.1 y.1)

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_smulH (e : AE D) (hc : cA D e = e) : Continuous (smulH (n := n) e hc) :=
  ((continuous_const_smul e).comp continuous_subtype_val).subtype_mk _

theorem smul_sandwich (e : AE D) (A B x : Mx D n n) (h : e • x = x) : e • (A * x * B) = A * x * B := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]

theorem mul_fix {e : AE D} (g : GL (Fin n) (AE D)) (hg : e • (g.1 - 1) = g.1 - 1) (x : Mx D n n) (hx : e • x = 0) :
    g.1 * x = x := by
  have h : (g.1 - 1) * x = 0 := by
    rw [← hg, Matrix.smul_mul, ← Matrix.mul_smul, hx, Matrix.mul_zero]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  exact h

theorem sandwich_fix {e : AE D} (g : GL (Fin n) (AE D)) (hg : e • (g.1 - 1) = g.1 - 1) (x : hermA D n)
    (hx : e • x.1 = 0) : g.1 * x.1 * adj g.1 = x.1 := by
  have h1 := mul_fix g hg x.1 hx
  have h2 : adj x.1 = x.1 := x.2
  have h3 : x.1 * adj g.1 = x.1 := by
    have := congrArg adj h1
    rwa [adj_mul, h2] at this
  rw [h1, h3]

end Main

end GlobalTheory.CompanionTheory.HermSc
