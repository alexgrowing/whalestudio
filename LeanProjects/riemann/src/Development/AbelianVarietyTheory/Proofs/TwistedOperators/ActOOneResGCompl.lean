import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt resG_compl suppAt_resG isDetAt_detAt resG_one resG_mul actO_actO isHalf_actO)

noncomputable section

namespace GlobalTheory.TopLevelInv

abbrev conjPt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (j : ℕ) (k : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))) :=
  (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem detAt_resG_eq {D : D7} {V : HSp D} {e : AE D} {ε : AF D.host.F} (he2 : e * e = e) (hc : e * cA D e = 0)
    (hε : IsIdempotentElem ε) (halg : algebraMap (AF D.host.F) (AE D) ε = e + cA D e) (g : GA D V) :
    detAt e V (resG V ε g) = detAt e V g := by
  apply Units.ext
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG V hε, halg]
  congr 1
  set I : Ideal (AE D) := Ideal.span {1 - e}
  have h1 : Ideal.Quotient.mk I e = 1 := by
    rw [← (Ideal.Quotient.mk I).map_one, Ideal.Quotient.eq]
    have : e - 1 = (-1) * (1 - e) := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have h2 : Ideal.Quotient.mk I (cA D e) = 0 := by
    calc Ideal.Quotient.mk I (cA D e) = Ideal.Quotient.mk I (cA D e) * Ideal.Quotient.mk I e := by rw [h1, mul_one]
      _ = Ideal.Quotient.mk I (cA D e * e) := (map_mul _ _ _).symm
      _ = 0 := by rw [mul_comm, hc, map_zero]
  have key : (Formalism.IndefR.Fin.LevelGroupLemmas.resM (e + cA D e) (mt V g)).map (Ideal.Quotient.mk I) =
      (mt V g).map (Ideal.Quotient.mk I) := by
    ext i j
    simp only [Matrix.map_apply, Formalism.IndefR.Fin.LevelGroupLemmas.resM, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, h1, h2]
    ring
  have hd : Ideal.Quotient.mk I (Formalism.IndefR.Fin.LevelGroupLemmas.resM (e + cA D e) (mt V g)).det = Ideal.Quotient.mk I (mt V g).det := by
    rw [RingHom.map_det, RingHom.map_det]
    exact congrArg Matrix.det key
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hd
  obtain ⟨r, hr⟩ := hd
  linear_combination (-e) * hr + (-r) * he2

theorem detAt_one' {D : D7} {e : AE D} (he2 : e * e = e) (V : HSp D) : detAt e V 1 = 1 := by
  apply Units.ext
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Formalism.IndefR.Fin.LevelGroupLemmas.mt_one', Matrix.det_one, Units.val_one]
  ring

theorem resG_inv_eq {D : D7} {V : HSp D} {ε : AF D.host.F} (hε : IsIdempotentElem ε) (g : GA D V) :
    (resG V ε g)⁻¹ = resG V ε g⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← resG_mul V hε, mul_inv_cancel, resG_one V hε]

theorem actO_one_resG_compl {D : D7} {S T : HSp D} {e : AE D} (he2 : e * e = e) (hc : e * cA D e = 0) {ε : AF D.host.F}
    (hε : IsIdempotentElem ε) (halg : algebraMap (AF D.host.F) (AE D) ε = e + cA D e) (h : GA D T) (x : WO S T)
    (hx : IsHalf e x) : actO S T 1 (resG T (1 - ε) h) x = x := by
  have hann : ∀ i j, algebraMap (AF D.host.F) (AE D) (1 - ε) * x i j = 0 := by
    intro i j
    rw [map_sub, map_one, halg, ← hx i j]
    linear_combination (-(x i j)) * he2 + (-(x i j)) * hc
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.actO_eq, inv_one, Formalism.IndefR.Fin.LevelGroupLemmas.mt_one', Matrix.mul_one,
    Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG T hε.one_sub]
  unfold Formalism.IndefR.Fin.LevelGroupLemmas.resM
  rw [Matrix.add_mul, Matrix.one_mul, add_eq_left]
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [mul_assoc, mul_left_comm, hann l j, mul_zero]

theorem isSBHalf_halfInd {D : D7} {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf e Λ (halfInd e Λ) := by
  refine ⟨fun x hx => ?_, 1, one_pos, fun u hu hu' x => ?_, fun x hx => ?_⟩
  · by_contra h; exact hx (if_neg fun h' => h h'.2)
  · rw [one_smul]
    have h1 : IsHalf e (x + u) ↔ IsHalf e x := forall₂_congr fun i j => by
      rw [Matrix.add_apply, mul_add, hu' i j, add_left_inj]
    exact halfInd_congr (and_congr (AddSubgroup.add_mem_cancel_right _ hu) h1)
  · rw [one_smul]; by_contra h; exact hx (if_neg fun h' => h h'.1)

end GlobalTheory.TopLevelInv

end
