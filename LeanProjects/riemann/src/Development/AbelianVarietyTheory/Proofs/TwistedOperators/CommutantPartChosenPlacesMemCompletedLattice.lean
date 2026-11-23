import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AnnPart

theorem idemSum_mul_conj {D : D7} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e₀ a : AE D} (he₀ : IsIdemSum e₀ P)
    {Q : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∈ P) (ha : Formalism.L2.NTheta.IsIdemAt a Q) : e₀ * cA D a = 0 := by
  obtain ⟨q0, q1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₀
  obtain ⟨-, d2⟩ := GlobalTheory.StdFrames.cpt_of_isIdemAt ha
  have k : e₀ * a = a := by
    refine GlobalTheory.DepthFix.ext_cpt ?_ fun R => ?_
    · rw [RingHom.map_mul, q0, zero_mul, GlobalTheory.SplitScalar.infPart_splitIdem ha.1]
    · rw [RingHom.map_mul, RingHom.map_mul]
      by_cases hR : R = Q
      · rw [hR, q1 _ hQ, one_mul]
      · rw [d2 R hR, mul_zero]
  rw [← k, RingHom.map_mul, ← mul_assoc, he₀.2, zero_mul]

theorem part_mem_latO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ w ∈ Ann ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → e • w ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True := by
  intro D T L sc μ₀ hL G ψ hψ i hi e he w hw hinf
  obtain ⟨hS, hT⟩ := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  obtain ⟨-, hw2⟩ := hw
  have hmx : MxAt (fun _ => True) (e • w) := fun a b => by
    refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun v => (v.2 trivial).elim⟩
    have h0 : infPart D (w a b) = 0 := by simpa using congrFun (congrFun hinf a) b
    rw [RingHom.mem_ker, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, h0, mul_zero]
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ _ _ _ _ hS hT (fun _ => True) (e • w) hmx).2 fun u hu => ?_
  rw [GlobalTheory.SplitScalar.symplO_smul]
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [map_sum, Finset.sum_smul, ← GlobalTheory.LatVac.symplHom_apply, map_sum]
  refine Finset.sum_induction _ (fun z => ψ z = 1) (fun a b ha hb => by rw [AddChar.map_add_eq_mul, ha, hb, mul_one])
    (AddChar.map_zero_eq_one ψ) fun PP hPP => ?_
  rw [GlobalTheory.LatVac.symplHom_apply]
  have hsp := GlobalTheory.SplitScalar.isSplitIdem_conj (hes PP hPP).1
  have hmem : cA D (es PP) • u ∈ depLat G (.chi i 0) := by
    show _ ∧ _
    refine ⟨GlobalTheory.CosetRow.smul_mem_latO_idem _ _ hsp.1 hu, fun e₀ he₀ => ?_⟩
    rw [smul_smul, idemSum_mul_conj he₀ hPP (hes PP hPP), zero_smul]
    exact zero_mem _
  refine hw2 _ hsp _ hmem ?_
  rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, hsp.1]

end GlobalTheory.AnnPart
