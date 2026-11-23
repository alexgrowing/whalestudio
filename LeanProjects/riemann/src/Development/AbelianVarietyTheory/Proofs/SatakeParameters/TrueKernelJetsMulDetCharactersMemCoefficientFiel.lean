import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmoothStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntAtOfLocTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkThind
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.LvT.Built.KMap

theorem rho_jet_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ColIn.JetsIn I → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ), (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) → ∃ k : B.LL, B.embLL k = (I.rho u a i c.1 ((I.stp u a i).rep c) * I.rho' u a i c'.1 ((I.stp u a (i + 1)).rep c')) * jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) e := by
  classical
  intro B X I h hP l Z hJ u a i hi c c' e he
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := GlobalTheory.T.trueColumn_periodLattice_vacuumSmooth I h hP l Z a u i hi
  set p := (I.stp u a i).rep c
  set p' := (I.stp u a (i + 1)).rep c'
  have hN : IsSdLat p.1.1.deco.1.N := ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩
  have hN' : IsSdLat p'.1.1.deco.1.N := ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) :=
    pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB : 0 < cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u := GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) _ _ u i hX hPr
    h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) hi ⟨_, _, _, _, h.ch_tied⟩ c.1 c'.1 p p'
  set N := p.1.1.deco.1.N
  set N' := p'.1.1.deco.1.N
  set cA := cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a)
  set cB := cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u
  set Ξ := xiAt (Pr := B.primes X) I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 p p'
  have hth := GlobalTheory.latSum_thInd_eq_thC B.fields I.A _ _ (I.Sb a u) N N' cA cB (fun x => I.A.σ₀ (Ξ x))
    (indTieD_of_la I.A _ _ _ _ (Nat.mul_pos hA hB) hLa) hN hN' hA hB (volC_pos_of_laHyp I.A _ _ _ hLa hN hN')
    (GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ _ _ _ _ _ hN.1 hN'.1 hA hB) (fun x hx => hbox.1 x ((map_ne_zero _).1 hx))
    (fun x y hy => congrArg I.A.σ₀ (hbox.2 x y hy))
  have hfin := GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ (I.Sb a u) N N' cA cB hN.1 hN'.1 hA hB
  let _ := @Fintype.ofFinite _ hfin
  rw [show I.th u a i c.1 c'.1 p p' = fun z => _ from funext fun z => (hth z).symm]
  unfold latSum
  simp only [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((Formalism.L2.Col.mulLat cB (homAt (I.Sb a u) N N')).comap (divLat cA (homAt (I.Sb a u) N N')).subtype))
  have hs : ∀ q (k : ℕ), ContDiff ℂ k (I.A.thInd (I.Sb a u) N N' cB (r q)) := fun q =>
    indSmooth_of I.A _ _ (I.Sb a u) (cA * cB) hE N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩
  rw [show I.J.cD = I.A.cD from rfl, jetC_sum _ _ _ hs]
  have hr := rhoIs I h a u hi c.1 p c'.1 p'
  rw [show I.rho u a i c.1 p * I.rho' u a i c'.1 p' = _ from hr]
  have hσ : (ColIn.A I).σ₀ = B.embLL := rfl
  rw [hσ]
  apply RingHom.mem_fieldRange.1
  rw [mul_assoc, Finset.mul_sum]
  refine Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) (Subfield.sum_mem _ fun q _ => ?_)
  obtain ⟨y, hy⟩ := hJ.exists_eq (a := a) (u := u) (N := N) (N' := N') (c := cB) (x := (r q).1) (e := e) hi
    ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩ he
  rw [mul_left_comm]
  refine Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) ?_
  exact ⟨y, hy⟩

end GlobalTheory.Mem.Col2.TC
