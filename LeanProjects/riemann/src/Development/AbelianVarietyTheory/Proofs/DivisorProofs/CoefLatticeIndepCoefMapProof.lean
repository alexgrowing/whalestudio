import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemHatSwap

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.CoefIndepProof

theorem coefIndep : GlobalTheory.BaseCmp.CoefIndep := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i c0L hc h w hw
  obtain ⟨gramR', c0R', c0L', hT', P, hP, rfl⟩ := hw
  obtain ⟨gramR, c0R, hT⟩ := hc
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := (R.B.L i A.μ0).pres.reps (fin (Vc D i) h)
  have hst : Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D i)) : GL (Fin (Vc D i).rank) _) ∈ St (R.βV i) :=
    Formalism.L2.DIV.parLev_St k.2.1
  obtain ⟨γE, hγ, hl⟩ := GlobalTheory.HLatMove.hLat_rat_mul_stab (Vc D i) (R.βV i) (R.ΛV i) (hR.lev.βV i) γ
  rw [e, hl _ _ hst, Formalism.L2.Col.nabAtr_gmap, MulEquiv.apply_symm_apply] at hP ⊢
  obtain ⟨P', hP', rfl⟩ := hP
  obtain ⟨e', -, h2', -, h4', -⟩ := hT'.coefL i A.μ0
  obtain ⟨e1, -, h2, -, h4, -⟩ := hT.coefL i A.μ0
  rw [← h4' c] at hP'
  obtain ⟨y, hy, rfl⟩ := hP'
  refine ⟨rhoVr (labLL D) (lamV D i) γE (e1 y), ⟨e1 y, ?_, rfl⟩, ?_⟩
  · rw [← h4 c]; exact ⟨y, hy, rfl⟩
  · have a1 := (hT'.mapL i).1 γ γE hγ (e' y)
    have a2 := (hT.mapL i).1 γ γE hγ (e1 y)
    change c0L' i (rhoVr (labLL D) (lamV D i) γE (e' y)) = c0L i (rhoVr (labLL D) (lamV D i) γE (e1 y))
    rw [a1, ← h2', h2]
    exact a2.symm

end GlobalTheory.CoefIndepProof
