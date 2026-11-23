import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeEquivCrdOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.LevExt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gridCharacter_eq_reference_at_base_tuple {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {t : T} (h : L.Is t) (j : ℕ) : L.mu t j = L.mu0 j := by
  have hx := h.xi t
  rw [h.xi_base] at hx
  have e : L.xi t = 1 := MonoidHom.ext (GlobalTheory.ChrEqUnique.eq_one_of_chrEq hx)
  show L.mu0 j * L.xi t = L.mu0 j
  rw [e, mul_one]

theorem Q_eq_empty {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {t : T} (h : L.Is t) : L.Q t = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h1 := (h.Q_ram t PP).2 (Or.inl hPP)
  rw [h.xi_base] at h1
  exact h1 fun _ _ => rfl

theorem isRes_unique' {D : D7} {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

section Gen

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}

theorem idc_heq (hP : B'.toPre = B.toPre) {c : (AE a.D)ˣ →* Circle} {c' : (AE a'.D)ˣ →* Circle}
    {χ : Formalism.L2.Host.HChar a.D.host.E} {χ' : Formalism.L2.Host.HChar a'.D.host.E} (hχ : HEq χ' χ) (h : ChrEq c χ)
    (h' : ChrEq c' χ') : HEq c' c := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (χ')) ((by with_unfolding_all exact ((χ) :))) (χ') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (χ')) (χ') (((χ))) (((hχ)))).symm : _))
  clear (hχ)
  subst e))
  have e : @Eq ((AE a.D)ˣ →* Circle) ((by with_unfolding_all exact (c' :))) c := GlobalTheory.ChrEqUnique.idc_unique a.D _ c χ ((by with_unfolding_all exact (h' :))) h
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

theorem res_heq (hP : B'.toPre = B.toPre) {χ : Formalism.L2.Host.HChar a.D.host.E} {χ' : Formalism.L2.Host.HChar a'.D.host.E} (hχ : HEq χ' χ)
    {PP : Pl a.D.host.E} {PP' : Pl a'.D.host.E} (hPP : HEq PP' PP) {c : (kP PP)ˣ →* ℂˣ} {c' : (kP PP')ˣ →* ℂˣ}
    (h : IsRes χ PP c⁻¹) (h' : IsRes χ' PP' c'⁻¹) : HEq c' c := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (χ')) ((by with_unfolding_all exact ((χ) :))) (χ') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (χ')) (χ') (((χ))) (((hχ)))).symm : _))
  clear (hχ)
  subst e))
  ( (
  have e : @Eq (type_of% (PP')) ((by with_unfolding_all exact ((PP) :))) (PP') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (PP')) (PP') (((PP))) (((hPP)))).symm : _))
  clear (hPP)
  subst e))
  have e : ((by with_unfolding_all exact (c' :)) : (kP PP)ˣ →* ℂˣ)⁻¹ = c⁻¹ := isRes_unique' (D := a.D) ((by with_unfolding_all exact (h' :))) h
  have e' : @Eq ((kP PP)ˣ →* ℂˣ) ((by with_unfolding_all exact (c' :))) c := inv_inj.1 e
  exact (by with_unfolding_all exact ((heq_of_eq e') :))

theorem hermitianCodeCharFrame_referenceCharacter_heq (hP : B'.toPre = B.toPre) {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) {i : Fin a.D.R.m}
    {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') : HEq ((Top.Fr.at a'.st f').mu0 i') ((Top.Fr.at a.st f).mu0 i) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  have e : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i' := (by with_unfolding_all exact ((Fin.ext h : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i') :))
  clear h
  subst e
  exact (by with_unfolding_all exact ((HEq.refl ((Top.Fr.at a.st f).mu0 i)) :))

theorem frat_eta_heq (hP : B'.toPre = B.toPre) {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) :
    HEq (Top.Fr.at a'.st f').eta (Top.Fr.at a.st f).eta := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl (Top.Fr.at a.st f).eta) :))

theorem mem_vGs (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px)
    {PP : Pl a.D.host.E} {PP' : Pl a'.D.host.E} (hPP : HEq PP' PP) (h : PP ∈ (B.primes px).vGs) : PP' ∈ (B'.primes px').vGs := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  ( (
  have e : @Eq (type_of% (PP')) ((by with_unfolding_all exact ((PP) :))) (PP') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (PP')) (PP') (((PP))) (((hPP)))).symm : _))
  clear (hPP)
  subst e))
  exact (by with_unfolding_all exact (h :))

end Gen

end GlobalTheory.Mem.R3.Rw.LevExt

open GlobalTheory.Mem.R3.Rw.LevExt in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh → LevSame z Wt' R' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hpx hL'
  have hP : B'.toPre = B.toPre := hE.1
  have hC : z.R.toLevCh.C = Top.Fr.at (w.st Z) f := z.lev.C.trans (by rw [w.C_eq])
  have hC' : R'.toLevCh.C = Top.Fr.at (w'.st Z') f' := hL'.C.trans (by rw [w'.C_eq])
  have hmu0 : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
      HEq (R'.toLevCh.C.mu0 i') (z.R.toLevCh.C.mu0 i) := by
    intro i i' h
    rw [hC, hC']
    exact hermitianCodeCharFrame_referenceCharacter_heq (a := Z) (a' := Z') hP hf h
  have heta : HEq R'.toLevCh.C.eta z.R.toLevCh.C.eta := by
    rw [hC, hC']
    exact frat_eta_heq (a := Z) (a' := Z') hP hf
  have hs := z.lev.is
  have hs' := hL'.is
  refine ⟨fun i i' h => ⟨?_, fun PP' PP hPP hm => ?_⟩, ?_, Q_eq_empty hs', Q_eq_empty hs⟩
  · rw [gridCharacter_eq_reference_at_base_tuple hs', gridCharacter_eq_reference_at_base_tuple hs]
    exact idc_heq (a := Z) (a' := Z') hP (hmu0 i i' h) (hs.mu0 i) (hs'.mu0 i')
  · have hm0 : PP ∈ (B.primes w.px).vGs := by
      have e := z.lev.Pg
      rw [← e]
      exact hm
    have hm' : PP' ∈ R'.toLevCh.Pg := by
      rw [hL'.Pg]
      exact mem_vGs (a := Z) (a' := Z') hP hpx hPP hm0
    exact res_heq (a := Z) (a' := Z') hP (hmu0 i i' h) hPP (hs.chi i PP hm) (hs'.chi i' PP' hm')
  · exact idc_heq (a := Z) (a' := Z') hP heta hs.eta hs'.eta
